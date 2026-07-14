#!/usr/bin/env python3
"""SALT — Suppose, Attempt, Learn, Triage.

Oriented random supposition: when the direct attack stalls, flood the goal with
*suppositions* (candidate `have` statements) drawn from goal-aware templates and
mutated corpus lemmas, then let the kernel triage every one of them.

The point is not the guessing — it is the TRIAGE. Each supposition H is checked
against two independent questions, cheaply, in batch:

    provable?  can H be proven from the current context by a cheap portfolio?
    useful?    if H were TRUE (assume it via sorry), does the goal close?

which sorts every guess into one of four boxes:

    provable + useful    -> KEY      the proof. insert H, done.
    ¬provable + useful   -> BRIDGE   the goal reduces to H. recurse on H.
    provable + ¬useful   -> TRUE     a fact, but not this fact. discard.
    ¬provable + ¬useful  -> NOISE    discard.

BRIDGEs are the real prize: they are the machine telling you which lemma to
prove next. That is a strictly smaller problem than the one you had.

THE EX FALSO TRAP (found the hard way, first run of this tool): a supposition
that CONTRADICTS the context closes the goal — any goal — by ex falso, so it
scores as maximally "useful" while being worthless. On the smoke test
`3 ∣ n ⊢ 9 ∣ n^2`, salt's top two "bridges" were `Nat.Coprime (n^2) n` (forces
n = 1, contradicting 3 ∣ n) and a false arithmetic identity. Both were pure
poison. So every supposition that looks useful must first survive a
consistency check: if `H` plus the context proves `False`, it is POISON and
never reported. Usefulness without consistency is not evidence — it is the
absence of evidence.

"Oriented" = candidates are built from the goal's OWN atoms and from `have`
statements mined out of the solved corpus. "Random" = a seed shuffles which
templates meet which atoms, so a second run with a new seed explores elsewhere.
Ill-typed junk costs nothing: the elaborator rejects it for free. Propose
freely; the kernel disposes.

Usage:
  salt.py shake FILE [--n 60] [--seed 7] [--depth 1]
  salt.py shake FILE --show-goal      # just print the goal state and atoms

FILE: a .lean file holding ONE theorem whose body is `sorry` (or partial, with
      the hole marked `sorry`). Needs the REPL daemon (tools/repl.py start).
"""

import argparse
import json
import os
import random
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(HERE)
CORPUS = [os.path.join(REPO, "bench", "solved_putnam"),
          os.path.join(REPO, "bench", "solved_imo")]

sys.path.insert(0, HERE)
import repl as R  # noqa: E402  (daemon client)


# ------------------------------------------------------------------ REPL glue
def ask(src, timeout=300):
    return R.ask({"cmd": src}, timeout=timeout)


def goal_of(header):
    """Elaborate `header := by sorry` and return the pretty-printed goal."""
    resp = ask(header + " := by sorry")
    errs = [m for m in resp.get("messages", []) if m["severity"] == "error"]
    if errs:
        sys.exit("statement does not elaborate:\n" +
                 "\n".join(m["data"] for m in errs))
    if not resp.get("sorries"):
        sys.exit("no sorry found — is the theorem already proved?")
    return resp["sorries"][0]["goal"]


# --------------------------------------------------------------- goal parsing
TYPE_KINDS = {
    "ℕ": "nat", "ℤ": "int", "ℚ": "rat", "ℝ": "real", "ℂ": "complex",
    "Prop": "prop",
}


def parse_goal(goal):
    """Split a Lean goal state into (hyps, atoms, target).

    atoms: {name: kind} for the plain scalar variables we can build on.
    """
    lines = goal.split("\n")
    tgt_i = next(i for i, l in enumerate(lines) if l.lstrip().startswith("⊢"))
    hyps = lines[:tgt_i]
    target = " ".join(l.strip() for l in lines[tgt_i:])[1:].strip()

    atoms, hyp_names = {}, []
    for l in hyps:
        if " : " not in l:
            continue
        names, ty = l.split(" : ", 1)
        ty = ty.strip()
        for nm in names.split():
            nm = nm.strip("✝")
            if not nm or not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", nm):
                continue
            if ty in TYPE_KINDS:
                atoms[nm] = TYPE_KINDS[ty]
            elif ty.startswith(("ℕ →", "ℤ →", "ℝ →", "Fin", "Set", "Finset")):
                atoms[nm] = "fun"
            else:
                hyp_names.append(nm)   # a proof of something
    return hyps, atoms, target, hyp_names


def subterms(target):
    """Cheap sub-expression harvest from the target: parenthesised groups,
    applications, and numerals. Ill-typed picks are filtered by the kernel."""
    out = set()
    for m in re.finditer(r"\(([^()]{1,40})\)", target):
        s = m.group(1).strip()
        if s and not s.startswith(("fun", "λ")):
            out.add(s)
    for m in re.finditer(r"\b(\d+)\b", target):
        out.add(m.group(1))
    for m in re.finditer(r"\b([a-zA-Z_][\w']*\s*[\^*+\-/]\s*[\w'\d]+)", target):
        out.add(m.group(1).strip())
    return sorted(out)


# ------------------------------------------------- supposition template banks
NUMERIC = ("nat", "int", "rat", "real")

# templates keyed by how many ingredients they eat
T1 = [
    "0 < {a}", "0 ≤ {a}", "{a} ≠ 0", "1 ≤ {a}", "2 ≤ {a}",
    "{a} = 0 ∨ 0 < {a}", "Even {a} ∨ Odd {a}", "{a} ≤ 1 ∨ 1 < {a}",
]
T1_NAT = [
    "0 < {a}", "{a} ≠ 0", "1 ≤ {a}", "2 ≤ {a}",
    "{a} = 0 ∨ 0 < {a}", "Even {a} ∨ Odd {a}",
    "∃ k, {a} = 2 * k ∨ {a} = 2 * k + 1",
]
T1_REAL = [
    "0 < {a}", "0 ≤ {a}", "{a} ≠ 0", "0 ≤ {a} ^ 2", "{a} < 0 ∨ 0 ≤ {a}",
    "|{a}| = {a} ∨ |{a}| = -{a}",
]
T2 = [
    "{a} ≤ {b}", "{a} < {b}", "{a} = {b}", "{a} ≠ {b}",
    "{a} ≤ {b} ∨ {b} ≤ {a}", "0 ≤ ({a} - {b}) ^ 2",
    "({a} - {b}) * ({a} + {b}) = {a} ^ 2 - {b} ^ 2",
]
T2_NAT = [
    "{a} ∣ {b}", "Nat.Coprime {a} {b}", "{a} ≤ {b} ∨ {b} ≤ {a}",
    "{a} % {b} = 0 ∨ 0 < {a} % {b}", "{a} = {b} ∨ {a} < {b} ∨ {b} < {a}",
    "∃ q r, {a} = {b} * q + r",
]
# suppositions built against the target itself
T_TARGET = [
    "{t} ∨ ¬ {t}",
]


def definitional(hyps, target):
    """Suppositions that UNFOLD what the context already says — the witness
    forms. `3 ∣ n` is inert until it becomes `∃ k, n = 3 * k`; that single
    move is what most stuck proofs are actually waiting for."""
    out = []
    facts = [h.split(" : ", 1)[1].strip() for h in hyps if " : " in h]
    for s in facts + [target]:
        m = re.fullmatch(r"(.+?)\s*∣\s*(.+)", s)
        if m:
            a, b = m.group(1).strip(), m.group(2).strip()
            out += [f"∃ k, {b} = {a} * k", f"∃ k, {b} = k * {a}"]
        m = re.fullmatch(r"Even\s+(.+)", s)
        if m:
            out.append(f"∃ k, {m.group(1).strip()} = 2 * k")
        m = re.fullmatch(r"Odd\s+(.+)", s)
        if m:
            out.append(f"∃ k, {m.group(1).strip()} = 2 * k + 1")
        m = re.fullmatch(r"(.+?)\s*≡\s*(.+?)\s*\[MOD\s*(.+?)\]", s)
        if m:
            a, b, n = (g.strip() for g in m.groups())
            out.append(f"∃ k, {a} = {b} + {n} * k")
        m = re.fullmatch(r"(.+?)\s*<\s*(.+)", s)
        if m:
            a, b = m.group(1).strip(), m.group(2).strip()
            out.append(f"∃ k, {b} = {a} + k + 1")
    return out


def gen_candidates(atoms, target, terms, corpus_haves, n, rng, hyps=()):
    """Build a salted, oriented candidate pool."""
    nums = [a for a, k in atoms.items() if k in NUMERIC]
    nats = [a for a, k in atoms.items() if k in ("nat", "int")]
    reals = [a for a, k in atoms.items() if k in ("real", "rat")]
    # ingredients: bare variables AND harvested subterms (parenthesised)
    ing = list(nums) + ["(" + t + ")" for t in terms if len(t) < 30]
    ing_nat = list(nats) + ["(" + t + ")" for t in terms if len(t) < 20]

    pool = set()

    def add(tpl, **kw):
        try:
            pool.add(tpl.format(**kw))
        except (KeyError, IndexError):
            pass

    for a in ing:
        for tpl in T1:
            add(tpl, a=a)
    for a in nats:
        for tpl in T1_NAT:
            add(tpl, a=a)
    for a in reals:
        for tpl in T1_REAL:
            add(tpl, a=a)
    for a in ing:
        for b in ing:
            if a != b:
                for tpl in T2:
                    add(tpl, a=a, b=b)
    for a in ing_nat:
        for b in ing_nat:
            if a != b:
                for tpl in T2_NAT:
                    add(tpl, a=a, b=b)
    for tpl in T_TARGET:
        add(tpl, t=target)

    # --- corpus mutation: real `have` types from solved proofs, resalted ---
    for h in corpus_haves:
        ids = sorted(set(re.findall(r"\b[a-z][\w']{0,2}\b", h)) -
                     {"of", "le", "lt", "eq", "ne", "in", "by"})
        if not ids or not ing:
            continue
        sub = {i: rng.choice(ing) for i in ids}
        mut = re.sub(r"\b[a-z][\w']{0,2}\b",
                     lambda m: sub.get(m.group(0), m.group(0)), h)
        if 3 < len(mut) < 90:
            pool.add(mut)

    cands = sorted(pool)
    rng.shuffle(cands)
    # definitional unfoldings are never crowded out by salt — they lead
    forced = definitional(list(hyps), target)
    rest = [c for c in cands if c not in forced]
    return (forced + rest)[:max(n, len(forced))]


def mine_corpus_haves(limit=400):
    """Harvest `have _ : TYPE := ...` statement types from solved proofs."""
    out = []
    for d in CORPUS:
        if not os.path.isdir(d):
            continue
        for fn in sorted(os.listdir(d)):
            for line in open(os.path.join(d, fn)):
                m = re.search(r"have\s+\w+\s*:\s*(.+?)\s*:=", line)
                if m:
                    t = m.group(1).strip()
                    if 3 < len(t) < 90 and "fun" not in t:
                        out.append(t)
    return out[:limit]


# ------------------------------------------------------------ batched triage
def portfolio(tactics):
    """`first | t1 | t2 | ...` picks the first tactic that SUCCEEDS — not the
    first that CLOSES the goal. `simp_all` can make progress, leave goals open,
    and shadow the branch that would have finished. Every branch therefore
    carries a `; done` guard: succeed only by finishing. (Cost me the key
    supposition on the very first smoke test; see KNOWN_TRAPS.md.)"""
    return "first " + " ".join(f"| ({t}; done)" for t in tactics)


# `exact?` searches all of mathlib — it is ~100x the cost of everything else
# here. Nested inside four obtain-branches it turned a 9 s triage into 3m23s,
# and even once per candidate it costs ~2 min. Off by default; --deep buys it.
_BASE = ["rfl", "assumption", "positivity", "norm_num", "omega", "decide",
         "simp_all", "linarith", "nlinarith", "aesop", "ring_nf",
         "simp [mul_pow, pow_mul]"]

# The closer must be able to USE a supposition, not just stare at it: an
# existential witness is inert until destructured, so `obtain` is part of
# closing, not a separate step.
_FIN = portfolio(_BASE + ["exact ⟨w, by ring⟩", "exact ⟨w ^ 2, by ring⟩",
                          "exact ⟨w ^ 3, by ring⟩", "exact ⟨w * w, by ring⟩"])
_OBTAIN = [
    f"obtain ⟨w, rfl⟩ := hsalt; {_FIN}",
    f"obtain ⟨w, hw⟩ := hsalt; subst hw; {_FIN}",
    f"obtain ⟨w, hw⟩ := hsalt; {_FIN}",
    f"rcases hsalt with h1 | h2 <;> ({_FIN})",
]
CHEAP = portfolio(_BASE)
CLOSER = portfolio(_BASE + _OBTAIN)


def set_depth(deep):
    """--deep adds `exact?` (full mathlib search) to both portfolios."""
    global CHEAP, CLOSER
    CHEAP = portfolio(_BASE + (["exact?"] if deep else []))
    CLOSER = portfolio(_BASE + _OBTAIN + (["exact?"] if deep else []))


def batch(blocks, timeout=600):
    """Run many independent `example`s in ONE kernel call; return per-block
    (errors, sorries) by line-range mapping. Blocks are anonymous examples —
    never named theorems (a named variant would enter the env and let a later
    candidate cite it: the fake-8/8 soundness trap in KNOWN_TRAPS.md)."""
    src, spans, line = [], [], 0
    for b in blocks:
        b = b.rstrip("\n")
        nl = b.count("\n") + 1
        spans.append((line + 1, line + nl))
        src.append(b)
        line += nl
    resp = ask("\n".join(src), timeout=timeout)
    if "error" in resp and "messages" not in resp:
        sys.exit(f"REPL error: {resp['error']}")
    errs = [[] for _ in blocks]
    sorries = [[] for _ in blocks]
    for m in resp.get("messages", []):
        ln = m["pos"]["line"]
        for i, (lo, hi) in enumerate(spans):
            if lo <= ln <= hi:
                if m["severity"] == "error":
                    errs[i].append(m["data"])
                break
    for s in resp.get("sorries", []):
        ln = s["pos"]["line"]
        for i, (lo, hi) in enumerate(spans):
            if lo <= ln <= hi:
                sorries[i].append(s)
                break
    return errs, sorries


def example_header(header):
    """theorem foo (a : X) ... : G   ->   example (a : X) ... : G"""
    h = header.strip()
    h = re.sub(r"^(theorem|lemma)\s+\S+", "example", h, count=1)
    return h


def shake(path, n, seed, verbose=True):
    rng = random.Random(seed)
    text = open(path).read()
    text = "\n".join(l for l in text.splitlines()
                     if not l.strip().startswith("import "))
    if ":= by" not in text:
        sys.exit("expected a theorem whose body is `:= by sorry`")
    header = text.split(":= by")[0].strip()
    ex_header = example_header(header)

    goal = goal_of(header)
    hyps, atoms, target, hyp_names = parse_goal(goal)
    terms = subterms(target)

    print("=" * 70)
    print("GOAL")
    print(goal)
    print("-" * 70)
    print(f"atoms: {atoms}")
    print(f"harvested subterms: {terms[:12]}")
    print("=" * 70)
    if n == 0:
        return

    cands = gen_candidates(atoms, target, terms, mine_corpus_haves(), n, rng, hyps)
    print(f"salted {len(cands)} suppositions (seed {seed}); triaging...\n")

    # --- pass 1: well-typed? (term-mode sorry: no tactic can mask a type error)
    errs, _ = batch([_mk_typecheck(ex_header, c) for c in cands])
    typed = [c for c, e in zip(cands, errs) if not e]
    print(f"pass 1  well-typed : {len(typed)}/{len(cands)}")
    if not typed:
        return

    # --- pass 2: provable from context, cheaply?
    errs, _ = batch([_mk_provable(ex_header, c) for c in typed])
    provable = {c: not e for c, e in zip(typed, errs)}
    print(f"pass 2  provable   : {sum(provable.values())}/{len(typed)}")

    # --- pass 3: POISON — does H contradict the context? (the ex falso trap)
    # A contradictory H closes every goal. Catch it before believing anything.
    errs, _ = batch([_mk_poison(ex_header, c) for c in typed])
    poison = {c: not e for c, e in zip(typed, errs)}   # proved False => poison
    print(f"pass 3  POISON     : {sum(poison.values())}/{len(typed)} "
          f"(contradict the context; would close the goal by ex falso)")

    # --- pass 4: useful — assume it, does the goal close?
    errs, sor = batch([_mk_useful(ex_header, c) for c in typed])
    useful = {}
    for c, e, s in zip(typed, errs, sor):
        # useful <=> no errors anywhere AND the only sorry is our own `have`
        useful[c] = (not e) and len(s) == 1 and not poison[c]
    print(f"pass 4  useful     : {sum(useful.values())}/{len(typed)}")

    # --- pass 5: circular — does the GOAL imply H? then H is the goal wearing
    # a hat (`9 ∣ n^2` unfolds to `∃ k, n^2 = 9*k`): "useful" but no progress.
    errs, _ = batch([_mk_circular(ex_header, target, c) for c in typed])
    circular = {c: not e for c, e in zip(typed, errs)}
    print(f"pass 5  circular   : {sum(circular.values())}/{len(typed)} "
          f"(goal implies H: a restatement, not a reduction)\n")

    box = {"KEY": [], "BRIDGE": [], "RESTATEMENT": [],
           "TRUE": [], "NOISE": [], "POISON": []}
    for c in typed:
        if poison[c]:
            box["POISON"].append(c)
            continue
        p, u, circ = provable[c], useful[c], circular[c]
        if p and u:
            box["KEY"].append(c)          # provable outright: a real proof
        elif u and circ:
            box["RESTATEMENT"].append(c)  # equivalent to the goal: no progress
        elif u:
            box["BRIDGE"].append(c)       # strictly stronger: real reduction
        else:
            box["TRUE" if p else "NOISE"].append(c)

    for k in ("KEY", "BRIDGE", "RESTATEMENT", "TRUE", "POISON"):
        if not box[k]:
            continue
        tag = {"KEY": "*** KEY — provable AND closes the goal: THIS IS A PROOF ***",
               "BRIDGE": "BRIDGE — closes the goal and is STRICTLY STRONGER; prove THIS next",
               "RESTATEMENT": "RESTATEMENT — equivalent to the goal (unfolding, not progress)",
               "TRUE": "TRUE — provable, but does not close the goal",
               "POISON": "POISON — contradicts the context (ex falso; NOT evidence)"}[k]
        cap = 15 if k in ("KEY", "BRIDGE") else 5
        print(tag)
        for c in box[k][:cap]:
            print(f"   have hsalt : {c}")
        if len(box[k]) > cap:
            print(f"   ... (+{len(box[k]) - cap} more)")
        print()
    print(f"NOISE discarded: {len(box['NOISE'])}")
    return box


def _mk_typecheck(ex_header, c):
    binders = ex_header.rsplit(" : ", 1)[0]        # drop the goal, keep binders
    return f"{binders} : ({c}) := sorry"


def _mk_provable(ex_header, c):
    binders = ex_header.rsplit(" : ", 1)[0]
    return f"{binders} : ({c}) := by\n  {CHEAP}"


def _mk_poison(ex_header, c):
    """Can the context PLUS H prove False? Then H is contradictory: it would
    close the goal by ex falso and teach us nothing."""
    binders = ex_header.rsplit(" : ", 1)[0]
    return f"{binders} (hsalt : ({c})) : False := by\n  {CLOSER}"


def _mk_useful(ex_header, c):
    return f"{ex_header} := by\n  have hsalt : ({c}) := sorry\n  {CLOSER}"


def _mk_circular(ex_header, target, c):
    """Does the GOAL imply H? If so H is not a reduction, just the goal in
    different clothes — it closes the goal only because it IS the goal."""
    binders = ex_header.rsplit(" : ", 1)[0]
    return f"{binders} (hgoal : ({target})) : ({c}) := by\n  {CHEAP}"


def main():
    p = argparse.ArgumentParser(description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest="op", required=True)
    s = sub.add_parser("shake")
    s.add_argument("file")
    s.add_argument("--n", type=int, default=60)
    s.add_argument("--seed", type=int, default=7)
    s.add_argument("--deep", action="store_true",
                   help="add exact? (full mathlib search) — much slower")
    s.add_argument("--show-goal", action="store_true")
    a = p.parse_args()
    if R._ping() is None:
        sys.exit("REPL daemon not running: python3 tools/repl.py start")
    set_depth(a.deep)
    shake(a.file, 0 if a.show_goal else a.n, a.seed)


if __name__ == "__main__":
    main()
