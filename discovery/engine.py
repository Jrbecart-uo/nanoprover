#!/usr/bin/env python3
"""DISCOVERY ENGINE — evolutionary program search for open constructive problems.

The architecture that has actually produced new mathematics from an LLM
(FunSearch → cap sets; AlphaEvolve → packing/overlap constants) is the one this
project already runs: THE AGENT PROPOSES, THE EVALUATOR DISPOSES. Only the
fitness function changes — a scoring program instead of the Lean kernel.

    idea (natural language, from some lens)
      → program that CONSTRUCTS an object
        → evaluator scores the object          <- the only source of truth
          → survivors breed the next round

WHY PROGRAMS AND NOT OBJECTS. A 500-element set is 500 arbitrary numbers; an LLM
cannot reason its way to it, and a hill-climber gets stuck. A *program* that
builds the set is short, readable, and carries the IDEA — so it can be mutated
by reasoning ("what if the sieve went the other way?") rather than by
coin-flips. Every result FunSearch and AlphaEvolve ever produced came out of
evolving programs, never raw objects. This is the single most important design
choice in the file.

WHAT IS DIFFERENT HERE. FunSearch fires millions of cheap LLM samples at a weak
mutation operator. We are keyless: the mutation operator is a session LLM (or
its subagents), so we get TENS of proposals, not millions. That flips the
design:

  * they buy diversity with SAMPLING VOLUME; we must buy it with LENSES —
    each proposal is asked to attack from a different intellectual tradition
    (physics, chemistry, biology, probability, algebra, algorithm design).
    A lens is a diversity mechanism, not decoration.
  * they can afford to throw away 99.9% of samples; every one of ours must be
    a serious attempt, so the prompt carries the full state of the art: the
    best programs so far, what has already FAILED, and why.
  * their islands prevent premature convergence over many generations; ours
    keep a handful of genuinely distinct IDEAS alive at once.

The evaluator is the referee and it never flatters us: a construction either
achieves the bound or it does not, and `verify` re-checks the winner from
scratch with an independent, deliberately naive routine (see problems/*.py).
A claimed record that only the fast scorer believes is not a record.

Usage:
  engine.py init      PROBLEM              start a run
  engine.py prompt    PROBLEM [--lens L]   emit the proposal prompt (for the LLM)
  engine.py ingest    PROBLEM FILE --lens L --note "the idea in one line"
  engine.py status    PROBLEM              population, best score, history
  engine.py verify    PROBLEM              re-check the champion, independently
"""

import argparse
import importlib.util
import json
import math
import os
import random
import subprocess
import sys
import textwrap
import time

HERE = os.path.dirname(os.path.abspath(__file__))
PROBLEMS = os.path.join(HERE, "problems")
RUNS = os.path.join(HERE, "runs")

# The lenses. Each is a different tradition of thought about structure; the
# point is that they FAIL DIFFERENTLY, so their errors do not correlate.
LENSES = {
    "physics":
        "Think like a physicist. Energy landscapes, symmetry and symmetry "
        "BREAKING, conservation laws, phase transitions, annealing, "
        "renormalisation (does the problem look the same at another scale?), "
        "frustration in disordered systems (spin glasses). Is the object you "
        "want a GROUND STATE of some energy you can write down?",
    "chemistry":
        "Think like a chemist. Local valence rules producing global structure; "
        "packing and steric exclusion; crystals versus glasses; self-assembly "
        "from simple local affinities; catalysis (an element that enables "
        "structure without appearing in it). What are the LOCAL bonding rules "
        "whose only consistent global completion is the object you want?",
    "biology":
        "Think like a biologist. Growth and accretion rules; developmental "
        "recursion (an organism built by repeatedly applying a small rule); "
        "modularity and reuse; symbiosis; evolutionary ratchets; niches. Can "
        "the object be GROWN by a local rule rather than designed globally?",
    "probability":
        "Think like a probabilist. The probabilistic method: take a random "
        "object and show the bad events are rare; then ALTERATION — delete the "
        "few offenders. Concentration of measure. Entropy/counting arguments. "
        "Lovász Local Lemma. Random greedy processes. What does a RANDOM "
        "construction give, and how much can you repair it?",
    "algebra":
        "Think like an algebraist. Impose structure so the constraints become "
        "automatic: finite fields, groups, characters, polynomials, lattices, "
        "cyclotomy, quadratic residues, difference sets, error-correcting "
        "codes. Algebraic constructions are how most extremal RECORDS are "
        "actually held. What algebraic object has exactly the property needed?",
    "algorithmic":
        "Think like an algorithm designer. State of the art search: simulated "
        "annealing with a good move set, tabu search, SAT/ILP encodings, "
        "beam search, dynamic programming over a clever state, branch and "
        "bound with strong pruning, local search from a structured seed. Do "
        "not just brute force — find the SEARCH SPACE in which the answer is "
        "shallow.",
    "geometry":
        "Think like a geometer. Draw it. Convexity, projections, tilings, "
        "scaling and self-similarity, fractals, dimension, embeddings into a "
        "space where the constraint becomes a distance. What does the object "
        "LOOK like, and what does that picture suggest?",
    "adversarial":
        "Think like the problem's defence lawyer. WHY has nobody beaten this "
        "bound? What is the obstruction, and is it real or merely habitual? "
        "Which assumption is everyone making without stating it? Attack THAT.",
}


# ------------------------------------------------------------------ problem
def load_problem(name):
    path = os.path.join(PROBLEMS, name + ".py")
    if not os.path.exists(path):
        sys.exit(f"no such problem: {path}")
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    for attr in ("STATEMENT", "TARGET", "RECORD", "evaluate", "verify", "SEED"):
        if not hasattr(mod, attr):
            sys.exit(f"problem {name} is missing `{attr}`")
    return mod


def run_dir(name):
    d = os.path.join(RUNS, name)
    os.makedirs(d, exist_ok=True)
    return d


def db_path(name):
    return os.path.join(run_dir(name), "population.json")


def load_db(name):
    p = db_path(name)
    if not os.path.exists(p):
        return {"programs": [], "history": []}
    return json.load(open(p))


def save_db(name, db):
    json.dump(db, open(db_path(name), "w"), indent=1)


# ---------------------------------------------------------------- evaluate
def score_program(problem, src, timeout=120):
    """Run a candidate program in a subprocess and score what it builds.

    Sandboxing is deliberately crude (separate process + timeout): the code is
    written by us, not by a stranger. The subprocess exists so an infinite loop
    or a segfault costs one candidate, not the run.
    """
    harness = textwrap.dedent(f"""
        import json, sys, traceback
        sys.setrecursionlimit(100000)
        src = {src!r}
        g = {{}}
        try:
            exec(compile(src, "candidate", "exec"), g)
            if "construct" not in g:
                print(json.dumps({{"error": "no construct() defined"}})); sys.exit()
            obj = g["construct"]()
        except Exception:
            print(json.dumps({{"error": traceback.format_exc()[-800:]}})); sys.exit()
        print(json.dumps({{"object": obj}}, default=list))
    """)
    try:
        r = subprocess.run([sys.executable, "-c", harness],
                           capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return {"score": None, "error": f"timeout after {timeout}s"}
    if r.returncode != 0:
        return {"score": None, "error": (r.stderr or "")[-800:]}
    try:
        out = json.loads(r.stdout.strip().splitlines()[-1])
    except (json.JSONDecodeError, IndexError):
        return {"score": None, "error": "candidate printed nothing parseable"}
    if "error" in out:
        return {"score": None, "error": out["error"]}
    try:
        return problem.evaluate(out["object"])
    except Exception as e:
        return {"score": None, "error": f"evaluator raised: {e}"}


# ------------------------------------------------------------------ prompt
def build_prompt(problem, name, lens=None, k_best=3):
    """The proposal prompt: state of the art, what failed, and one lens.

    Showing the best-so-far programs is what makes this evolution rather than
    repeated guessing — the LLM improves a lineage instead of restarting.
    Showing the FAILURES is what stops it from re-proposing them, which a
    volume-sampling system can afford to do and we cannot.
    """
    db = load_db(name)
    progs = sorted([p for p in db["programs"] if p["score"] is not None],
                   key=lambda p: -p["score"])
    dead = [p for p in db["programs"] if p["score"] is None][-4:]

    out = []
    out.append("=" * 78)
    out.append(f"OPEN PROBLEM: {name}")
    out.append("=" * 78)
    out.append(problem.STATEMENT.strip())
    out.append("")
    out.append(f"TARGET     : {problem.TARGET.strip()}")
    out.append(f"RECORD     : {problem.RECORD.strip()}")
    out.append("")
    out.append("YOU MUST WRITE a self-contained Python program defining")
    out.append("    def construct():  ->  the object (JSON-serialisable)")
    out.append("It may compute, search, or reason internally, but it must finish")
    out.append("well inside the time limit and RETURN THE OBJECT ITSELF. The")
    out.append("evaluator scores what you return; it does not read your comments.")
    out.append("")

    if progs:
        out.append("-" * 78)
        out.append(f"BEST SO FAR ({len(progs)} scored candidates)")
        out.append("-" * 78)
        for p in progs[:k_best]:
            out.append(f"\n### score {p['score']}   lens={p.get('lens','?')}"
                       f"   idea: {p.get('note','(none)')}")
            out.append("```python")
            out.append(p["src"].strip())
            out.append("```")
        out.append("")
    if dead:
        out.append("-" * 78)
        out.append("RECENT FAILURES — do not repeat these")
        out.append("-" * 78)
        for p in dead:
            out.append(f"  [{p.get('lens','?')}] {p.get('note','')} "
                       f"→ {str(p.get('error'))[:120]}")
        out.append("")

    tried = {p.get("note", "") for p in db["programs"]}
    if tried:
        out.append("IDEAS ALREADY TRIED (do not re-propose):")
        for t in sorted(x for x in tried if x)[:20]:
            out.append(f"  - {t}")
        out.append("")

    out.append("=" * 78)
    if lens:
        out.append(f"YOUR LENS THIS ROUND: {lens.upper()}")
        out.append("=" * 78)
        out.append(textwrap.fill(LENSES[lens], 78))
        out.append("")
        out.append("Do not blend lenses. Push THIS one until it breaks. An idea")
        out.append("that fails in an interesting way is worth more than a safe")
        out.append("variation on the incumbent — we have the incumbent already.")
    else:
        out.append("NO LENS ASSIGNED — argue from the structure of the problem.")
    out.append("")
    out.append("State your idea in ONE sentence, then give the program.")
    return "\n".join(out)


# ------------------------------------------------------------------ commands
def cmd_ingest(problem, name, path, lens, note):
    src = open(path).read()
    db = load_db(name)
    t0 = time.time()
    res = score_program(problem, src)
    entry = {
        "id": len(db["programs"]),
        "src": src,
        "lens": lens,
        "note": note,
        "score": res.get("score"),
        "detail": res.get("detail"),
        "error": res.get("error"),
        "seconds": round(time.time() - t0, 1),
    }
    db["programs"].append(entry)

    best = max((p["score"] for p in db["programs"] if p["score"] is not None),
               default=None)
    db["history"].append({"n": len(db["programs"]), "best": best,
                          "this": entry["score"], "lens": lens})
    save_db(name, db)

    print(f"[{lens}] {note}")
    if entry["score"] is None:
        print(f"  FAILED: {str(entry['error'])[:400]}")
    else:
        print(f"  score = {entry['score']}   ({entry['seconds']}s)")
        if entry["detail"]:
            print(f"  {entry['detail']}")
        print(f"  best so far = {best}")
        if problem.beats_record(entry["score"]):
            print()
            print("  *** THIS BEATS THE PUBLISHED RECORD ***")
            print("  *** run `engine.py verify` before believing a word of it ***")


def cmd_status(problem, name):
    db = load_db(name)
    ok = [p for p in db["programs"] if p["score"] is not None]
    bad = [p for p in db["programs"] if p["score"] is None]
    print(f"problem : {name}")
    print(f"record  : {problem.RECORD.strip()}")
    print(f"scored  : {len(ok)}    failed: {len(bad)}")
    if not ok:
        print("no scored candidates yet")
        return
    ok.sort(key=lambda p: -p["score"])
    print(f"\nbest    : {ok[0]['score']}  "
          f"{'*** BEATS RECORD ***' if problem.beats_record(ok[0]['score']) else ''}")
    print("\n  score      lens         idea")
    for p in ok[:12]:
        print(f"  {str(p['score']):<10} {p.get('lens','?'):<12} "
              f"{(p.get('note') or '')[:46]}")
    by_lens = {}
    for p in ok:
        by_lens.setdefault(p.get("lens", "?"), []).append(p["score"])
    print("\n  lens         n    best")
    for L, ss in sorted(by_lens.items(), key=lambda kv: -max(kv[1])):
        print(f"  {L:<12} {len(ss):<4} {max(ss)}")


def cmd_verify(problem, name):
    """Re-check the champion with the INDEPENDENT, naive verifier.

    The fast evaluator is optimised and therefore trusted less than the slow
    one. If these two ever disagree, the fast one is wrong and the record is
    not a record.
    """
    db = load_db(name)
    ok = [p for p in db["programs"] if p["score"] is not None]
    if not ok:
        sys.exit("nothing to verify")
    champ = max(ok, key=lambda p: p["score"])
    print(f"champion: score {champ['score']}  [{champ.get('lens')}] "
          f"{champ.get('note')}")
    print("rebuilding the object from its program...")
    res = score_program(problem, champ["src"], timeout=600)
    if res.get("score") is None:
        sys.exit(f"REPRODUCTION FAILED: {res.get('error')}")
    if res["score"] != champ["score"]:
        sys.exit(f"NON-DETERMINISTIC: rescored {res['score']} "
                 f"(was {champ['score']}) — a random seed is unpinned")
    print(f"reproduced: {res['score']}")
    print("independent verification (slow, naive)...")
    ok2, msg = problem.verify_champion(champ["src"])
    print(("VERIFIED: " if ok2 else "REJECTED: ") + msg)
    if ok2 and problem.beats_record(champ["score"]):
        print("\nthis is a new record, and it survived an independent check.")


def main():
    p = argparse.ArgumentParser(description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest="op", required=True)
    for op in ("init", "status", "verify"):
        s = sub.add_parser(op)
        s.add_argument("problem")
    s = sub.add_parser("prompt")
    s.add_argument("problem")
    s.add_argument("--lens", choices=sorted(LENSES))
    s = sub.add_parser("ingest")
    s.add_argument("problem")
    s.add_argument("file")
    s.add_argument("--lens", required=True, choices=sorted(LENSES))
    s.add_argument("--note", required=True, help="the idea, in one line")
    a = p.parse_args()

    problem = load_problem(a.problem)
    if a.op == "init":
        run_dir(a.problem)
        db = load_db(a.problem)
        if not db["programs"] and problem.SEED:
            print("scoring the SEED program (the published construction)...")
            tmp = os.path.join(run_dir(a.problem), "seed.py")
            open(tmp, "w").write(problem.SEED)
            cmd_ingest(problem, a.problem, tmp, "algebra", "SEED: published construction")
        else:
            print(f"run already has {len(db['programs'])} candidates")
    elif a.op == "prompt":
        print(build_prompt(problem, a.problem, a.lens))
    elif a.op == "ingest":
        cmd_ingest(problem, a.problem, a.file, a.lens, a.note)
    elif a.op == "status":
        cmd_status(problem, a.problem)
    elif a.op == "verify":
        cmd_verify(problem, a.problem)


if __name__ == "__main__":
    main()
