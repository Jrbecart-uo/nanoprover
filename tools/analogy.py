#!/usr/bin/env python3
"""ANALOGY — "this new problem is the old one wearing a different coat."

Mathematicians do not search the literature when stuck; they remember a problem
that FELT like this one. This indexes the solved corpus so the machine can do
the same: score a new goal against every proof we have ever landed, and surface
the closest few — with the tactic that carried them and, where we have it, the
STORY: what the proof is really doing, said in terms of the physical world.

The story matters. "Finset.sum_involution over n.divisors" retrieves nothing
from a human brain. "Pair every dancer with their partner; partners cancel"
retrieves the idea instantly — and the idea is what transfers to a new problem,
not the lemma name. A proof you can only recall by its API is a proof you can
only reuse when the API matches.

Usage:
  analogy.py match FILE      # top matches for a goal (theorem with := by sorry)
  analogy.py match --text "∀ n, 24 ∣ ∑ d in n.divisors, d"
  analogy.py index           # rebuild + show the whole index
"""

import argparse
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(HERE)
CORPUS = {"putnam": os.path.join(REPO, "bench", "solved_putnam"),
          "imo": os.path.join(REPO, "bench", "solved_imo")}
INDEX = os.path.join(REPO, "data", "pattern_index.json")

# ---------------------------------------------------------------- features
# A feature fires on a *shape*, not a name: shapes are what recur across
# problems, names are what change between mathlib versions.
FEATURES = {
    "divisibility":  [r"∣", r"Dvd", r"dvd"],
    "congruence":    [r"MOD", r"ModEq", r"ZMod", r"%"],
    "primes":        [r"Prime", r"prime", r"totient", r"Coprime"],
    "divisor_sum":   [r"divisors", r"σ", r"sigma"],
    "binomial":      [r"choose", r"Nat\.choose", r"add_pow"],
    "finset_sum":    [r"∑", r"Finset\.sum", r"sum_"],
    "finset_prod":   [r"∏", r"Finset\.prod", r"prod_"],
    "recurrence":    [r"induction", r"ih\b", r"Nat\.rec", r"strong_induction"],
    "sequence":      [r"a\s*\(", r"x\s*\d", r"Filter", r"Tendsto", r"seq"],
    "inequality":    [r"≤", r"<", r"nlinarith", r"linarith", r"Cauchy"],
    "abs_norm":      [r"\|", r"abs", r"norm", r"normSq"],
    "complex":       [r"ℂ", r"Complex", r"cpow", r"I\b"],
    "real_analysis": [r"ℝ", r"deriv", r"∫", r"Real\.", r"exp", r"log"],
    "polynomial":    [r"Polynomial", r"roots", r"eval", r"degree"],
    "group":         [r"Group", r"⁻¹", r"zpow", r"orderOf", r"Subgroup"],
    "matrix":        [r"Matrix", r"det", r"trace"],
    "cardinality":   [r"ncard", r"card", r"Fintype", r"pigeonhole"],
    "set":           [r"Set\.", r"∈", r"⊆", r"∩", r"∪"],
    "functional_eq": [r"f\s*\(f", r"f\s*\(", r"∀ x"],
    "existence":     [r"∃"],
    "uniqueness":    [r"∃!", r"unique"],
    "invariant":     [r"invariant", r"conserv"],
    "parity":        [r"Even", r"Odd", r"parity"],
}

# ------------------------------------------------------------------ stories
# The transferable idea, in physical terms. Written only where we actually
# know what the proof does (from the solve itself) — never invented to fill a
# row. A missing story is reported as missing.
STORIES = {
    "putnam_2007_a5":
        "COUNT THE NECKLACES. Write down every p-bead necklace whose beads "
        "multiply to 1: there are |G|^(p-1) of them, a multiple of p. Turning "
        "a necklace one click moves it; only the one-colour necklaces "
        "(g,...,g) with g^p = 1 stay put. Everything else comes in orbits of "
        "size p, so the still ones are also a multiple of p: 1 + n.",
    "putnam_1974_b3":
        "THE DENOMINATOR THAT KEEPS GROWING. Doubling the angle squares the "
        "cosine (2x^2-1): starting from 1/3 the denominators run 3, 9, 81, "
        "3^(2^k) and never cancel (3 never divides the numerator), so the "
        "values never repeat. A rational angle is a clock hand: doubling it "
        "can only visit finitely many positions. Infinitely many distinct "
        "values vs finitely many positions — alpha cannot be rational.",
    "putnam_1969_b1":
        "PAIR OFF THE DANCERS. Every divisor d has a partner n/d; the two "
        "cancel mod 24, and nobody is their own partner. Sum dies by pairing.",
    "putnam_1996_a5":
        "PAIR OFF THE DANCERS, ON THE MIDDLE THIRD. p | C(p,i) lets you divide "
        "the whole problem by p, dropping it into the FIELD ZMod p. What is "
        "left is a harmonic sum over (p/3, 2p/3] — a range symmetric under "
        "i ↦ p-i, where 1/(p-i) = -1/i. The sum is its own negative: it is 0.",
    "putnam_1997_b5":
        "THE TOWER STOPS MATTERING. Above a certain height a power tower is "
        "invisible mod n — like a clock, only the remainder shows. Recurse on "
        "the MODULUS (Euler/totient), not on the tower.",
    "putnam_1991_b4":
        "BELOW THE NOISE FLOOR. Working mod p², anything carrying p² is dust: "
        "drop it. Cross terms vanish and a hard binomial identity goes linear.",
    "putnam_1968_b2":
        "MORE PIGEONS THAN HOLES. Two sets whose sizes together exceed the "
        "room must overlap — and one shared element is the whole theorem.",
    "putnam_1993_a2":
        "A CONSERVED QUANTITY. Like energy: a ratio built from the sequence "
        "never changes. Measure it once at the start; it pins every later term.",
    "putnam_1988_a5":
        "THE RUNAWAY FEEDBACK LOOP. Any nonzero error is amplified by (9/4) "
        "each step and escapes every bound — so the error must be exactly zero.",
    "putnam_1972_b3":
        "GEARS IN A MACHINE. The relation lets you rewind any word back to the "
        "identity; grind the word down until B has finite order, then Bezout.",
    "putnam_1989_a3":
        "PINNED TO THE RIM. Not inside the circle, not outside it — so every "
        "root lies exactly ON it. Trichotomy does the work.",
    "putnam_1979_b6":
        "A DETOUR IS NEVER SHORTER. Cauchy–Schwarz / triangle inequality: the "
        "straight-line quantity bounds the wandering one.",
    "putnam_2004_b2":
        "ONE TERM NEVER BEATS THE WHOLE SUM. Compare a single binomial term "
        "against the full expansion it sits inside.",
    "putnam_2010_a4":
        "A SELF-SIMILAR FACTORY. Each doubling reproduces the same structure, "
        "so one divisor found at the bottom propagates all the way up.",
    "putnam_2020_b5":
        "EVERYTHING STAYS ON THE RIM. The map z ↦ 1/(1-z) sends the unit "
        "circle to the line Re = 1/2; the constraint survives the transform.",
    "putnam_1977_a5":
        "DIGIT-WISE BOOKKEEPING (LUCAS). In base p the digits do not talk to "
        "each other — a binomial coefficient factors digit by digit.",
    "imo_1981_p6":
        "UNWIND THE RECURSION. Ackermann-style: the same instruction applied "
        "over and over; find the closed form of each layer, then induct.",
}


def featurize(text):
    f = set()
    for name, pats in FEATURES.items():
        if any(re.search(p, text) for p in pats):
            f.add(name)
    return f


def tactics_of(proof):
    tacs = re.findall(
        r"\b(nlinarith|linarith|omega|decide|simp_all|simp|norm_num|ring_nf|"
        r"ring|field_simp|positivity|induction|rcases|obtain|refine|calc|"
        r"linear_combination|push_cast|zify|interval_cases|aesop|gcongr|"
        r"Finset\.sum_involution|exact\?)\b", proof)
    seen, out = set(), []
    for t in tacs:
        if t not in seen:
            seen.add(t)
            out.append(t)
    return out[:8]


def statement_of(text, name=None):
    """The MAIN theorem's statement: from `theorem <name>` up to `:=`.

    Anchor on the theorem whose name matches the file — a corpus proof opens
    with helper lemmas and defs, and the main result may close in term mode
    (`:= foo n h`, no `by`). Matching the first `theorem ... := by` silently
    indexed a file's scaffolding as if it were the problem.
    """
    if name:
        m = re.search(r"theorem\s+" + re.escape(name) + r"\b(.*?):=", text, re.S)
        if m:
            return re.sub(r"\s+", " ", m.group(0))
    ms = list(re.finditer(r"(theorem|lemma)\s+\w+(.*?):=", text, re.S))
    return re.sub(r"\s+", " ", ms[-1].group(0)) if ms else text[:300]


def build():
    idx = []
    for bench, d in CORPUS.items():
        if not os.path.isdir(d):
            continue
        for fn in sorted(os.listdir(d)):
            name = fn.rsplit(".", 1)[0]
            text = open(os.path.join(d, fn)).read()
            stmt = statement_of(text, name)
            idx.append({
                "name": name,
                "bench": bench,
                # Features come from the STATEMENT — what the problem IS.
                # Featurizing the whole proof imports the solution's incidental
                # vocabulary as if it described the question, and every long
                # proof then looks like every other long proof.
                "features": sorted(featurize(stmt)),
                "tactics": tactics_of(text),
                "story": STORIES.get(name),
                "statement": stmt[:220],
                "path": os.path.join(d, fn),
                "lines": text.count("\n") + 1,
            })
    os.makedirs(os.path.dirname(INDEX), exist_ok=True)
    with open(INDEX, "w") as f:
        json.dump(idx, f, indent=1, ensure_ascii=False)
    return idx


def load():
    if not os.path.exists(INDEX):
        return build()
    return json.load(open(INDEX))


def match(text, k=3):
    idx = load()
    want = featurize(text)
    if not want:
        print("no features fired on this goal — nothing to match on")
        return
    # IDF: a feature shared by everything ("inequality", "set") says nothing;
    # a rare one ("divisor_sum") is the whole signal. Weight by rarity or the
    # common features drown the informative ones.
    import math
    N = len(idx)
    df = {f: sum(1 for e in idx if f in e["features"]) for f in FEATURES}
    idf = {f: math.log((N + 1) / (df.get(f, 0) + 1)) + 0.1 for f in FEATURES}

    # Cosine, not Jaccard: Jaccard divides by the UNION, so a proof with a rich
    # statement is punished for every feature the query lacks — the deepest
    # proofs in the corpus rank last exactly when they are the right analogy.
    scored = []
    for e in idx:
        have = set(e["features"])
        inter = want & have
        if not inter:
            continue
        num = sum(idf[f] ** 2 for f in inter)
        den = (math.sqrt(sum(idf[f] ** 2 for f in want)) *
               math.sqrt(sum(idf[f] ** 2 for f in have)))
        scored.append((num / den, sorted(inter, key=lambda f: -idf[f]), e))
    scored.sort(key=lambda t: -t[0])

    print(f"goal features: {sorted(want)}\n")
    if not scored:
        print("nothing in the corpus shares a feature with this goal.")
        return
    for j, shared, e in scored[:k]:
        print("=" * 72)
        print(f"{e['name']}  ({e['bench']}, {e['lines']} lines)   "
              f"similarity {j:.2f}   shared: {', '.join(shared)}")
        if e["story"]:
            print(f"\n  IDEA: {e['story']}")
        else:
            print("\n  IDEA: (not yet written — see the proof)")
        print(f"\n  tactics: {' → '.join(e['tactics'])}")
        print(f"  proof:   {e['path']}")
        print()


def main():
    p = argparse.ArgumentParser(description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest="op", required=True)
    m = sub.add_parser("match")
    m.add_argument("file", nargs="?")
    m.add_argument("--text")
    m.add_argument("-k", type=int, default=3)
    sub.add_parser("index")
    a = p.parse_args()

    if a.op == "index":
        idx = build()
        print(f"indexed {len(idx)} solved proofs -> {INDEX}")
        nostory = [e["name"] for e in idx if not e["story"]]
        for e in idx:
            print(f"  {e['name']:22s} {','.join(e['features'])}")
        print(f"\nstories written: {len(idx) - len(nostory)}/{len(idx)}")
        if nostory:
            print(f"still need a story: {', '.join(nostory)}")
    else:
        text = a.text if a.text else open(a.file).read()
        match(text, a.k)


if __name__ == "__main__":
    main()
