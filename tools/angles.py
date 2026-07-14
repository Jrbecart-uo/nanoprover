#!/usr/bin/env python3
"""ANGLES — look at the goal from somewhere else, and actually SEE it.

"Try a different angle" is advice, not a tactic. This makes it mechanical:
apply every standard reframing to the real proof state and print the goal each
one produces. You are not imagining the reformulation — the kernel hands it to
you, and you pick the one that looks tractable.

The moves are the ones a human reaches for when stuck: flip the implication,
push the negation inward, assume the opposite, move to a ring where the
arithmetic is honest (ℕ subtraction is a liar — zify), split the world into
cases, induct, or reduce an equality to two inequalities.

Usage:  angles.py FILE          # FILE holds one theorem with `:= by sorry`

Needs the REPL daemon (tools/repl.py start).
"""

import argparse
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import repl as R  # noqa: E402
import salt as S  # noqa: E402


# name -> (tactic, why you would ever want this)
ANGLES = [
    ("contrapose",     "contrapose!",
     "prove the contrapositive: assume the goal false, derive the hypothesis false"),
    ("by_contra",      "by_contra hcon; push_neg at hcon",
     "assume the opposite and hunt for the contradiction"),
    ("push_neg",       "push_neg",
     "drive negations inward until they hit atoms"),
    ("zify",           "zify",
     "leave ℕ for ℤ — ℕ subtraction truncates and will lie to you"),
    ("push_cast",      "push_cast",
     "normalise casts so ring/omega can see through them"),
    ("field_simp",     "field_simp",
     "clear denominators"),
    ("ring_nf",        "ring_nf",
     "normalise the algebra; sometimes the goal just falls out"),
    ("sub_nonneg",     "rw [← sub_nonneg]",
     "a ≤ b becomes 0 ≤ b - a: now positivity/nlinarith can work"),
    ("le_antisymm",    "apply le_antisymm",
     "split an equality into two inequalities"),
    ("constructor",    "constructor",
     "split a conjunction / iff into its halves"),
    ("dvd_unfold",     "rw [Nat.dvd_iff_exists_eq_mul_left]",
     "turn divisibility into an explicit witness"),
    ("modeq_unfold",   "rw [Nat.ModEq]",
     "turn a congruence into an equation on remainders"),
    ("cases_zero",     "rcases Nat.eq_zero_or_pos n with rfl | hpos",
     "split n = 0 from n > 0 (the degenerate case is usually free)"),
    ("le_total",       "rcases le_total a b with hab | hab",
     "WLOG-style: one of the two orderings must hold"),
    ("induction",      "induction n with | zero => ?_ | succ k ih => ?_",
     "peel the naturals"),
    ("strong_ind",     "induction n using Nat.strong_induction_on with | _ n ih => ?_",
     "strong induction: the IH covers ALL smaller values"),
    ("parity",         "rcases Nat.even_or_odd n with he | ho",
     "split on parity"),
    ("symm",           "symm",
     "prove the equality the other way round"),
    ("exfalso",        "exfalso",
     "abandon the goal; find the contradiction instead"),
    ("specialize",     "simp_all",
     "let simp grind the hypotheses into the goal"),
]


def run(path):
    text = open(path).read()
    text = "\n".join(l for l in text.splitlines()
                     if not l.strip().startswith("import "))
    header = text.split(":= by")[0].strip()
    goal = S.goal_of(header)
    hyps, atoms, target, _ = S.parse_goal(goal)

    print("=" * 74)
    print("GOAL")
    print(goal)
    print("=" * 74)

    # substitute real variable names into the schematic angles
    nats = [a for a, k in atoms.items() if k == "nat"] or ["n"]
    nums = [a for a, k in atoms.items() if k in S.NUMERIC] or ["a", "b"]
    n0 = nats[0]
    a0, b0 = (nums + nums)[0], (nums + nums)[1] if len(nums) > 1 else nums[0]

    resp = R.ask({"cmd": header + " := by sorry"})
    ps = resp["sorries"][0]["proofState"]

    hits, dead = [], []
    for name, tac, why in ANGLES:
        t = (tac.replace(" n ", f" {n0} ").replace(" n with", f" {n0} with")
                .replace(" a ", f" {a0} ").replace(" b ", f" {b0} "))
        r = R.ask({"tactic": t, "proofState": ps})
        if "message" in r and "error" in r["message"].lower():
            dead.append(name)
            continue
        if r.get("proofStatus", "").startswith("Completed"):
            print(f"\n*** {name}  ({t})  CLOSES THE GOAL OUTRIGHT ***")
            print(f"    {why}")
            hits.append(name)
            continue
        goals = r.get("goals", [])
        if not goals:
            dead.append(name)
            continue
        hits.append(name)
        print(f"\n── {name}  ──  {t}")
        print(f"   why: {why}")
        for g in goals[:2]:
            body = "\n".join("      " + l for l in g.split("\n"))
            print(body)
        if len(goals) > 2:
            print(f"      ... (+{len(goals) - 2} more goals)")

    print("\n" + "=" * 74)
    print(f"{len(hits)} angles opened; not applicable here: {', '.join(dead)}")


def main():
    p = argparse.ArgumentParser(description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("file")
    a = p.parse_args()
    if R._ping() is None:
        sys.exit("REPL daemon not running: python3 tools/repl.py start")
    run(a.file)


if __name__ == "__main__":
    main()
