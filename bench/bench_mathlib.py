"""
Baseline experiment: how far do builtin tactics get on mathlib-style goals,
and what does premise retrieval add?

Runs each goal through LeanCLIEnv (mathlib mode) twice:
  A) builtins only            (rfl/simp/omega/norm_num/linarith/exact?/...)
  B) builtins + LibraryAgent  (premise retrieval from the local index)

The residual -- goals neither solves -- is the map of where an LLM proposer
(or a human in sherpa) earns its place in the portfolio.

    python bench/bench_mathlib.py            # full run
    python bench/bench_mathlib.py --half 0   # goals 0..N/2 (fits a time cap)
    python bench/bench_mathlib.py --half 1
"""

import argparse
import json
import os
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "core"))

from lean_cli_env import LeanCLIEnv
from agents import BuiltinAgent, LibraryAgent, PortfolioAgent
from search import search

MATHLIB = os.environ.get("NANOPROVER_MATHLIB_DIR",
                         os.path.join(ROOT, "mathlib4"))

PRE_REAL = "import Mathlib.Data.Real.Basic\nimport Mathlib.Tactic"
PRE_NAT = "import Mathlib.Data.Nat.Prime.Basic\nimport Mathlib.Tactic"

GOALS = [
    # -- expected builtin wins --
    ("binom_sq",     PRE_REAL, "(a b : ℝ) : (a + b)^2 = a^2 + 2*a*b + b^2"),
    ("sq_nonneg",    PRE_REAL, "(x : ℝ) : 0 ≤ x^2"),
    ("and_swap",     "import Mathlib.Tactic", "(p q : Prop) : p ∧ q → q ∧ p"),
    ("nat_arith",    "import Mathlib.Tactic", "(n : Nat) : n + n = 2 * n"),
    # -- single-lemma goals (exact? or retrieval should land these) --
    ("abs_triangle", PRE_REAL, "(a b : ℝ) : |a + b| ≤ |a| + |b|"),
    ("prime_two_le", PRE_NAT,  "(p : ℕ) : p.Prime → 2 ≤ p"),
    ("abs_sub_comm", PRE_REAL, "(a b : ℝ) : |a - b| = |b - a|"),
    ("mul_self_abs", PRE_REAL, "(a : ℝ) : |a| * |a| = a * a"),
    # -- multi-step / harder (expected residual without an LLM) --
    ("abs_le_iff",   PRE_REAL, "(a b : ℝ) : |a| ≤ b ↔ -b ≤ a ∧ a ≤ b"),
    ("min_le_max",   PRE_REAL, "(a b : ℝ) : min a b ≤ max a b"),
    ("prime_dvd_or", PRE_NAT,  "(p m n : ℕ) : p.Prime → p ∣ m * n → p ∣ m ∨ p ∣ n"),
    ("sq_abs_sub",   PRE_REAL, "(a b : ℝ) : (|a| - |b|)^2 ≤ (a - b)^2 ∨ |a - b| ≤ |a| + |b|"),
]

# Builtins trimmed for mathlib mode: 'decide' can hang on Real goals.
MATHLIB_BUILTINS = ["rfl", "simp", "norm_num", "positivity", "omega",
                    "linarith", "aesop", "tauto", "ring", "exact?"]


def run_config(goals, agent, label):
    results = {}
    for name, pre, sig in goals:
        env = LeanCLIEnv(signature=sig, preamble=pre,
                         lean_cmd=["lake", "env", "lean"], cwd=MATHLIB,
                         timeout=90)
        t0 = time.time()
        r = search(env, agent, branching=14, max_expansions=1, verbose=False)
        dt = time.time() - t0
        results[name] = {"solved": r.solved, "proof": r.proof, "secs": round(dt, 1)}
        print("  [{}] {:14s} {}  ({}s){}".format(
            label, name,
            "SOLVED" if r.solved else "  --  ",
            round(dt, 1),
            "  via " + " ; ".join(r.proof) if r.solved else ""))
    return results


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--half", type=int, choices=[0, 1], default=None)
    ap.add_argument("--out", default="/tmp/bench_results.json")
    args = ap.parse_args()

    goals = GOALS
    if args.half is not None:
        mid = len(GOALS) // 2
        goals = GOALS[:mid] if args.half == 0 else GOALS[mid:]

    print("== A: builtins only ==")
    a = run_config(goals, PortfolioAgent([BuiltinAgent(MATHLIB_BUILTINS)]), "A")
    print("== B: builtins + premise retrieval ==")
    b = run_config(goals, PortfolioAgent([BuiltinAgent(MATHLIB_BUILTINS),
                                          LibraryAgent(k=4)]), "B")

    na = sum(1 for r in a.values() if r["solved"])
    nb = sum(1 for r in b.values() if r["solved"])
    print("\nsolve rate: builtins {}/{}   builtins+library {}/{}"
          .format(na, len(goals), nb, len(goals)))
    residual = [n for n in b if not b[n]["solved"]]
    if residual:
        print("residual (LLM/human territory): {}".format(", ".join(residual)))

    payload = {"A_builtins": a, "B_with_library": b}
    mode = "r+" if os.path.exists(args.out) and args.half is not None else "w"
    if mode == "r+":
        with open(args.out) as f:
            prev = json.load(f)
        for k in payload:
            prev[k].update(payload[k])
        payload = prev
    with open(args.out, "w") as f:
        json.dump(payload, f, indent=1)
    print("results -> {}".format(args.out))


if __name__ == "__main__":
    main()
