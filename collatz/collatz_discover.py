"""
Agent-Solver discovery loop for the Collatz conjecture.

The "agent" is a BFS over the Collatz backward tree rooted at 1, using two
kernel-proved closure rules:

    reaches1_double : reaches1 n            -> reaches1 (2*n)
    reaches1_odd    : n odd -> reaches1 (3n+1) -> reaches1 n

Every number it discovers becomes a named theorem `c_<n> : reaches1 <n>` whose
proof term references previously-derived theorems -- a growing, self-referential
theorem database, exactly the forward-chaining architecture from the original
PoC, except every entry is checked by the Lean kernel instead of trusted.

Output: collatz_db.lean (definitions + closure lemmas + one theorem per number).
"""

import argparse
from collections import deque

HEADER = '''-- AUTO-GENERATED Collatz theorem database (see collatz_discover.py)
def step (n : Nat) : Nat := if n % 2 = 0 then n / 2 else 3 * n + 1
def iter : Nat → Nat → Nat
  | 0,     n => n
  | k + 1, n => iter k (step n)
def reaches1 (n : Nat) : Prop := ∃ k, iter k n = 1

theorem step_double (n : Nat) : step (2 * n) = n := by
  unfold step
  rw [if_pos (Nat.mul_mod_right 2 n), Nat.mul_div_cancel_left _ (by decide : 0 < 2)]

theorem reaches1_double {n : Nat} : reaches1 n → reaches1 (2 * n) := by
  intro ⟨k, hk⟩
  exact ⟨k + 1, by show iter k (step (2 * n)) = 1; rw [step_double]; exact hk⟩

theorem reaches1_odd {n : Nat} (hodd : n % 2 = 1) :
    reaches1 (3 * n + 1) → reaches1 n := by
  intro ⟨k, hk⟩
  refine ⟨k + 1, ?_⟩
  show iter k (step n) = 1
  unfold step
  rw [if_neg (by omega : ¬ n % 2 = 0)]
  exact hk

theorem c_1 : reaches1 1 := ⟨0, rfl⟩
'''


def discover(max_value: int, max_theorems: int):
    """BFS the backward Collatz tree from 1; return [(n, proof_line)] in order."""
    proofs = {1: "c_1"}
    order = []
    queue = deque([1])
    while queue and len(order) < max_theorems:
        n = queue.popleft()
        # Rule 1: n verified => 2n verified.
        d = 2 * n
        if d <= max_value and d not in proofs:
            proofs[d] = "c_{}".format(d)
            order.append((d, "theorem c_{} : reaches1 {} := reaches1_double c_{}"
                          .format(d, d, n)))
            queue.append(d)
        # Rule 2: n verified and n = 3m+1 for odd m>1 => m verified.
        if n % 3 == 1 and n > 4:
            m = (n - 1) // 3
            if m % 2 == 1 and m > 1 and m not in proofs:
                proofs[m] = "c_{}".format(m)
                order.append((m, "theorem c_{} : reaches1 {} := "
                                 "reaches1_odd (n := {}) (by decide) c_{}"
                              .format(m, m, m, n)))
                queue.append(m)
    return order


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-value", type=int, default=200_000)
    ap.add_argument("--max-theorems", type=int, default=400)
    ap.add_argument("--out", default="/tmp/collatz_db.lean")
    args = ap.parse_args()

    order = discover(args.max_value, args.max_theorems)
    with open(args.out, "w") as f:
        f.write(HEADER)
        f.write("\n-- ===== discovered theorems ({}) =====\n".format(len(order)))
        for _, line in order:
            f.write(line + "\n")

    ns = sorted(n for n, _ in order) + [1]
    small = [n for n in ns if n <= 60]
    print("discovered {} numbers (plus the root 1)".format(len(order)))
    print("smallest verified: {}".format(sorted(small)))
    print("largest verified: {}".format(max(ns)))
    print("lean file: {}".format(args.out))


if __name__ == "__main__":
    main()
