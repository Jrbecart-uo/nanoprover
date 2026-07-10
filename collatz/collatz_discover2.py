"""
INNER LOOP, re-oriented with the new gear.

Old strategy (collatz_discover.py): BFS *backward* from 1 with two parity rules.
Stalled at 82% coverage of 1..100 even with 10,000 theorems.

New strategy, enabled by the kernel-proved orbit-jump lemma
    reaches1_iter : ∀ k n, reaches1 (iter k n) → reaches1 n
For any n, just COMPUTE the forward orbit until it hits 1 (k steps), then emit
    theorem c_<n> : reaches1 <n> := reaches1_iter <k> <n> reaches1_one
The kernel re-computes iter k n itself when checking -- Python only supplies
the witness k; nothing is trusted. Every proof is one line, coverage is total.
"""

import argparse
import os

GEAR = os.path.join(os.path.dirname(__file__), "proved_gear.lean")


def orbit_length(n: int, cap: int = 100_000):
    k, m = 0, n
    while m != 1:
        m = m // 2 if m % 2 == 0 else 3 * m + 1
        k += 1
        if k > cap:
            return None  # would-be counterexample (never happens below 2^68)
    return k


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--upto", type=int, default=1000)
    ap.add_argument("--out", default="/tmp/collatz_db2.lean")
    args = ap.parse_args()

    lines = []
    worst = (0, 0)
    for n in range(2, args.upto + 1):
        k = orbit_length(n)
        if k is None:
            print("!! n={} exceeded orbit cap -- investigate!".format(n))
            continue
        worst = max(worst, (k, n))
        lines.append("theorem c_{} : reaches1 {} := reaches1_iter {} {} reaches1_one"
                     .format(n, n, k, n))

    with open(args.out, "w") as f:
        # deep orbits (n=871 needs 178 iter-unfoldings) exceed the elaborator's
        # default recursion limit during the defeq check
        f.write("set_option maxRecDepth 1000000\n")
        f.write(open(GEAR).read())
        f.write("\n-- ===== complete verified range 2..{} =====\n".format(args.upto))
        f.write("\n".join(lines) + "\n")

    print("emitted {} theorems (complete coverage 1..{})".format(len(lines), args.upto))
    print("longest orbit: n={} needs {} steps".format(worst[1], worst[0]))
    print("lean file: {}".format(args.out))


if __name__ == "__main__":
    main()
