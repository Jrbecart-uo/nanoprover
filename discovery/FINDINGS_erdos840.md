# Erdős #840 — quasi-Sidon sets: attacked, no improvement (and why)

**Target (open since 1991):** `f(N)` = size of the largest quasi-Sidon
`A ⊆ [1,N]`, where quasi-Sidon means `|A+A| = (1+o(1))·C(|A|,2)` (almost all
pairwise sums distinct). Bounds:

    (2/√3 + o(1))·√N  ≤  f(N)  ≤  (1.863… + o(1))·√N
    Erdős–Freud 1991        Pikhurko 2006

The lower bound `2/√3 ≈ 1.1547` is a construction; beating it (a family with
`r = |A|/√N → c > 1.1547` and `δ = |A+A|/C(|A|,2) → 1`) is a new record.

## What we did

1. **Verified evaluator.** Built the Bose optimal Sidon set (size `q`,
   density → 1, Sidon mod `q²−1`) and reproduced the known construction
   `A = B ∪ (N+1−B)` with `B` in the first third `[1,N/3]`. It hits `r → 1.1547`
   with `δ → 1` exactly — the Erdős–Freud lower bound, confirmed.

2. **Understood *why* thirds.** The three sumset components live in disjoint
   intervals iff the placement fraction `α ≤ 1/3`:
   `B+B ⊆ [2, 2αN]`, `B+mirror = (N+1)+(B−B) ⊆ [(1−α)N, (1+α)N]`,
   `mirror+mirror ⊆ [(2−2α)N, 2N]`. Disjointness of the first two needs
   `2αN ≤ (1−α)N ⇔ α ≤ 1/3`. So **`2/√3 = 2√(1/3)` is exactly the
   disjointness threshold** — the same structural reason #791's bound is what
   it is.

3. **Caught a finite-size trap.** Pushing the fraction past `1/3`
   (`α = 1/2.7 → r = 1.217`) shows `δ ≈ 0.9998` at small `N` — apparently a new
   record. It is not. Tracking `δ` to `q = 4001` (`|A| ≈ 8000`):

   | α | r | δ at q=211 | δ at q=4001 | verdict |
   |---|---|---|---|---|
   | 1/3    | 1.1547 | 1.0024 | 1.00013 | → 1 ✓ quasi-Sidon |
   | 1/2.85 | 1.1847 | 1.0019 | 0.99987 | crosses below 1, tiny deficit |
   | 1/2.7  | 1.2172 | 0.9998 | 0.99814 | settles ~0.998 < 1 ✗ |
   | 1/2.5  | 1.2649 | 0.9894 | 0.99044 | ~0.99 < 1 ✗ |

   Past `α = 1/3` the overlap collisions do **not** vanish — `δ` stabilises
   *below* 1, so the sets are not asymptotically quasi-Sidon. The small-`N`
   `δ ≈ 1` was a mirage. **No valid improvement.**

## Honest conclusion

The reflection-fraction knob — the obvious thing to vary — is at its optimum,
and `2/√3` is exactly the disjointness threshold. Beating it requires a
genuinely different construction where extra density does *not* cause
`Θ(collisions)`; searching the reflection family cannot reach it. That is why
a 30-year-old bound is 30 years old.

The value of this run: a **verified evaluator + the structural reason for the
bound**, and a clean example of the finite-size self-deception trap being
caught by testing `δ` as `N → ∞` rather than trusting one `N`. Exactly the
discipline the discovery engine's independent-verify step exists to enforce.
