# Erdős #791 — attack log

**Status: the record stands. We did not beat it.**

Target: `liminf n(k)/k²` for additive 2-bases.
Incumbent: **Kohonen 2017, 85/294 = 0.289115646** (ℓ=42, m=510).
To beat at ℓ=42: **m = 511. One additional covered square.**

## What we ran

| attack | result |
|---|---|
| simulated annealing over raw integer sets, split free | **failed** — returned the incumbent |
| split scan at ℓ=42, every shape, annealed | **catastrophic** — 5–8% efficiency vs Kohonen's 91% |
| structured shape-space annealing (APs + blocks), seeded from Kohonen, 19M iterations | **no improvement** — Kohonen is a hard local optimum |
| exact enumeration of the engine design family, 4320 designs | **none beat him** — optimal within his own class |

## What we learned (this is the real yield)

**1. The problem is not locally searchable.** Annealing from random placements
reaches m≈27–45 where Kohonen reaches 510 — 5–8% of capacity against his 91%.
The object does not live in the space of *sets*; it lives in the space of
*shapes*. Any attack that treats (I,J,K) as bags of integers is dead on arrival.

**2. Kohonen's design, decoded.** Re-encoding his sets as shapes reveals an
engine:

    K ⊇ [0,4]   I ⊇ {0,5}   J = AP with step 6

Each `j ∈ J` buys exactly six squares: `j` and `j+5` from `I+J`, and `j+1..j+4`
from parallelograms (K's block makes `J+K` contain the run `j..j+4`). J's step
is exactly 6, so the blocks **tile with zero waste**. The far parts of I (an AP
of step 5) and K (blocks of length 5–6) then extend the cover to 509, because
`AP(step g) + block(length g)` is a *contiguous* run.

**3. The asymmetry is FORCED, and this kills the balanced-split idea.**
We hoped a balanced split (ceiling 1/3) would beat Kohonen's lopsided 8/17/17
(ceiling 0.318). It cannot, and now we know why: the `J+K` parallelogram
channel is **intrinsically lossy** — a run of length r in `J+K` yields only
`r−1` squares, because a square needs *both* `s` and `s−1`. You therefore
*under-invest* in the lossy channel on purpose. Kohonen's imbalance is not a
hand-design artefact; it is the optimum response to an asymmetric mechanism.
That closes the line of attack we opened this run with.

## What is left

Kohonen's own stated route, and now the only one we can see:

> "no matter how well the placement I,J,K is chosen, the asymptotic ratio n/k²
> achievable through this construction from three elementary segments cannot
> essentially exceed 1/3. If one aims to exceed this ratio, one may want to
> consider **four or more kinds of elementary segments**. The challenge is then
> twofold: first, to design elementary segments with conveniently-shaped
> sumsets that fit together well; and second, to find a good placement."

That is a *design* problem, not a search problem — invent a 4th segment shape
whose pairwise sumsets tile against V, H and S. It is exactly the class the
AlphaEvolve authors named **"AlphaEvolve-hard"**: the machine is good at finding
constructions already within reach of current methods, and bad at inventing the
new mechanism. We should expect it to be hard, and we should not pretend
otherwise.
