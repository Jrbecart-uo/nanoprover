# Erdős #791 — attack log

**Status: the record stands. We did not beat it.**

Incumbent: **Kohonen 2017, 85/294 = 0.289115646** (ℓ=42, m=510).
To beat at ℓ=42: **m = 511 — one additional covered square.**

## Attacks run, and how they died

| attack | best ratio | vs record |
|---|---|---|
| annealing over raw integer sets | returned incumbent | — |
| split scan at ℓ=42, every shape, annealed | **5–8% efficiency** (Kohonen: 91%) | hopeless |
| structured shape-space annealing, seeded from Kohonen, **19M iterations** | 0.289115646 | no improvement — hard local optimum |
| exact enumeration of the engine family (4,320 designs) | < record | none better |
| greedy structural growth (scan over g, t) | **0.282380** | short by 0.0067 |
| beam search over grafts | did not finish in budget | — |

**Every automated search we built loses to a construction one person built partly
by hand in 2016.** That is the honest headline, and it is exactly what the
literature warns about (Ellenberg on PatternBoost: optimal to n=33, "loses to
humans" beyond; "simple baselines are competitive with code evolution").

## CORRECTION to an earlier claim in this file

I previously wrote that Kohonen's lopsided split is **forced** because the J+K
parallelogram channel is "intrinsically lossy". **That was wrong, and I am
striking it.** A run of length *r* in J+K yields *r−1* squares — the loss is
**one square per run**, not half the channel. Long runs are nearly 100%
efficient. The balanced-split ceiling of 1/3 is therefore *not* excluded by
this mechanism. Our searches failed to realise it; that is a statement about
our searches, not a theorem about the problem.

## The design theory we did extract (this part is solid)

Kohonen's construction is a **two-stage machine**:

**Stage 1 — the engine.** `K ⊇ [0,g−1]`, `I ⊇ {0,g}`, `J` = AP of step `g+1`.
Each `j ∈ J` buys `g+1` squares: `j` and `j+g` from `I+J`, and `j+1 … j+g−1`
from parallelograms (K's block makes `J+K` contain the run `j … j+g−1`). J's
step is exactly `g+1`, so the blocks **tile with zero waste**.

* The J×K channel leaks exactly **1/g** (a run of g yields g−1 squares).
  Kohonen's g=5 leaks 20%; g=10 would leak only 10%.
* **But the engine alone is capped at 1/4**, for any g and t:
  `m = t(g+1)`, `ℓ = t+g+2` → ratio → 1/4. It cannot reach 0.289.

**Stage 2 — the extension.** Only the extension stages push past 1/4, by
*reusing* I against K: an AP of step g plus a block of length g gives a
**contiguous** run. Kohonen's far blocks ([224,229], [367,372]) each pair with
*both* J (parallelograms) and I's AP (contiguous runs) — one block doing two
jobs. That double duty is what our greedy could never see, and it is where his
extra 0.007 lives.

So the real optimisation is a joint one over (g, engine length, extension
placements) that trades the 1/g leak against extension efficiency. **Nobody has
done it, including us.**

## What is actually left

1. **Exact optimisation at ℓ ≈ 42–50** (ILP/SAT). Kohonen's own exhaustive
   frontier is ℓ ≤ 17. Settling ℓ = 42 exactly would either produce m ≥ 511 or
   prove his placement optimal at that size. This is the highest-value next
   step and it is a real build.
2. **A fourth segment shape** — Kohonen's own suggested route, which breaks the
   1/3 ceiling of the three-segment ansatz entirely. A design problem, not a
   search problem: precisely the class the AlphaEvolve authors call
   **"AlphaEvolve-hard"**, where machines are weakest.

## The honest lesson

Our best automated design reaches 0.2824. A human reached 0.2891 nine years ago
with pen and paper and a small program. The gap is not compute — we spent
millions of evaluations. The gap is **one idea** (a block that serves two
mechanisms at once), and we did not find it.
