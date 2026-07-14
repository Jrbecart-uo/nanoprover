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

---

# Round 2 — structural results (no record, but real knowledge)

Five more attacks. **The record still stands.** But three structural facts came
out, and they are worth more than another failed annealer.

## 1. The counting ceiling of 1/3 is NOT attainable (new)

Kohonen bounds the three-segment ansatz by `m/ℓ² ≤ 1/3` via counting. That bound
**cannot be met**, and here is why. To run all three channels at full capacity,
`I+J`, `I+K` and `J+K` would each have to be a *perfect tiling* (sumset = an
interval of size |X|·|Y|). But if `I⊕J` and `I⊕K` are both perfect, then as
polynomials `I(q)·J(q)` and `I(q)·K(q)` are both interval polynomials, so
**J and K are translates of each other** — and then `J+K` collapses from `n²` to
`2n−1`. Verified numerically: block ⊕ AP ⊕ AP(shifted) gives |I+J| = |I+K| = 36
(perfect) and |J+K| = **11**, not 36. The third channel dies.

**All three channels cannot be perfect. The true ceiling is strictly below 1/3.**
Kohonen only ever proved the loose counting bound.

## 2. Kohonen is a very deep local optimum

| search | result |
|---|---|
| structured annealing, 19M iterations | no improvement |
| **exhaustive coordinate descent** (every parameter swept over its full range) | **strict local optimum** |
| **joint moves** (grow I's AP *and* relocate the far blocks together) | no improvement |

The joint scan mattered: the marginal value of an I element is |J|+|K| = 34,
well above the break-even 2m/ℓ = 24.3, so *more I ought to pay* — but only if
the far blocks move with it. Neither move helps alone. We scanned them together
and it still fails. His placement is not luck.

Where his 51 wasted capacity units go: **12** to `I+K` collisions (his far blocks
have length 6 against a step-5 AP — a deliberate trade, since longer blocks make
better parallelogram runs), **20** to double-covered squares, ~**19** to
parallelogram run-boundaries.

## 3. There may be NO fourth elementary segment (evidence, not proof)

Kohonen's own escape route is "four or more kinds of elementary segments," which
would lift the ceiling from 1/3 to **3/8**. We looked for one.

A fourth segment T must give a square with V (`V+T ⊇ Q`) and working
parallelograms with *both* H and S. With `T` = the other diagonal (step t−1):
`V+T` ⊇ Q ✓, `H+T` ✓ — but **`S+T` is dead**. And with `S+T` dead the ceiling
falls straight back to 1/3, so it buys nothing.

We then searched exhaustively:
* **all AP fourth segments** (every step, every length, t = 10,12,14,16): none.
* **all mixed-step segments** over the forced gap alphabet {t−1, t, t+1} —
  **180,132 candidates at t=10**: none.

**Caveat, and it is a real one:** this tests the *standard mechanism*, where each
tile must cover a square alone or in consecutive pairs. Tiles are in principle
allowed to **combine** (a holed `V+T` could have its holes filled by another
tile), and we did not search that. So this is strong evidence, not a theorem.

But taken at face value it says the three-segment ansatz was never a choice.
It is the only one available — which would explain why Kohonen *suggested* four
segments and never produced one.

## Honest bottom line

Still 0.289115646. Our best automated design: 0.2824. We did not beat it, and
after this round I believe the reason is structural rather than a lack of
search: the ansatz is forced, its ceiling is unattainable, and the record sits
at a very deep optimum inside it.
