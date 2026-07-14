# discovery/ — evolutionary program search for open constructive problems

The Lean kernel proves things we already believe. This is the other half: a
loop aimed at things nobody has established yet.

## Why this shape

The only method that has produced *genuinely new* mathematics from an LLM is
propose-and-evaluate over **programs**: FunSearch (Nature 2023) improved the
cap-set lower bound in dimension 8; AlphaEvolve (2025) improved bounds on
matrix multiplication, kissing numbers, and the Erdős minimum-overlap constant.
Both work exactly the way nanoprover already works — *the agent proposes, the
kernel disposes* — with a scoring program in place of the kernel.

Two consequences fix the design:

**Evolve programs, not objects.** A 500-element set is 500 arbitrary numbers; an
LLM cannot reason toward it and a hill-climber gets lost in it. A *program* that
builds the set is short and carries the IDEA, so it can be mutated by reasoning
("what if the sieve ran the other way?") instead of by coin-flips.

**The target must be constructive.** A witness has to be checkable in finite
time. "Here is a set achieving X" can be verified; "for all n, P(n)" cannot.
Open *universal* conjectures are the worst possible fit for this architecture —
the repo's own Collatz campaign is the proof: the outer loop proposed a lemma
that would have settled the conjecture, and the kernel correctly rejected it.

## What is different here from FunSearch

FunSearch fires millions of cheap LLM samples through a weak mutation operator.
This project is keyless: the mutation operator is a *session LLM*, so we get
tens of proposals, not millions. Diversity therefore cannot be bought with
volume — it is bought with **lenses**. Each proposal attacks from a different
intellectual tradition (physics, chemistry, biology, probability, algebra,
geometry, algorithm design, adversarial), because those traditions *fail
differently* and their errors do not correlate.

## Calibration — read this before trusting any result

Pointed at `capset6` (cap sets in F_3^6), where the true maximum is a **known
theorem**: 112 (Potechin 2008).

| lens | idea | score | time |
|---|---|---|---|
| seed | product of the trivial 2-cap, 2^6 | 64 | 0s |
| algorithmic | randomised greedy + plateau-walk local search | 84 | 36s |
| **algebra** | **caps multiply: cap(5) x cap(1)** | **90** | **8s** |

Two findings, both load-bearing:

1. **Our laptop-scale search is mediocre.** 84 against a known optimum of 112.
   So we must not expect to beat world records by *searching harder* on
   well-studied problems. The idea has to do the work.
2. **Structure beat search, and by a mile** — 90 in 8 seconds versus 84 in 36.
   Extremal records are overwhelmingly held by algebraic constructions, and
   this reproduces that in miniature. It is the strongest argument for the
   multi-lens design: the winning lens was not the one that looked like
   "optimisation".

A tool whose scales have not been checked against a known weight is not an
instrument, it is a rumour.

## Usage

```bash
python engine.py init   PROBLEM              # score the seed construction
python engine.py prompt PROBLEM --lens physics   # emit a proposal prompt
python engine.py ingest PROBLEM cand.py --lens algebra --note "the idea"
python engine.py status PROBLEM              # population, best, per-lens
python engine.py verify PROBLEM              # INDEPENDENT re-check of the champion
```

`verify` re-runs the champion's program from scratch, checks the score is
reproducible (an unpinned random seed is a lie waiting to happen), and then
re-validates the object with a separate, deliberately naive routine. If the
fast evaluator and the slow one ever disagree, the fast one is wrong and the
record is not a record.
