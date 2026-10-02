# Clean-room certificate checker — specification

Goal: an independently written checker (Rust) for the look-ahead potential certificates of Erdős #1110.
It must be written from THIS spec only. Do not read any `*.c`, `*.py`, `*.lean`, `*.log`, `*.out`, `*.txt`
or `NOTE*.md` / `FINDINGS*.md` file under `erdos/1110/` (they contain another implementation and the expected
results; the point is a blind, independent reimplementation).

## Parameters
Coprime integers `B ≥ 2` (digit base) and `Q ≥ 2` (other base); block length `s ≥ 1`; state length `D`;
height bound `H`; `SLACK ≥ 0`. Write `P = B^s`, `M = B^D` (number of states), `M' = B^(D+s)`.
All arithmetic below is exact integer arithmetic (use u128 where products can overflow u64).

## Chains
A chain is a pair (α-set, γ-set) with α-set ⊆ {0,…,s−1}, γ-set ⊆ {0,…,H−1}, equal sizes k ≥ 0; sort both
increasingly and pair them: (α_1,γ_1),…,(α_k,γ_k). Its value is
`v = Σ_i B^{α_i} · Q^{−γ_i} mod M'` (Q^{−1} is the inverse of Q modulo M'), and its height is
`h = γ_k + 1` (h = 0 for the empty chain, whose value is 0). Its class is `c = v mod P`.
**Kept chains:** for each class c let `hmin(c)` = the minimum height over chains of class c; keep the chains of
class c with `h ≤ hmin(c) + SLACK`. A class with no chain at all is *uncovered*.

## Transitions
States are `x ∈ {0,…,M−1}` (D base-B digits). Fresh blocks are `u ∈ {0,…,P−1}`.
For a state x, a fresh block u and a kept chain (v,h) of class `x mod P`:
`z = x + M·u` (this is < M'), `r = (z − v) mod M'` (necessarily divisible by P — assert it),
`next = Q^h · (r / P) mod M`.

## Viable set W
Start with W = all states x whose class `x mod P` is covered. Repeatedly remove from W every x such that
(i) for some u ∈ [0,P), NO kept chain of class `x mod P` gives `next ∈ W`, or
(ii) `(Q·x) mod M ∉ W`.
Iterate until nothing is removed (greatest fixed point). Report |W|. W must be nonempty.

## Potential and drift
The potential file is `M` little-endian float32 values in a *transposed* layout: the value for state x is at
index `(x mod B^(D−s)) · P + ⌊x / B^(D−s)⌋`. Define the integer potential
`Vi(x) = round_half_away_from_zero(V(x) · 2^20)` (V(x)·2^20 is exact in f64). Reject (count as bad) any
x ∈ W with non-finite V or |V(x)| ≥ 1e5.
For every x ∈ W compute
`d(x) = Σ_{u=0}^{P−1} min over kept chains (v,h) of class x mod P with next ∈ W of [ h·2^20 + Vi(next) ]  −  P·Vi(x)`
(by construction of W the min is over a nonempty set). Report `GNUM = max_{x∈W} d(x)`, the argmax state (any
one), the number of bad states, and `g = GNUM / (P · 2^20)` as an exact rational and as a decimal.

## Verdict
Given a threshold rational `λ = a/b` (positive integers), report exactly (integers, no floats) whether
`GNUM · b < a · P · 2^20` (i.e. g < λ). Also report, exactly with big integers, whether `Q^a < B^(s·b)` and
whether `B^(s·b) < Q^a` (which side of the density threshold λ is on).

## Instances to run (tables are xz-compressed; decompress to a scratch dir, verify SHA-256 first)
| name | B | Q | s | D | H | SLACK | λ = a/b | table (relative to `erdos/1110/`) | SHA-256 of uncompressed |
|---|---|---|---|---|---|---|---|---|---|
| (4,3) | 4 | 3 | 2 | 14 | 18 | 12 | 58/23 | `data_43/V43_final.bin.xz` | (sha of the .xz is in `data_43/V43_final.bin.xz.sha256`) |
| (9,2) | 2 | 9 | 1 | 26 | 12 | 7 | 13/37 | `data_pow/V92_d26.bin.xz` | `df36042caada6ed6d20c255dae4b8f04de063784fb547318ce9b92d4b7f1db68` |
| (5,3) | 3 | 5 | 1 | 17 | 12 | 7 | 35/46 | `data_pow/V53_d17.bin.xz` | `0906e8b2dd421a0a8e0a94fabde3060fecf91960a1dde13dda5b910a4ffead82` |

Machine: 8 cores, ~16 GB free RAM; a single Bash call is capped at 10 minutes, so run long jobs detached
(`nohup setsid … &`) and poll. At most one large instance at a time.

## Self-tests (required before the real runs)
1. Brute-force cross-check of the transition on tiny parameters (e.g. B=4,Q=3,s=1,D=3,H=4 and B=2,Q=9,s=1,D=5,H=4):
   for random states/blocks/chains, verify with big integers that `next` equals the low D digits of
   `Q^h · (Y − Σ_i B^{α_i} Q^{−γ_i} … )/P`-style direct computation of your own design (derive it yourself from
   the definitions: the window z is the low D+s digits of an integer Y; subtracting the chain value and dividing
   by P then multiplying by Q^h must give an integer whose low D digits are `next`; check this on Y with random
   high digits, so the high digits provably do not matter).
2. Check the chain count per class and `hmin` on a tiny case by an independent enumeration.
3. Check that a potential V ≡ 0 gives `GNUM = Σ_u min h·2^20` structure-consistent results on a tiny case.

## Output
Put the code in `erdos/1110/indep_rs/` (Cargo project) and the results in `erdos/1110/indep_rs/RESULTS.md`:
for each instance: |W|, bad, GNUM, argmax, g, verdict booleans, runtime, and the SHA-256 you verified.
