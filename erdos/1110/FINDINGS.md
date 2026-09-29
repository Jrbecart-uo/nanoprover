# Erdős #1110 — density clause for (p,q) = (7,2): attack log (2026-09-28)

**Status: candidate proof of positive lower density for (7,2) — see `PROOF_SKETCH.md` (computer-verified certificate, review pending).** Earlier sections below record the path. Status re-checked 2026-09-28: the only density claim is Ding–Li–Liu–Zhang
(2026-08-24, (5,2), positive lower density of representables). Pairs still open for density:
(7,2), (9,2), (4,3), (5,3).

## Empirics (`rep.c`, exact up to 2^27)
Fraction representable: (7,2) ≈ 0.22 and flat from 2^20 to 2^27; (4,3) ≈ 0.15 and still drifting down.

## A clean sufficient criterion (our reconstruction of the (5,2) method)
Chain = set {(α_i, γ_i)} strictly increasing in both coordinates. For every residue r mod 2^s pick a chain
with α < s and Σ 2^α 7^(−γ) ≡ r (mod 2^s); height h(r) = max γ + 1.
**If the average height H̄ < s·log_7 2 (≈ 0.3562 s), the representables for (7,2) have positive lower density.**
Proof sketch: stack blocks (2-exponents in [st, st+s), 7-exponent windows G_{t+1} = max(G_t + h(r_t), ⌈(t+1)λ⌉),
H̄ < λ < s log_7 2, A = ⌈Nλ⌉ + c). The map word → n is injective (n·7^(−A) mod 2^{sN} decodes the word
triangularly), n ≤ K·2^{sN} (geometric decay since G_t ≥ tλ), and admissibility (G_N ≤ A) holds for a
fixed positive fraction of words (Lindley recursion + Chernoff union bound over suffixes).
Variable-length refinement (prefix tree, `tree.c`): needs E[h − μ·ℓ] < 0 over the leaves.

**Validation:** for (5,2), s = 12 gives H̄ = 4.930 < 5.168 with max height 8 — exactly the certificate
shape Ding et al. report (P = 2^12, γ ≤ 7, average height < 5).

## (7,2) numbers
| s (flat) | H̄ | bound 0.3562 s | gap |
|---|---|---|---|
| 12 | 4.920 | 4.274 | 0.645 |
| 20 | 7.737 | 7.124 | 0.613 |
| 24 | 9.107 | 8.549 | 0.558 |
| 28 | 10.466 | 9.974 | 0.492 |
Optimal variable-length tree (ratio E[h]/E[ℓ], need < 0.35621): D=16 0.3879, D=20 0.3804, D=24 0.3735,
D=26 0.3705. Fit ≈ 0.343 + 0.72/D ⇒ crossing near D ≈ 50 (infeasible as full bitsets; the tree's deep
tail is fat: ~4% of mass reaches depth 23, nodes grow ~1.8×/level).
Beam search on 300-bit random targets (`beam.py`) achieves ≈ 0.339 γ/bit < 0.3562: the method should
work in principle; the obstacle is certificate size (boundary losses), not the mathematics.

## Other pairs
- 7-adic orientation for (7,2) is impossible: one term per 7-adic position, and 2^(−β) mod 7 ∈ {1,2,4}
  (2 is not a primitive root mod 7), so half the residues are unreachable.
- (4,3): both orientations hit the known obstruction (3-adic: 4^(−g) ≡ 1 mod 3; 4-adic: 3^(−β) ≡ ±1 mod 4),
  so the scheme must be restricted to the unobstructed classes.
- (9,2), (5,3): heuristic exponents 1.045 / 1.034 — margins thinner than (7,2).

## Next ideas (not tried)
Lookahead/Markov certificates that choose among chains of a block by their carry into the next block
(reduces the boundary loss that dominates the finite-size penalty); certificates as explicit leaf lists
checked by an independent verifier.

## 2026-09-28 (later): recheck + other pairs
- Recheck of (7,2): `verify.c` re-run → GNUM = 8385274094 (PASS); new independent full-state checker `verify2.c`
  (different chain enumeration, inverse, arithmetic) → identical GNUM and argmax over all 2^22 states. Write-up with a
  simplified probabilistic step (exponential potential instead of Azuma/coupling): `NOTE.md`.
- (9,2), (5,3) with the same two-block look-ahead (`gvi.c`, general base; exact VI lower bracket / threshold):
  (7,2) calib 1.017 (s=8), 1.010 (s=9), 0.9965 (s=11); (9,2) 1.145 (s=8), 1.131 (s=9);
  (5,3) base 3: 1.155 (s=5), 1.136 (s=6); base 5: 1.212 (s=3). Beam on 300-bit targets: (9,2) ≈ 0.319 vs μ = 0.3155.
  Extrapolated need: blocks ~2^19 / 3^13 — out of reach for this state space. NOT pursued further.

## 2026-09-29: densities at large scale, (4,3) attack, new tools
**Exact representability test** `repdfs.c`: n is representable iff, after stripping q's, one can subtract p^a with
a strictly decreasing (and q | remainder) down to exactly 0 (the smallest-q-power term carries the largest
p-power). Matches brute force for all n < 2^20 for (9,2),(7,2),(5,3),(4,3),(5,2),(3,2) (0 mismatches; (3,2): all).
Monte Carlo (local density of n in [2^(L-1),2^L), 20k-40k samples, +-0.002-0.006):
| L | (5,2) | (7,2) | (4,3) | (9,2) | (5,3) |
|---|---|---|---|---|---|
| 32 | 0.975 | 0.245 | 0.138 | 0.070 | 0.052 |
| 48 | 0.9994 | 0.258 | 0.152 | 0.0605 | 0.043 |
| 56 | | | | 0.0614 | |
| 64 | | 0.329 | 0.180 | 0.0605 | 0.040 |
| 80 | | | | | 0.043 |
Enumeration (`rep2.c`, exact cumulative to 2^32..2^34): (7,2) flat ~0.22, (4,3) ~0.15, (9,2) 0.137 -> 0.073,
(5,3) 0.106 -> 0.055 over 2^17..2^32 (the early decline flattens at larger L). Conjecture suggested by the data:
non-representables have density 0 when the antichain-counting exponent exceeds 1 and there is no congruence
obstruction ((5,2) is already at 99.94%); (4,3) is capped by the mod-3 / mod-4 obstructions.
**2-adic shadow** (`shadow.c`): |O_A mod 2^k| / 2^(k-1) at the critical top exponent stays ~constant
(0.12-0.26 for (9,2) up to k=30) -> no density-zero proof from 2-adic information alone.
**Certificate search, general form** (`gvik.c`, `gvid.c`): state = D digits, blocks of s digits, fresh block
enters at the top (window W = D+s); dead residues (no chain) and the viable set W (closed under all fresh
blocks and under x -> Qx, needed for padded steps). Findings: ratio depends mainly on the window, and finer
blocks are better at equal window. (4,3) base 4, s=2: W=12 1.0278, 13 1.0180, 14 1.0096, 15 1.0024 -> W=16
expected ~0.996 (run in progress). (9,2) s=1: W=13..21 -> 1.21..1.14; (5,3) s=1: 1.20..1.15 (W=9..13 trits):
out of reach. (4,3) viable set = exactly 2/3 of states (stuck states: (4^(D-s)-1)/3 of them).
`verifyd.c`: independent exact checker for such certificates (reproduces gvid's ghat at W=12).
