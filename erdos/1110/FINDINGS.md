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

## 2026-09-29 (later session): quenched vs annealed rates — why (9,2) and (5,3) are out of reach of finite certificates
Encoding rate = exponent range used per target digit; positive density needs typical targets encodable at
rate < mu = log_R B (the certificate proves exactly this with a finite-window online policy). Three rates:
* **annealed** (first moment, root of (1+r)H(1/(1+r)) = log2 B): 0.29382 for EVERY (p,2) (kappa > 1 <=> p <= 10,
  exactly Yu-Chen's threshold); (5,3): 0.64179 in base 3, 1.36213 in base 5; (9,2) in base 9: 2.82351.
* **quenched** (offline optimum for a fixed typical target). Constructive upper bounds from a large-population
  beam (`nbrw.c`, keep the N cheapest partial staircases; every traced solution re-verified with Python
  big-int arithmetic; beam = exact optimum on 12 random 18-bit targets); estimates from the exact mean over ALL
  k-digit targets (`hmean.c`, min-plus transfer operator; E[H_k]/k is itself an upper bound by subadditivity).
* **online** with a W-digit look-ahead (what a finite-state certificate can certify): `rollout.c` (optimal
  W-bit plan, first step committed; ~0.01-0.02 worse than the previous VI at equal window).

| pair (base) | mu | annealed | quenched <= (beam N=1e6, L=4000) | exact increment E[H_k]-E[H_{k-1}] | online (rollout) |
|---|---|---|---|---|---|
| (5,2) b2 | 0.43068 | 0.29382 | 0.3588 | 0.349 (flat from k=15 on) | — (DLLZ: 12-bit block suffices) |
| (7,2) b2 | 0.35621 | 0.29382 | 0.3412 (0.958 mu) | 0.3395 at k=26, still falling | W=21/25/29: 1.038/1.025/1.014 mu (VI W=33: 0.9965 = our certificate) |
| (9,2) b2 | 0.31546 | 0.29382 | **0.3117, 0.3133, 0.3143** (0.988/0.993/0.996 mu, 3 seeds; final cost/L 0.3128-0.3135) | 0.3295 at k=26, still falling | W=13/17/21/25/29/31: 1.225/1.188/1.161/1.140/1.124/1.117 mu |
| (5,3) b3 | 0.68261 | 0.64179 | N=1e6: 0.977, 0.979 mu (2 seeds; N=3e5: 0.976; N=1e4: 0.992-0.996) | 0.722 at k=17, still falling | (VI W<=13 trits: 1.15-1.20) |
| (5,3) b5 | 1.46497 | 1.36213 | N=1e5: 0.970, 0.992 mu (2 seeds; N=1e4: 0.973-0.980; single targets vary by ~2%) | — | (VI s=3: 1.21) |

Conclusions.
1. **Strong disorder**: the quenched rate exceeds the annealed one by 7-22%, and the gap depends on the
   arithmetic of p ((5,2) has the largest). The first-moment heuristic (kappa > 1) badly overstates margins.
2. **(9,2) and (5,3) look quenched-SUPERcritical**: random 4000-bit targets are encodable below mu
   (constructively, both seeds), so positive density of representables is plausible; the flat ~6% / ~4% local
   densities fit a near-critical supercritical branching process (survival probability ~ 2 eps / sigma^2),
   not a subcritical one. Margins are thin: ~1-4% for (9,2), ~1-3% for (5,3) (either orientation).
3. **Finite certificates cannot reach them**: the online rate approaches the offline one only like
   W^(-0.6..-0.7) ((9,2): 1.117 mu at W=31); crossing mu would need a look-ahead of several hundred bits
   (2^300 states). (5,2) has short memory (exact increments converge by k~15), (7,2) moderate, (9,2) long.
4. A proof needs a genuinely non-causal (offline) argument, e.g. a truncated second moment for the number
   of cheap staircases; the plain second moment diverges exponentially because of the strong disorder.
5. Side note: for (9,2), n = 3, 6 (mod 9) is never representable (at most one summand has a = 0, and 2^b is a
   unit mod 9) and 9m is representable iff m is, so non-representables have density >= 1/4.

## 2026-09-30: reachable sets, the carry mechanism, and an EXACT integer reformulation ((9,2), (5,3))
Goal: think past single-path online certificates.  Tools: `rolloutg.c` (online rollout, any base, dead residues),
`viterbi.c` (forward reachable set on W-bit windows, "window model"), `exactset.c`/`exactsp.c` (exact integer
process below), `check_ek.py` (validation).
1. **Other orientations do not help online**: rollout ratio at ~25-29 bits of look-ahead: (9,2) base 9 W=7
   digits 1.178; (5,3) base 5 W=11 1.132, base 3 W=18 1.124 (same slow convergence as base 2).
2. **What the offline optimum does differently** (beam N=1e5, 3000 bits): same mean increment as online
   (1.247 vs 1.244 per term; d=1 in 80%, d=2 in 16%) but longer gaps between terms (3.98 vs 3.46 bits).
3. **Existence is a FORWARD question**: a bounded-excess staircase exists iff the forward reachable set never
   empties (Koenig); no look-ahead needed.  In the "window model" (all candidates merged by their W-bit
   window and fed the same fresh bit, equivalent to truncating each term's 2-adic value to W bits) the
   reachable-set rate is supercritical already at W=12 and reaches 0.964 mu at W=20 for (9,2).
4. **The window model is universal but fake**: at W=16 its rate is 0.306-0.307 per bit for p = 5, 7, 9, 11, 13,
   25 (0.312 for p=3), close to the counting rate 0.294, i.e. it only sees 2-adic combinatorics.  The true
   process adds a p-dependent **carry penalty**: (5,2) ~0.35, (7,2) ~0.333, (9,2) ~0.312.  In the true process,
   one-candidate-per-window selection gives 0.991-0.997 mu at 2^14 candidates (seeds), 0.994 at 2^16.
5. **Exact integer reformulation (new).**  Fix a reference line of rate rho < mu (levels G_ref(t) = floor(rho t))
   and let z_ref be the (uniform) target; its bits r_t are iid.  Every candidate staircase has normalized
   residual  z = R^e z_ref + k  with e = excess over the line (>= 0 after padding) and k an INTEGER, bounded
   by C(rho) R^e (geometric decay since rho < mu; C ~ 75 at rho=5/16, ~750 at rho=0.315).  Transitions:
     (r+k) even: e' = e - lam, pad if negative (k' = (r + R k)/2), else k' = (R^e' r + k)/2;
     (r+k) odd, increment d: e' = e + d - lam, k' = (R^e' r + R^d k - 1)/2.
   Equal (e,k) means identical candidates, so merging is lossless: the offline problem is EXACTLY a branching
   process on integer pairs in an iid random environment (one bit per step).  The "carries" are the R^e twist
   between candidates at different excess levels (the window model ignores it).  `check_ek.py`: transitions
   agree with direct big-integer 2-adic arithmetic on 60,000 steps (40 paths, random choices, padding), 0 errors.
6. **Exact numerics for (9,2)**: rho = 5/16 = 0.9906 mu: the front (min excess) drifts up, extinct with caps
   D=4,6,8.  rho = 0.315 = 0.9985 mu, D=8-9: 3 of 5 targets survive with the front at 0-2 and the population
   growing (27K -> 954K over 2000 steps); 2 die in the early phase.  So the offline rate is in (0.3125, 0.315)
   and the process is barely supercritical: survival probability small but positive, matching the flat ~6%
   density.  **Pruning to candidates within 1, 2 or 3 levels of the front kills every run**: the offline
   advantage lives in a deep population, so no small "front configuration" certificate exists.
7. **Status**: positive density for (9,2) is strongly supported (exact model, not heuristics), but a proof
   needs front tightness for an explicit near-critical branching process in random environment with a deep
   relevant population.  Out of reach of finite-state certificates (single-path needs ~300 bits of look-ahead;
   set-based needs >= 4 levels of depth with |k| ~ C 9^e).  The exact reformulation is the clean target for
   a probabilistic proof.
