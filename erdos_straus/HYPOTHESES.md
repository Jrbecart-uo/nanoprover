# Erdős–Straus (Erdős #242): hypothesis log

Loop: generate executable hypotheses → test on growing families → literature filter → Lean for survivors.
Target statement: formal-conjectures `Erdos242.erdos_242` (distinct `x < y < z`), copied as `ES` in `ES24.lean`.
Context (2026-10-05): open; verified to 10^18; very active arXiv area (many 2025–26 "near proofs"). Mordell's hard
classes mod 840 are all ≡ 1 (mod 24). Erdos242 forum lists one proof claim.

## Kernel-checked (ES24.lean, clean axioms)
- `es_of_not_one_mod_24`: ES n for n > 2, n ≢ 1 (mod 24), from five explicit identities.
- `es_mul` + `es_of_prime_factor`: ES is closed under multiples, so ES holds unless every prime factor of n is ≡ 1 (mod 24).
- `es_of_cert`: any certificate (a, d) with 4x = n + a, d | (nx)², d < nx, a | nx + d, a | nx + (nx)²/d gives ES n.
- `es_mordell` (**Mordell's theorem**): ES n for every n > 2 outside n ≡ 1, 121, 169, 289, 361, 529 (mod 840), via five more
  identities (mod 7: n ≡ 3, 5, 6; mod 15: n ≡ 7, 13) plus scaling from ES 5 and ES 7. Matches R3-6: least non-residue 5 or 7 ⇒ easy.
- `es_of_divisor_two_mod_three`: n ≡ 1 (mod 12) and (n+3)/4 having a divisor ≡ 2 (mod 3) give ES n. This is a divisor
  criterion, not a congruence criterion, so it reaches inside the hard class.

## Round 1 (primes p ≡ 1 mod 24 below 10^8: 719 781 primes; `es_scan.c`, brute-force cross-checked on the first 40)
a_min = the smallest a = 4x − p that works. Distribution: 3 (59.8%), 7 (32.7%), 11 (4.9%), 15, 19, 23, … The maximum
is 107, at p = 8 803 369.

| # | hypothesis | verdict |
|---|---|---|
| H1 | a_min = 3 always | dead (p = 73) |
| H2 | a_min ≤ 50 | dead (p = 118 801: 59) |
| H3 | a_min ≤ 2 ln p | dead (p = 1201: 23) |
| H4 | a_min ≤ (ln p)² | **survives** to 10^8 (would imply ES for these primes; unprovable now) |
| H5 | a_min prime | dead (p = 2689: 15) |
| H6 | the witness at a_min avoids p (e = 0) | dead (p = 51 769) |
| H7 | ≥ 2 working a ≤ 400 | survives |
| H8 | a_min = 3 ⇔ (p+3)/4 has a prime factor ≡ 2 (mod 3) | **survives**; the "⇐" direction is proved in Lean for all n ≡ 1 (mod 12) |
| H9 | a_min ≤ 4·(least QNR) − 1 | dead (p = 118 801) |
| H10 | a_min ≤ least prime q ≡ 3 (mod 4) with (p/q) = −1 | dead (p = 1201) |
| H11 | a_min ≤ 7 or p+1 has a prime factor ≡ 3 (mod 4) | dead (p = 1129) |
| H12 | some working a ≤ 400 is prime | dead (p = 31 081) |
| H13 | a_min ≠ 27 | dead (p = 94 441) |
| H14 | a_min ≠ 15 | dead (p = 2689) |
| H15 | a_min ≤ 6 √(ln p) ln ln p | dead (p = 118 801) |
| H16 | p a QNR mod 7 ⇒ a_min ≤ 7 | survives (classical Mordell class, x' = 2) |

## Round 2 (wilder; first 6000 primes p ≡ 1 mod 24, `hyp_round2.py`, `hyp_w11.py`)
| # | hypothesis | verdict |
|---|---|---|
| W1 | a Type I solution (only x divisible by p) with x' ≤ 60 | dead (p = 167 521) |
| W2 | a Type II solution (p divides y and z) with y', z' < 40 | dead (p = 241) |
| W3 | a_min ≥ 23 ⇒ p is a QR mod 5, 7, 11, 13 | dead (p = 1201) |
| W4 | a_min ≤ the first a with (p+a)/4 composite | dead (p = 193) |
| W5 | #working a ≤ 400 is ≥ ln p | dead (p = 73) |
| W6 | (a = 3 fails) a = 7 works ⇔ (p+7)/4 or p has a prime factor that is a QNR mod 7 | **survives** (exact a = 7 criterion) |
| W7 | naive mod-11 analog of W6 | dead (p = 1201) |
| W8 | a_min ≤ 3 + 4·#{prime factors of (p+3)/4 that are ≡ 1 mod 3} | dead (p = 1129) |
| W9 | (p+3)/4 prime ⇒ a_min ≤ 7 | dead (p = 1129) |
| W10 | a_min ≤ 7 unless p is a QR mod 7 | survives (= classical class) |
| W11 | a works ⇔ −1 ∈ ⟨prime factors of p·(p+a)/4⟩ ≤ (Z/a)* | **half**: "⇒" never fails (37 500 pairs, a ≤ 99); "⇐" fails 8 088 times because divisors of (px)² have bounded exponents. A necessary condition: an obstruction tool, not an existence tool |

Takeaways: the hard primes are those where, for every small a, the prime factors of p·(p+a)/4 sit in a subgroup avoiding −1
(mod a), or exponent caps block the needed residue. Proving ES therefore needs a sieve-type statement: for some a ≤ A(p)
the factorisation of (p+a)/4 is "rich enough" mod a. That is the open core (cf. arXiv 2608.24035, sieve dimension for
n ≡ 1 mod 24). H4 (a_min ≤ (ln p)²) is the cleanest empirical form of it.

## Round 3 (growth and structure; `es_scan … records` to 10^9, `model_r3.py`, `records_r3.py`)
Data: 6.35 M primes p ≡ 1 (mod 24) below 10^9. No new record after 8.8·10^6; the largest a_min is still 107 at
p = 8 803 369. Tail: a_min ≥ 63 for only 24 primes.

| # | hypothesis | verdict |
|---|---|---|
| R3-1 | P(a = 3 fails) ≈ 1.7/√(ln p) (integers built from primes in an index-2 subgroup thin out like (log)^{-1/2}) | **fits** 10^5…10^9: 1.69, 1.75, 1.73, 1.70, 1.67 |
| R3-2 | independent per-a failures predict the tail of a_min | **roughly**: within ~2×; the real tail is fatter (failures positively correlated) |
| R3-3 | max a_min below X grows like log X / log log X (model: each a fails with prob ~ c(log p)^{-1/2}) | consistent (records 59 → 107 → none up to 10^9) |
| R3-4 | a_min ≤ 7 ln p | survives to 10^9 (tight at the record: 107 ≤ 111.7) |
| R3-5 | records lie in Mordell's hard classes mod 840 | yes (169, 289, 361), as theory predicts |
| R3-6 | lqnr(p) ∈ {5, 7} ⇒ a_min ≤ 7 | **true on 540 313 primes**; it is the classical mod-5/mod-7 Mordell coverage |
| R3-7 | a_min rises with the least quadratic non-residue lqnr(p) | **strong**: mean a_min 4.1 (lqnr 5) → ~12 (lqnr ≥ 37); the champion has lqnr = 41 |
| R3-8 | a_min ≤ 5·lqnr(p) | **survives** to 10^8 (max ratio 4.54 at p = 118 801) and at the 10^9 record (107/41) |

Reading: the hard primes are those that look like squares modulo every small prime (large least non-residue).
R3-8 + GRH (lqnr ≤ 2 ln² p, Bach) would give a_min ≤ 10 ln² p, i.e. H4 up to the constant, and so Erdős–Straus for
all primes, conditionally on GRH and on R3-8. R3-8 is the missing link and is NOT proved; an unconditional
version would still need lqnr bounds far beyond Burgess. Known heuristics (Elsholtz–Tao) are consistent with this.
Records anatomy: of the a < a_min at each record prime, ~80% fail because −1 ∉ ⟨prime factors of p(p+a)/4⟩ mod a,
~20% because of exponent caps.
