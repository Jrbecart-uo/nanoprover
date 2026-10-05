# Erdős–Straus (Erdős #242): hypothesis log

Loop: generate executable hypotheses → test on growing families → literature filter → Lean for survivors.
Target statement: formal-conjectures `Erdos242.erdos_242` (distinct `x < y < z`), copied as `ES` in `ES24.lean`.
Context (2026-10-05): open; verified to 10^18; very active arXiv area (many 2025–26 "near proofs"). Mordell's hard
classes mod 840 are all ≡ 1 (mod 24). Erdos242 forum lists one proof claim.

## Kernel-checked (ES24.lean, clean axioms)
- `es_of_not_one_mod_24`: ES n for n > 2, n ≢ 1 (mod 24), from five explicit identities.
- `es_mul` + `es_of_prime_factor`: ES is closed under multiples, so ES holds unless every prime factor of n is ≡ 1 (mod 24).
- `es_of_cert`: any certificate (a, d) with 4x = n + a, d | (nx)², d < nx, a | nx + d, a | nx + (nx)²/d gives ES n.
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
