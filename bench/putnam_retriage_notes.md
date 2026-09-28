# PutnamBench re-triage — `real-algebraic` tier (2026-09-28)

Input: the 117 `real-algebraic` rows of `bench/putnam_retriage.tsv`. Three read-only agents
rated each by statement only (no Lean): cost 1 (<30 lines) … 5 (major missing theory).
Estimates, not results — the kernel decides. Solved this session are struck out.

## Cheapest (cost 1–2), with the plan that looked right — ALL DONE 2026-09-28
22/22 fell (21 real + 1991_a6 VACUOUS, counted separately); most passed in 1–3 kernel rounds.
Also solved the same day, from the older NEXT list: 2000_b5.
- ~~2012_a1~~ ~~1982_a5~~ ~~1983_b4~~ ~~2008_b4~~ ~~1970_b3~~ ~~1968_b6~~ (all solved 2026-09-28)
- ~~1991_a6~~ ✅ — **VACUOUS** (`→` looser than `∧` in `hA`; the set is infinite, `encard = ⊤`
  contradicts `A n : ℕ`). Label as vacuous if counted.
- ~~1986_b6~~ ✅ — `fromBlocks A B C D * fromBlocks Dᵀ (-Bᵀ) (-Cᵀ) Aᵀ = 1`, `Matrix.mul_eq_one_comm`,
  read off block (2,2).
- ~~1987_b3~~ ✅ — rational parametrization r = y/(1−x); `field_simp; ring` both ways.
- ~~1972_a1~~ ✅ — `Nat.choose_succ_right_eq` ×3 → (n−2r−2)² = n+2 = (n−2r−4)², impossible.
- ~~1994_a4~~ ✅ — det(A+tB) quadratic in t, ±1 at t=0..4 → 32 sign cases by omega.
- ~~1978_b6~~ ✅ — x_i = A_i/i ∈ [0,m], induct on n, `nlinarith` per step.
- ~~1965_a6~~ ✅ — rpow algebra with n = m/(m−1).
- ~~2000_b1~~ ✅ — double count over 7 nonzero (r,s,t) ∈ {0,1}³; 4 of 7 odd (`decide` in ZMod 2).
- ~~2004_a3~~ ✅ — `det_fin_two`; induction on u n·u(n+1) = n!, u(n+2) = (n+1)·u n.
- ~~1978_b4~~ ✅ — Vieta-jumping sequence 1,1,1,2,4,13,85,…; invariant by `linear_combination`.
- ~~1999_b6~~ ✅ — `Nat.find` least n with gcd(s,n) > 1 ∀ s; prime p ∣ s; minimality at n/p.
- ~~1988_b6~~ ✅ — t triangular ⇔ 8t+1 odd square; family ((2k+1)², k(k+1)/2) injective ⇒ encard ⊤.
- ~~2001_b1~~ ✅ — split grid sum; per-row/col counts n/2.
- ~~2003_b4~~ ✅ — Vieta by evaluating at 5 points; rational-closure chain.
- ~~1969_b6~~ ✅ — P·P = 9P; det(BA) = 81 via Cauchy–Binet `linear_combination`; BA = 9I.
- ~~2005_a4~~ ✅ — ‖Σ chosen rows‖² = a·n vs ≥ b·a².

## Cost 3 (next wave)
✅ done 2026-09-28 (25): 1993_b5, 2000_a6, 1994_b6, 2002_b5, 1968_a4, 1977_b5, 2003_a2, 2015_a6,
1985_b6, 2010_b6, 2018_b6, 2019_b3, 1967_b4, 1971_a3, 2000_a5, 2004_b1, 1973_b3, 1994_b5,
1975_b6, 2006_b2, 1977_b6, 1978_a2, 1967_b5, 1987_b2 (+ 1973_b2 from the older NEXT list).
Remaining: 2007_b5 (coefficients of ∏(n−j−k·m) in m), 2003_a4 (case split on disc(Q); needs
|a| ≤ |A| from large x), 1970_a2 (ε-δ), 2012_b5 (sSup; needs ℝ ≃ ℝ×ℝ indexing), 1966_b4
(Mirsky), 1973_b1, 1998_a5, 2002_a2 (hemisphere; cross product + encard bookkeeping),
1987_b6, 1964_b6 (needs isometry surjectivity), 1973_a6, 2017_b1, 2023_a4, 1996_a4.
Also from the older NEXT list: 2017_a2, 2005_a1, 2025_a1.

## Statement findings
- 1991_a6 VACUOUS (above).
- 2013_a3 misformalized (`a i / (1 - x^(i+1))` vs a_i/(1−x)^{i+1}) but still TRUE; needs IVT + tsum.
- 2012_b5 weaker than original (`sSup` instead of attained max) — still true.
- 2004_a4 misformalized-weaker (x bound before ∃) — still needs the polarization identity.
- 1967_b1 true only with the convexity/orientation hypothesis (numerically checked).
- Not actually algebraic: 1971_a6, 1962_b5, 1999_a2, 2014_b6, 2013_a3, 1979_a5, 1962_b3, 2005_b6.
