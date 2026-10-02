import Mathlib

/-!
# nanoprover lemma library

Recurring pieces extracted from kernel-verified solved proofs
(`bench/solved_putnam/`, `bench/solved_imo/`). Every lemma here was distilled
from a proof that passed `#print axioms` with only the standard three.

Usage: the REPL daemon (`tools/repl.py`) loads this file at boot into a
`lemmas_env`; check attempts with `--lemmas` to have these in scope. For the
final self-contained artifact, inline whatever you used.

Provenance is noted on each lemma. Keep this file small and battle-tested:
a lemma enters only after carrying weight in ≥1 real solve.
-/

namespace Nanoprover

/-- Exponent congruence via Euler's totient: to prove `a^x ≡ a^y [MOD t]`
it suffices that `x ≡ y [MOD φ(t)]`, for `a` coprime to `t`.
The workhorse of tower/tetration arguments. (putnam_1997_b5) -/
lemma pow_exp_congr (a t : ℕ) (hco : Nat.Coprime a t) :
    ∀ x y : ℕ, x ≡ y [MOD t.totient] → a ^ x ≡ a ^ y [MOD t] := by
  have key : ∀ x y : ℕ, x ≤ y → x ≡ y [MOD t.totient] → a ^ x ≡ a ^ y [MOD t] := by
    intro x y hxy h
    obtain ⟨c, hc⟩ := (Nat.modEq_iff_dvd' hxy).mp h
    have hy : y = x + t.totient * c := by omega
    subst hy
    rw [pow_add, pow_mul]
    exact (calc a ^ x * (a ^ t.totient) ^ c
        ≡ a ^ x * 1 ^ c [MOD t] :=
          Nat.ModEq.mul_left _ ((Nat.ModEq.pow_totient hco).pow c)
      _ = a ^ x := by rw [one_pow, mul_one]).symm
  intro x y h
  rcases le_total x y with hxy | hxy
  · exact key x y hxy h
  · exact (key y x hxy h.symm).symm

/-- Split `m ≠ 0` as `p^s * t` with `p ∤ t`, plus the coprimality that CRT
arguments need. Instantiate with `p = 2` for even/odd splits. (putnam_1997_b5) -/
lemma exists_ordProj_split (p m : ℕ) (hp : Nat.Prime p) (hm : m ≠ 0) :
    ∃ s t, m = p ^ s * t ∧ ¬ p ∣ t ∧ Nat.Coprime (p ^ s) t :=
  have hnd : ¬ p ∣ ordCompl[p] m := Nat.not_dvd_ordCompl hp hm
  ⟨m.factorization p, ordCompl[p] m, (Nat.ordProj_mul_ordCompl_eq_self m p).symm,
   hnd, Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd)⟩

/-- Anything dividing `n` is coprime to anything dividing `n + 1`.
Kills the "divisors of `n` are units mod `k`" obligation when `k ∣ n + 1`.
(putnam_1969_b1) -/
lemma coprime_of_dvd_of_dvd_succ {d k n : ℕ} (hd : d ∣ n) (hk : k ∣ n + 1) :
    Nat.Coprime d k := by
  have h1 : Nat.gcd d k ∣ n := (Nat.gcd_dvd_left d k).trans hd
  have h2 : Nat.gcd d k ∣ n + 1 := (Nat.gcd_dvd_right d k).trans hk
  have h3 : Nat.gcd d k ∣ 1 := by simpa using Nat.dvd_sub h2 h1
  exact Nat.dvd_one.mp h3

/-- A divisor `d` of `n` and its partner `n / d` multiply to `n`, cast into
any `ZMod k`. The algebraic half of every divisor-pairing argument.
(putnam_1969_b1) -/
lemma cast_div_pair_mul (n d k : ℕ) (hd : d ∣ n) :
    ((d : ZMod k) * ((n / d : ℕ) : ZMod k)) = (n : ZMod k) := by
  have h : ((d * (n / d) : ℕ) : ZMod k) = (n : ZMod k) := by
    rw [Nat.mul_div_cancel' hd]
  push_cast at h
  exact h

/-- Divisor-pairing skeleton: if `f` is antisymmetric under `d ↦ n / d` and
the pairing has no fixed points (on the support of `f`), the divisor sum
vanishes. Works in any additive commutative group. (putnam_1969_b1) -/
lemma sum_divisors_eq_zero_of_pairing {M : Type*} [AddCommGroup M]
    (n : ℕ) (hn : n ≠ 0) (f : ℕ → M)
    (hpair : ∀ d ∈ n.divisors, f (n / d) = - f d)
    (hnofix : ∀ d ∈ n.divisors, n / d = d → f d = 0) :
    ∑ d ∈ n.divisors, f d = 0 := by
  have h2 : ∀ d ∈ n.divisors, f d + f (n / d) = 0 := by
    intro d hd; rw [hpair d hd]; exact add_neg_cancel (f d)
  refine Finset.sum_involution (fun d _ => n / d) h2 ?_ ?_ ?_
  · intro d hd hfd heq
    exact hfd (hnofix d hd heq)
  · intro d hd
    obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp hd
    exact Nat.mem_divisors.mpr ⟨⟨d, (Nat.div_mul_cancel hdvd).symm⟩, hn⟩
  · intro d hd
    obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp hd
    exact Nat.div_div_self hdvd hn

/-- `p² = 0` in `ZMod (p²)` — the cross-term killer. State once, feed to
`linear_combination`. (putnam_1991_b4) -/
lemma cast_sq_zero (p : ℕ) : ((p : ZMod (p ^ 2)) ^ 2) = 0 := by
  have h := ZMod.natCast_self (p ^ 2)
  push_cast at h
  exact h

/-- In `ZMod (p²)`, factors of the form `1 + p·a` multiply additively:
`(1 + pa)(1 + pb) = 1 + p(a+b)`. Turns Lucas-step products into sums.
(putnam_1991_b4) -/
lemma one_add_mul_cast_sq (p : ℕ) (a b : ZMod (p ^ 2)) :
    (1 + (p : ZMod (p ^ 2)) * a) * (1 + (p : ZMod (p ^ 2)) * b)
      = 1 + (p : ZMod (p ^ 2)) * (a + b) := by
  linear_combination (a * b) * cast_sq_zero p

/-- An odd non-square has an even divisor sum: pair `d ↔ b / d` (no fixed point, both odd) and sum in
`ZMod 2`. (putnam_1976_b6) -/
lemma even_sum_divisors_of_odd_not_sq {b : ℕ} (hb : Odd b) (hsq : ¬ IsSquare b) :
    Even (∑ d ∈ b.divisors, d) := by
  rw [← ZMod.natCast_eq_zero_iff_even, Nat.cast_sum]
  have hb0 : b ≠ 0 := by rintro rfl; exact hsq ⟨0, rfl⟩
  refine Finset.sum_involution (fun d _ => b / d) ?_ ?_ ?_ ?_
  · intro d hd
    have hdb : d ∣ b := Nat.dvd_of_mem_divisors hd
    have h1 : Odd d := hb.of_dvd_nat hdb
    have h2 : Odd (b / d) := hb.of_dvd_nat (Nat.div_dvd_of_dvd hdb)
    rw [ZMod.natCast_eq_one_iff_odd.mpr h1, ZMod.natCast_eq_one_iff_odd.mpr h2]
    decide
  · intro d hd _ heq
    have hdb : d ∣ b := Nat.dvd_of_mem_divisors hd
    apply hsq
    refine ⟨d, ?_⟩
    have := Nat.div_mul_cancel hdb
    rw [heq] at this
    exact this.symm
  · intro d hd
    exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hd), hb0⟩
  · intro d hd
    exact Nat.div_div_self (Nat.dvd_of_mem_divisors hd) hb0

/-- Walks in a graph properly 2-coloured by `side` change colour at every step, so the endpoints have the same
colour iff the length is even. (putnam_1965_b5) -/
lemma walk_parity {K : Type*} {G : SimpleGraph K} (side : K → Bool)
    (hG : ∀ x y, G.Adj x y → side x ≠ side y) :
    ∀ {a b : K} (w : G.Walk a b), (side a = side b ↔ Even w.length) := by
  intro a b w
  induction w with
  | nil => simp
  | @cons x y z h p ih =>
    have hxy := hG x y h
    rw [SimpleGraph.Walk.length_cons, Nat.even_add_one, ← ih]
    cases hx : side x <;> cases hy : side y <;> cases hz : side z <;> simp_all

/-- A real quadratic that is nonnegative everywhere has `p ≥ 0`, `r ≥ 0` and discriminant `≤ 0`
(including the degenerate `p = 0` case). (putnam_2003_a4) -/
lemma quad_nonneg {p q r : ℝ} (h : ∀ x : ℝ, 0 ≤ p * x ^ 2 + q * x + r) :
    0 ≤ p ∧ 0 ≤ r ∧ q ^ 2 ≤ 4 * p * r := by
  have hd : discrim p q r ≤ 0 := discrim_le_zero (fun x => by have := h x; nlinarith)
  unfold discrim at hd
  have hr : 0 ≤ r := by simpa using h 0
  refine ⟨?_, hr, by linarith⟩
  by_contra hp
  push Not at hp
  have hq : q = 0 := by nlinarith [sq_nonneg q]
  have hpn : 0 < -p := by linarith
  set x := (r + 1) / (-p) + 1 with hx
  have h0 : 0 ≤ (r + 1) / (-p) := div_nonneg (by linarith) hpn.le
  have hx1 : 1 ≤ x := by linarith
  have h3 : r + 1 ≤ -p * x := by
    have : (r + 1) / (-p) * (-p) = r + 1 := div_mul_cancel₀ _ hpn.ne'
    nlinarith
  have := h x
  rw [hq] at this
  nlinarith

/-- `r^(p/q) ≤ b` from the integer inequality `r^p ≤ b^q`. Keeps `norm_num` away from real powers: pick
small `p, q` (continued-fraction convergents) so `r^p ≤ b^q` is decidable by `norm_num`. (E1110G) -/
lemma rpow_div_le_of_pow_le {r b : ℝ} (hr : 0 ≤ r) (hb : 0 ≤ b) {p q : ℕ} (hq : 0 < q)
    (h : r ^ p ≤ b ^ q) : r ^ ((p : ℝ) / q) ≤ b := by
  have e : r ^ ((p : ℝ) / q) = (r ^ p) ^ ((q : ℝ)⁻¹) := by
    rw [← Real.rpow_natCast r p, ← Real.rpow_mul hr, div_eq_mul_inv]
  rw [e]
  calc (r ^ p) ^ ((q : ℝ)⁻¹) ≤ (b ^ q) ^ ((q : ℝ)⁻¹) :=
        Real.rpow_le_rpow (by positivity) h (by positivity)
    _ = b := Real.pow_rpow_inv_natCast hb hq.ne'

/-- `b < r^(p/q)` from the integer inequality `b^q < r^p`. (E1110G) -/
lemma lt_rpow_div_of_pow_lt {r b : ℝ} (hr : 0 ≤ r) (hb : 0 ≤ b) {p q : ℕ} (hq : 0 < q)
    (h : b ^ q < r ^ p) : b < r ^ ((p : ℝ) / q) := by
  have e : r ^ ((p : ℝ) / q) = (r ^ p) ^ ((q : ℝ)⁻¹) := by
    rw [← Real.rpow_natCast r p, ← Real.rpow_mul hr, div_eq_mul_inv]
  rw [e]
  calc b = (b ^ q) ^ ((q : ℝ)⁻¹) := (Real.pow_rpow_inv_natCast hb hq.ne').symm
    _ < (r ^ p) ^ ((q : ℝ)⁻¹) :=
        Real.rpow_lt_rpow (by positivity) h (by positivity)

/-- At least `⌊x/M⌋ · |R|` integers `n < x` have `n mod M ∈ R` (for `R` a set of residues `< M`). The
counting half of every "these residue classes are never representable" density bound. (E1110G) -/
lemma card_residues_ge {M x : ℕ} (R : Finset ℕ) (hR : ∀ c ∈ R, c < M) :
    x / M * R.card ≤ ((Finset.range x).filter (fun n => n % M ∈ R)).card := by
  rw [← Finset.card_range (x / M), ← Finset.card_product]
  refine Finset.card_le_card_of_injOn (fun p => M * p.1 + p.2) ?_ ?_
  · intro p hp
    simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio, Finset.mem_coe] at hp
    have hM := hR _ hp.2
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq]
    refine ⟨?_, ?_⟩
    · have h1 : M * (p.1 + 1) ≤ M * (x / M) := Nat.mul_le_mul_left M hp.1
      have h2 := Nat.mul_div_le x M
      rw [mul_add, mul_one] at h1
      omega
    · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hM]; exact hp.2
  · intro p hp q hq hpq
    simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio, Finset.mem_coe] at hp hq
    simp only at hpq
    have hp2 := hR _ hp.2; have hq2 := hR _ hq.2
    have e2 : p.2 = q.2 := by
      have := congrArg (· % M) hpq
      simpa [Nat.mul_add_mod, Nat.mod_eq_of_lt hp2, Nat.mod_eq_of_lt hq2] using this
    have hM : 0 < M := by omega
    have e1 : p.1 = q.1 := by
      rw [e2] at hpq
      exact Nat.eq_of_mul_eq_mul_left hM (by omega)
    exact Prod.ext e1 e2

/-- QM + GM ≤ 2·AM for two nonnegative reals: `√((x²+t²)/2) + √(xt) ≤ x + t`. (imo_2026_p5) -/
lemma qm_add_gm_le {x t : ℝ} (hx : 0 ≤ x) (ht : 0 ≤ t) :
    Real.sqrt ((x ^ 2 + t ^ 2) / 2) + Real.sqrt (x * t) ≤ x + t := by
  set u := Real.sqrt ((x ^ 2 + t ^ 2) / 2)
  set v := Real.sqrt (x * t)
  have hu : u ^ 2 = (x ^ 2 + t ^ 2) / 2 := Real.sq_sqrt (by positivity)
  have hv : v ^ 2 = x * t := Real.sq_sqrt (by positivity)
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hv0 : 0 ≤ v := Real.sqrt_nonneg _
  nlinarith [sq_nonneg (u - v), sq_nonneg (u + v - (x + t))]

/-- `(√x - √t)² ≤ |x - t|` for nonnegative reals (the AM–GM gap is at most the distance). (imo_2026_p5) -/
lemma sqrt_sub_sq_le_abs {x t : ℝ} (hx : 0 ≤ x) (ht : 0 ≤ t) :
    (Real.sqrt x - Real.sqrt t) ^ 2 ≤ |x - t| := by
  have ha := Real.sqrt_nonneg x
  have hb := Real.sqrt_nonneg t
  have h1 := Real.sq_sqrt hx
  have h2 := Real.sq_sqrt ht
  have e : x - t = (Real.sqrt x - Real.sqrt t) * (Real.sqrt x + Real.sqrt t) := by nlinarith
  rw [e, abs_mul, abs_of_nonneg (by positivity : 0 ≤ Real.sqrt x + Real.sqrt t)]
  have hle : |Real.sqrt x - Real.sqrt t| ≤ Real.sqrt x + Real.sqrt t := by
    calc |Real.sqrt x - Real.sqrt t| ≤ |Real.sqrt x| + |Real.sqrt t| := abs_sub _ _
      _ = Real.sqrt x + Real.sqrt t := by rw [abs_of_nonneg ha, abs_of_nonneg hb]
  calc (Real.sqrt x - Real.sqrt t) ^ 2 = |Real.sqrt x - Real.sqrt t| * |Real.sqrt x - Real.sqrt t| := by
        rw [abs_mul_abs_self]; ring
    _ ≤ |Real.sqrt x - Real.sqrt t| * (Real.sqrt x + Real.sqrt t) :=
        mul_le_mul_of_nonneg_left hle (abs_nonneg _)

/-- One subtractive Euclid step preserves the gcd: `gcd (min a b) (max a b - min a b) = gcd a b`.
With `padicValNat p (gcd m n) = min …` this makes "gcd of valuations" an invariant of gcd/lcm moves.
(imo_2026_p1) -/
lemma gcd_min_max (a b : ℕ) : Nat.gcd (min a b) (max a b - min a b) = Nat.gcd a b := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right h, Nat.gcd_sub_self_right h]
  · rw [min_eq_right h, max_eq_left h, Nat.gcd_sub_self_right h, Nat.gcd_comm]

/-- `p`-adic valuation of a gcd is the min of the valuations. (imo_2026_p1) -/
lemma padicValNat_gcd {p m n : ℕ} (hp : p.Prime) (hm : 0 < m) (hn : 0 < n) :
    padicValNat p (Nat.gcd m n) = min (padicValNat p m) (padicValNat p n) := by
  rw [← Nat.factorization_def _ hp, ← Nat.factorization_def _ hp, ← Nat.factorization_def _ hp,
    Nat.factorization_gcd hm.ne' hn.ne', Finsupp.inf_apply]

end Nanoprover

/-- Free-group word normalizer. Mathlib's `group` tactic FAILS on powers of
products like `(A*B*A)^2`; this simp set is the reliable normalizer.
(putnam_1972_b3, see KNOWN_TRAPS.md) -/
macro "group_nf" : tactic =>
  `(tactic| simp only [pow_succ, pow_zero, one_mul, mul_one, mul_assoc,
      mul_inv_cancel_left, inv_mul_cancel_left, mul_inv_cancel, inv_mul_cancel])
