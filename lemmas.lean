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

end Nanoprover

/-- Free-group word normalizer. Mathlib's `group` tactic FAILS on powers of
products like `(A*B*A)^2`; this simp set is the reliable normalizer.
(putnam_1972_b3, see KNOWN_TRAPS.md) -/
macro "group_nf" : tactic =>
  `(tactic| simp only [pow_succ, pow_zero, one_mul, mul_one, mul_assoc,
      mul_inv_cancel_left, inv_mul_cancel_left, mul_inv_cancel, inv_mul_cancel])
