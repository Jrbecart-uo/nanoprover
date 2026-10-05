import Mathlib

/-!
# Erdős–Straus (Erdős #242) outside the class `n ≡ 1 (mod 24)`

`ES n` is the statement of `Erdos242.erdos_242` from formal-conjectures, verbatim (distinct `x < y < z`).
Every hard residue class of Mordell (`1, 121, 169, 289, 361, 529 mod 840`) is `≡ 1 (mod 24)`; this file
proves the conjecture for all other `n`, with five explicit identities:

* `n = 2k`:      `4/n = 1/k + 1/(k+1) + 1/(k(k+1))`
* `n = 4k+3`:    `4/n = 1/(k+1) + 1/(m+1) + 1/(m(m+1))`, `m = n(k+1)`
* `n = 3m`:      `4/n = 1/m + 1/(4m) + 1/(12m)`
* `n = 3k+2`:    `4/n = 1/(k+1) + 1/n + 1/(n(k+1))`
* `n = 24k+13`:  `x = 6k+4`, `y = 48k²+58k+18`, `z = (72k²+87k+26)·y`  (`x = (n+3)/4`, `y = (nx+2)/3`, `z = nx·y/2`)
-/

namespace ErdosStraus

/-- `Erdos242.erdos_242`'s conclusion, verbatim. -/
def ES (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧ (4 / n : ℚ) = 1 / x + 1 / y + 1 / z

lemma es_even {k : ℕ} (hk : 2 ≤ k) : ES (2 * k) := by
  refine ⟨k, k + 1, k * (k + 1), by omega, by omega, by nlinarith, ?_⟩
  have hk0 : (k : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

lemma es_three_mod_four (k : ℕ) : ES (4 * k + 3) := by
  set m := (4 * k + 3) * (k + 1) with hm
  have hm1 : k + 1 < m + 1 := by rw [hm]; nlinarith
  refine ⟨k + 1, m + 1, m * (m + 1), by omega, hm1, by nlinarith, ?_⟩
  rw [hm]
  push_cast
  field_simp
  ring

lemma es_mul_three {m : ℕ} (hm : 1 ≤ m) : ES (3 * m) := by
  refine ⟨m, 4 * m, 12 * m, hm, by omega, by omega, ?_⟩
  have : (m : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

lemma es_two_mod_three {k : ℕ} (hk : 1 ≤ k) : ES (3 * k + 2) := by
  refine ⟨k + 1, 3 * k + 2, (3 * k + 2) * (k + 1), by omega, by omega, by nlinarith, ?_⟩
  push_cast
  field_simp
  ring

lemma es_thirteen_mod_24 (k : ℕ) : ES (24 * k + 13) := by
  refine ⟨6 * k + 4, 48 * k ^ 2 + 58 * k + 18, (72 * k ^ 2 + 87 * k + 26) * (48 * k ^ 2 + 58 * k + 18),
    by omega, by nlinarith, by nlinarith, ?_⟩
  push_cast
  field_simp
  ring

/-- **Erdős–Straus holds for every `n > 2` with `n ≢ 1 (mod 24)`.** -/
theorem es_of_not_one_mod_24 (n : ℕ) (hn : 2 < n) (h24 : n % 24 ≠ 1) : ES n := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | hodd
  · rw [show n = 2 * k by omega]; exact es_even (by omega)
  · by_cases h4 : n % 4 = 3
    · rw [show n = 4 * (n / 4) + 3 by omega]; exact es_three_mod_four _
    · by_cases h3 : n % 3 = 0
      · rw [show n = 3 * (n / 3) by omega]; exact es_mul_three (by omega)
      · by_cases h32 : n % 3 = 2
        · rw [show n = 3 * (n / 3) + 2 by omega]; exact es_two_mod_three (by omega)
        · have : n % 24 = 13 := by
            have := Nat.odd_iff.mp hodd
            omega
          rw [show n = 24 * (n / 24) + 13 by omega]; exact es_thirteen_mod_24 _

/-- Solutions scale: a solution for `m` gives one for every multiple `k m`. -/
lemma es_mul {m k : ℕ} (hk : 1 ≤ k) (h : ES m) : ES (k * m) := by
  obtain ⟨x, y, z, hx, hxy, hyz, he⟩ := h
  refine ⟨k * x, k * y, k * z, by nlinarith, Nat.mul_lt_mul_of_pos_left hxy (by omega),
    Nat.mul_lt_mul_of_pos_left hyz (by omega), ?_⟩
  have hk0 : (k : ℚ) ≠ 0 := by positivity
  have e : (4 / ((k * m : ℕ) : ℚ)) = (4 / (m : ℚ)) / k := by push_cast; rw [div_div, mul_comm]
  rw [e, he]
  push_cast
  field_simp

/-- **Erdős–Straus holds for every `n > 2` having a prime factor `p ≢ 1 (mod 24)`.** The open cases are the
`n > 2` all of whose prime factors are `≡ 1 (mod 24)`. -/
theorem es_of_prime_factor (n : ℕ) (hn : 2 < n) (h : ∃ p, p.Prime ∧ p ∣ n ∧ p % 24 ≠ 1) : ES n := by
  obtain ⟨p, hp, hpn, hp24⟩ := h
  obtain ⟨k, rfl⟩ := hpn
  have hk : 1 ≤ k := by rcases k with _ | k <;> simp_all
  rcases hp.eq_two_or_odd' with rfl | hodd
  · rcases Nat.even_or_odd k with ⟨j, hj⟩ | hko
    · rw [show 2 * k = 2 * (2 * j) by omega]; exact es_even (by omega)
    · exact es_of_not_one_mod_24 _ hn (by have := Nat.odd_iff.mp hko; omega)
  · rw [mul_comm]
    exact es_mul hk (es_of_not_one_mod_24 p (by have := hp.two_le; have := Nat.odd_iff.mp hodd; omega) hp24)

/-- **Certificate lemma.** If `4x = n + a` with `0 < a < n`, and `d ∣ (nx)²` with `d < nx`, `a ∣ nx + d` and
`a ∣ nx + (nx)²/d`, then `4/n = 1/x + 1/y + 1/z` with `y = (nx+d)/a`, `z = (nx + (nx)²/d)/a`. -/
lemma es_of_cert {n a x d : ℕ} (ha : 0 < a) (han : a < n) (hx : 4 * x = n + a) (hd : d ∣ (n * x) ^ 2)
    (hd0 : 0 < d) (hdB : d < n * x) (h1 : a ∣ n * x + d) (h2 : a ∣ n * x + (n * x) ^ 2 / d) : ES n := by
  set B := n * x with hB
  have hx0 : 0 < x := by omega
  have hn0 : 0 < n := by omega
  have hB0 : 0 < B := Nat.mul_pos hn0 hx0
  obtain ⟨y, hy⟩ := h1
  obtain ⟨z, hz⟩ := h2
  obtain ⟨c, hc⟩ := hd
  have hcd : B ^ 2 / d = c := by rw [hc]; exact Nat.mul_div_cancel_left c hd0
  rw [hcd] at hz
  -- `c > B` since `d < B` and `d c = B²`
  have hcB : B < c := by
    by_contra h; push Not at h
    have : d * c < B * B := Nat.mul_lt_mul_of_lt_of_le hdB h (by omega)
    nlinarith
  have hxy : x < y := by
    have : a * x < a * y := by
      rw [← hy]
      have : a * x < n * x := Nat.mul_lt_mul_of_pos_right han hx0
      omega
    exact Nat.lt_of_mul_lt_mul_left this
  have hyz : y < z := by
    have : a * y < a * z := by rw [← hy, ← hz]; omega
    exact Nat.lt_of_mul_lt_mul_left this
  refine ⟨x, y, z, hx0, hxy, hyz, ?_⟩
  have hyq : (a : ℚ) * y = B + d := by exact_mod_cast hy.symm
  have hzq : (a : ℚ) * z = B + c := by exact_mod_cast hz.symm
  have hcq : (d : ℚ) * c = B ^ 2 := by exact_mod_cast hc.symm
  have hxq : 4 * (x : ℚ) = n + a := by exact_mod_cast hx
  have hBq : (B : ℚ) = n * x := by rw [hB]; push_cast; ring
  have hy0 : (y : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hz0 : (z : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hd0' : (d : ℚ) ≠ 0 := by exact_mod_cast hd0.ne'
  have hx0' : (x : ℚ) ≠ 0 := by exact_mod_cast hx0.ne'
  have hn0' : (n : ℚ) ≠ 0 := by exact_mod_cast hn0.ne'
  have hB0' : (B : ℚ) ≠ 0 := by exact_mod_cast hB0.ne'
  -- 1/y + 1/z = a/B, and 4/n - 1/x = a/B
  have e1 : (1 : ℚ) / y + 1 / z = a / B := by
    have hy' : (y : ℚ) = (B + d) / a := by field_simp; linarith
    have hz' : (z : ℚ) = (B + c) / a := by field_simp; linarith
    have hc' : (c : ℚ) = B ^ 2 / d := by field_simp; linarith
    rw [hy', hz', hc']
    have : (B : ℚ) + d ≠ 0 := by positivity
    field_simp
    ring
  have e2 : (4 : ℚ) / n - 1 / x = a / B := by
    rw [hBq]; field_simp; linarith
  linarith

/-- **A non-congruence criterion.** If `n ≡ 1 (mod 12)` and `(n+3)/4` has a divisor `d ≡ 2 (mod 3)`, then `ES n`
(take `a = 3`: `x = (n+3)/4`, `y = (nx+d)/3`, `z = (nx/d)(nx+d)/3`). For primes `p ≡ 1 (mod 24)` below `10^8`
this is exactly the condition for `a = 3` to work (hypothesis H8 of round 1). -/
theorem es_of_divisor_two_mod_three {n d : ℕ} (hn : n % 12 = 1) (hn1 : 1 < n) (hd : d ∣ (n + 3) / 4)
    (hd3 : d % 3 = 2) : ES n := by
  set x := (n + 3) / 4 with hxdef
  have hx : 4 * x = n + 3 := by omega
  have hx3 : x % 3 = 1 := by omega
  obtain ⟨e, he⟩ := hd
  have hd0 : 0 < d := by omega
  have hxpos : 0 < x := by omega
  apply es_of_cert (a := 3) (x := x) (d := d) (by norm_num) (by omega) hx
  · exact (Dvd.dvd.mul_left ⟨e, he⟩ n).trans (dvd_pow_self _ two_ne_zero)
  · exact hd0
  · have : d ≤ x := Nat.le_of_dvd hxpos ⟨e, he⟩
    have : x < n * x := by nlinarith
    omega
  · -- n x + d ≡ 1·1 + 2 ≡ 0 (mod 3)
    have : (n * x + d) % 3 = 0 := by
      rw [Nat.add_mod, Nat.mul_mod, show n % 3 = 1 by omega, hx3, hd3]
    exact Nat.dvd_of_mod_eq_zero this
  · -- (n x)²/d = n² x e  and  n x + n² x e = n x (1 + n e) with 1 + n e ≡ 1 + e ≡ 0 (mod 3)
    have he3 : e % 3 = 2 := by
      have : (d * e) % 3 = 1 := by rw [← he]; exact hx3
      rw [Nat.mul_mod, hd3] at this
      have : e % 3 < 3 := Nat.mod_lt _ (by norm_num)
      interval_cases h : e % 3 <;> simp_all
    have hq : (n * x) ^ 2 / d = n * n * x * e := by
      rw [show (n * x) ^ 2 = d * (n * n * x * e) by rw [mul_pow, he]; ring]
      exact Nat.mul_div_cancel_left _ hd0
    rw [hq]
    have : (n * x + n * n * x * e) % 3 = 0 := by
      rw [show n * x + n * n * x * e = n * x * (1 + n * e) by ring, Nat.mul_mod,
        show (1 + n * e) % 3 = 0 by rw [Nat.add_mod, Nat.mul_mod, show n % 3 = 1 by omega, he3]]
      simp
    exact Nat.dvd_of_mod_eq_zero this

/-! ## Mordell's theorem: everything outside the six square classes mod 840 -/

lemma es_7k3 {k : ℕ} (hk : 1 ≤ k) : ES (7 * k + 3) := by
  refine ⟨2 * k + 1, 2 * (7 * k + 3), 2 * (7 * k + 3) * (2 * k + 1), by omega, by omega, by nlinarith, ?_⟩
  push_cast; field_simp; ring

lemma es_7k6 {k : ℕ} (hk : 1 ≤ k) : ES (7 * k + 6) := by
  refine ⟨2 * k + 2, 2 * (7 * k + 6), 2 * (7 * k + 6) * (k + 1), by omega, by omega, by nlinarith, ?_⟩
  push_cast; field_simp; ring

lemma es_7k5 {k : ℕ} (hk : 2 ≤ k) : ES (7 * k + 5) := by
  refine ⟨2 * k + 2, 2 * (7 * k + 5), (7 * k + 5) * (k + 1), by omega, by omega, by nlinarith, ?_⟩
  push_cast; field_simp; ring

lemma es_15k7 {k : ℕ} (hk : 1 ≤ k) : ES (15 * k + 7) := by
  refine ⟨4 * k + 2, 4 * (15 * k + 7), 4 * (15 * k + 7) * (2 * k + 1), by omega, by omega, by nlinarith, ?_⟩
  push_cast; field_simp; ring

lemma es_15k13 {k : ℕ} (hk : 2 ≤ k) : ES (15 * k + 13) := by
  refine ⟨4 * k + 4, 4 * (15 * k + 13), 2 * (15 * k + 13) * (k + 1), by omega, by omega, by nlinarith, ?_⟩
  push_cast; field_simp; ring

/-- The residue bookkeeping behind Mordell's theorem: the 35 classes `≡ 1 (mod 24)` mod 840. -/
lemma mordell_residues : ∀ t ∈ Finset.range 35, (24 * t + 1) % 5 ≠ 0 → (24 * t + 1) % 7 ≠ 0 → (24 * t + 1) % 15 ≠ 7 →
    (24 * t + 1) % 15 ≠ 13 → (24 * t + 1) % 7 ≠ 3 → (24 * t + 1) % 7 ≠ 6 → (24 * t + 1) % 7 ≠ 5 →
    24 * t + 1 = 1 ∨ 24 * t + 1 = 121 ∨ 24 * t + 1 = 169 ∨ 24 * t + 1 = 289 ∨ 24 * t + 1 = 361 ∨ 24 * t + 1 = 529 := by
  decide

/-- **Mordell's theorem, kernel-checked.** Erdős–Straus holds for every `n > 2` outside the six classes
`n ≡ 1, 121, 169, 289, 361, 529 (mod 840)` (the squares mod 840 that are `≡ 1 mod 24`, i.e. `n` a quadratic
residue mod 3, 5, 7, 8). -/
theorem es_mordell (n : ℕ) (hn : 2 < n)
    (h840 : n % 840 ≠ 1 ∧ n % 840 ≠ 121 ∧ n % 840 ≠ 169 ∧ n % 840 ≠ 289 ∧ n % 840 ≠ 361 ∧ n % 840 ≠ 529) :
    ES n := by
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := h840
  by_cases h24 : n % 24 = 1
  · have hn25 : 25 ≤ n := by omega
    by_cases h5 : n % 5 = 0
    · obtain ⟨m, rfl⟩ : 5 ∣ n := Nat.dvd_of_mod_eq_zero h5
      rw [mul_comm]; exact es_mul (by omega) (es_of_not_one_mod_24 5 (by norm_num) (by norm_num))
    by_cases h7 : n % 7 = 0
    · obtain ⟨m, rfl⟩ : 7 ∣ n := Nat.dvd_of_mod_eq_zero h7
      rw [mul_comm]; exact es_mul (by omega) (es_of_not_one_mod_24 7 (by norm_num) (by norm_num))
    by_cases h15a : n % 15 = 7
    · rw [show n = 15 * (n / 15) + 7 by omega]; exact es_15k7 (by omega)
    by_cases h15b : n % 15 = 13
    · rw [show n = 15 * (n / 15) + 13 by omega]; exact es_15k13 (by omega)
    by_cases h73 : n % 7 = 3
    · rw [show n = 7 * (n / 7) + 3 by omega]; exact es_7k3 (by omega)
    by_cases h76 : n % 7 = 6
    · rw [show n = 7 * (n / 7) + 6 by omega]; exact es_7k6 (by omega)
    by_cases h75 : n % 7 = 5
    · rw [show n = 7 * (n / 7) + 5 by omega]; exact es_7k5 (by omega)
    exfalso
    have m5 : n % 5 = n % 840 % 5 := (Nat.mod_mod_of_dvd n (by norm_num)).symm
    have m7 : n % 7 = n % 840 % 7 := (Nat.mod_mod_of_dvd n (by norm_num)).symm
    have m15 : n % 15 = n % 840 % 15 := (Nat.mod_mod_of_dvd n (by norm_num)).symm
    have m24 : n % 24 = n % 840 % 24 := (Nat.mod_mod_of_dvd n (by norm_num)).symm
    have hr : n % 840 < 840 := Nat.mod_lt _ (by norm_num)
    generalize n % 840 = r at *
    obtain ⟨t, rfl⟩ : ∃ t, r = 24 * t + 1 := ⟨r / 24, by omega⟩
    have ht : t < 35 := by omega
    rw [m5] at h5; rw [m7] at h7 h73 h76 h75; rw [m15] at h15a h15b
    rcases mordell_residues t (Finset.mem_range.mpr ht) h5 h7 h15a h15b h73 h76 h75 with h | h | h | h | h | h <;> omega
  · exact es_of_not_one_mod_24 n hn h24

end ErdosStraus

#print axioms ErdosStraus.es_of_not_one_mod_24
#print axioms ErdosStraus.es_of_prime_factor
#print axioms ErdosStraus.es_of_cert
#print axioms ErdosStraus.es_of_divisor_two_mod_three
#print axioms ErdosStraus.es_mordell
