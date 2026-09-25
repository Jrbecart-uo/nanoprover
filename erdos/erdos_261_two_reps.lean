/-!
Erdős #261, `erdos_261.variants.two_representations` (formal-conjectures), tagged
`research open`. It is settled by one swap: 4/2^4 = 5/2^5 + 6/2^6.
  3/8 = Σ_{k≥5} k/2^k            (a k = k + 5)
  3/8 = 4/2^4 + Σ_{k≥7} k/2^k    (b 0 = 4, b (k+1) = k + 7)
Definitions copied verbatim from FormalConjectures/ErdosProblems/261.lean;
`answer(sorry)` instantiated with `True`, `#` spelled `Cardinal.mk`.
-/

def Erdos261InfiniteRepresentation (x : ℚ) (a : ℕ → ℕ) : Prop :=
  StrictMono a ∧ (1 ≤ a) ∧ Summable (fun k => (a k) / (2 ^ (a k) : ℚ)) ∧
    x = ∑' k, (a k) / (2 ^ (a k) : ℚ)

/-- `Σ n * (1/2)^n = 2` over ℚ (ℚ is a normed division ring; no completeness needed). -/
lemma hasSum_half : HasSum (fun n : ℕ => (n : ℚ) * (1 / 2) ^ n) 2 := by
  have h := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℚ) (r := 1 / 2)
    (by rw [← Rat.norm_cast_real]; norm_num)
  norm_num at h ⊢
  exact h

lemma term_eq (n : ℕ) : (n : ℚ) / 2 ^ n = (n : ℚ) * (1 / 2) ^ n := by
  rw [one_div, inv_pow, div_eq_mul_inv]

/-- Tail from 5: sum 3/8. -/
lemma hasSum_a : HasSum (fun k : ℕ => ((k + 5 : ℕ) : ℚ) / 2 ^ (k + 5)) (3 / 8) := by
  have h := (hasSum_nat_add_iff' 5).mpr hasSum_half
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  have e : (fun k : ℕ => ((k + 5 : ℕ) : ℚ) / 2 ^ (k + 5)) =
      fun n : ℕ => ((n : ℚ) + 5) * (1 / 2) ^ (n + 5) := by
    funext k; push_cast; rw [one_div, inv_pow, div_eq_mul_inv]
  rw [e]; exact h

def bseq : ℕ → ℕ := fun k => if k = 0 then 4 else k + 6

lemma bseq_strictMono : StrictMono bseq := by
  apply strictMono_nat_of_lt_succ
  intro k; cases k <;> simp [bseq]

lemma hasSum_b : HasSum (fun k : ℕ => ((bseq k : ℕ) : ℚ) / 2 ^ (bseq k)) (3 / 8) := by
  have h7 := (hasSum_nat_add_iff' 7).mpr hasSum_half
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h7
  norm_num at h7
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [bseq]
  convert h7 using 2 with k
  rw [one_div, inv_pow, div_eq_mul_inv]; ring

theorem erdos_261_two_representations : True ↔ ∃ x : ℚ,
    2 ≤ Cardinal.mk {a : ℕ → ℕ | Erdos261InfiniteRepresentation x a} := by
  simp only [true_iff]
  refine ⟨3 / 8, ?_⟩
  rw [Cardinal.two_le_iff]
  refine ⟨⟨fun k => k + 5, ?_⟩, ⟨bseq, ?_⟩, ?_⟩
  · refine ⟨fun i j h => by simpa using h, fun k => by simp, hasSum_a.summable,
      hasSum_a.tsum_eq.symm⟩
  · refine ⟨bseq_strictMono, fun k => ?_, hasSum_b.summable, hasSum_b.tsum_eq.symm⟩
    simp only [Pi.one_apply, bseq]; split_ifs <;> omega
  · intro h
    have := congrFun (congrArg Subtype.val h) 0
    simp [bseq] at this

#print axioms erdos_261_two_representations
