set_option maxRecDepth 100000
def step (n : Nat) : Nat := if n % 2 = 0 then n / 2 else 3 * n + 1
def iter : Nat → Nat → Nat
  | 0,     n => n
  | k + 1, n => iter k (step n)
def reaches1 (n : Nat) : Prop := ∃ k, iter k n = 1

/-- Bounded checker: does n reach 1 within `fuel` steps? -/
def chk : Nat → Nat → Bool
  | 0,     _ => false
  | f + 1, n => if n = 1 then true else chk f (step n)

/-- SOUNDNESS BRIDGE: if the checker says yes, the real property holds. -/
theorem chk_sound : ∀ fuel n, chk fuel n = true → reaches1 n := by
  intro fuel
  induction fuel with
  | zero => intro n h; simp [chk] at h
  | succ f ih =>
      intro n h
      unfold chk at h
      by_cases hn : n = 1
      · exact ⟨0, hn⟩
      · rw [if_neg hn] at h
        obtain ⟨k, hk⟩ := ih (step n) h
        exact ⟨k + 1, hk⟩

/-- Check every n in 1..N (descending). -/
def chkAll : Nat → Bool
  | 0     => true
  | n + 1 => chk 260 (n + 1) && chkAll n

theorem chkAll_sound : ∀ N, chkAll N = true → ∀ n, 1 ≤ n → n ≤ N → reaches1 n := by
  intro N
  induction N with
  | zero => intro _ n h1 h2; omega
  | succ M ih =>
      intro h n h1 h2
      unfold chkAll at h
      rw [Bool.and_eq_true] at h
      by_cases hn : n = M + 1
      · exact hn ▸ chk_sound 260 (M + 1) h.1
      · exact ih h.2 n h1 (by omega)

-- RESULT 2: Collatz verified for all 1 ≤ n ≤ 100, kernel-checked.
-- Pure kernel reduction (no compiler trust) for 1..200:
set_option maxHeartbeats 2000000 in
theorem collatz_up_to_200 : ∀ n, 1 ≤ n → n ≤ 200 → reaches1 n :=
  chkAll_sound 200 (by decide)

-- Compiled evaluation (native_decide) reaches 1..1000 in milliseconds:
theorem collatz_up_to_1000 : ∀ n, 1 ≤ n → n ≤ 1000 → reaches1 n :=
  chkAll_sound 1000 (by native_decide)

-- Powers of two (infinite family), from collatz2:
theorem step_pow2 (m : Nat) : step (2 ^ (m + 1)) = 2 ^ m := by
  unfold step
  have h1 : 2 ^ (m + 1) % 2 = 0 := by
    rw [Nat.pow_succ]; exact Nat.mul_mod_left _ _
  rw [if_pos h1, Nat.pow_succ, Nat.mul_div_cancel _ (by decide : 0 < 2)]
theorem iter_pow2 (m : Nat) : iter m (2 ^ m) = 1 := by
  induction m with
  | zero => rfl
  | succ k ih => show iter k (step (2 ^ (k + 1))) = 1
                 rw [step_pow2, ih]
theorem collatz_pow2 (m : Nat) : reaches1 (2 ^ m) := ⟨m, iter_pow2 m⟩
