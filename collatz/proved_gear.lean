def step (n : Nat) : Nat := if n % 2 = 0 then n / 2 else 3 * n + 1
def iter : Nat → Nat → Nat
  | 0,     n => n
  | k + 1, n => iter k (step n)
def reaches1 (n : Nat) : Prop := ∃ k, iter k n = 1
theorem reaches1_one : reaches1 1 := ⟨0, rfl⟩
theorem step_double (n : Nat) : step (2 * n) = n := by
  unfold step
  rw [if_pos (Nat.mul_mod_right 2 n), Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
theorem reaches1_double {n : Nat} : reaches1 n → reaches1 (2 * n) := by
  intro ⟨k, hk⟩
  exact ⟨k + 1, by show iter k (step (2 * n)) = 1; rw [step_double]; exact hk⟩
theorem reaches1_of_step {n : Nat} : reaches1 (step n) → reaches1 n := by
  intro ⟨k, hk⟩
  exact ⟨k + 1, hk⟩
theorem reaches1_iter : ∀ (k n : Nat), reaches1 (iter k n) → reaches1 n := by
  intro k
  induction k with
  | zero => intro n h; exact h
  | succ j ih => intro n h; exact reaches1_of_step (ih (step n) h)
theorem reaches1_mul_pow2 (k : Nat) {n : Nat} : reaches1 n → reaches1 (2 ^ k * n) := by
  induction k with
  | zero => intro h; rw [Nat.pow_zero, Nat.one_mul]; exact h
  | succ j ih =>
      intro h
      have h2 : 2 ^ (j + 1) * n = 2 * (2 ^ j * n) := by
        rw [Nat.pow_succ, Nat.mul_comm (2 ^ j) 2, Nat.mul_assoc]
      rw [h2]
      exact reaches1_double (ih h)
