"""
OUTER LOOP, step 2: proposed "gear" -- candidate closure lemmas.

Proposed by the session LLM (Claude) after observing the stall: backward-tree
BFS saturates at 82% coverage of 1..100 because some numbers (27!) are only
reachable through huge orbit peaks. The re-orientation idea: stop searching
backward from 1; instead notice that reaches1 is preserved along FORWARD steps,
so any n whose forward orbit hits a verified number is verified. That turns
search into computation.

Each candidate carries proof attempts (tried in order). The kernel is the
filter: PROVED gear joins the rule set, REJECTED gear is discarded, and
candidates whose attempts all fail are PARKED (maybe true, no proof found).
"""

PRELUDE = """def step (n : Nat) : Nat := if n % 2 = 0 then n / 2 else 3 * n + 1
def iter : Nat → Nat → Nat
  | 0,     n => n
  | k + 1, n => iter k (step n)
def reaches1 (n : Nat) : Prop := ∃ k, iter k n = 1
theorem reaches1_one : reaches1 1 := ⟨0, rfl⟩
"""

# Gear already in service (proved last session) -- new gear may reference it.
EXISTING_GEAR = """theorem step_double (n : Nat) : step (2 * n) = n := by
  unfold step
  rw [if_pos (Nat.mul_mod_right 2 n), Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
theorem reaches1_double {n : Nat} : reaches1 n → reaches1 (2 * n) := by
  intro ⟨k, hk⟩
  exact ⟨k + 1, by show iter k (step (2 * n)) = 1; rw [step_double]; exact hk⟩
"""

CANDIDATES = [
    {
        "name": "reaches1_of_step",
        "statement": "theorem reaches1_of_step {n : Nat} : reaches1 (step n) → reaches1 n",
        "why": "one-step forward closure: subsumes BOTH old backward rules "
               "(double and odd) in a single parity-free lemma",
        "attempts": [
            ":= by\n  intro ⟨k, hk⟩\n  exact ⟨k + 1, hk⟩",
        ],
    },
    {
        "name": "reaches1_iter",
        "statement": "theorem reaches1_iter : ∀ (k n : Nat), reaches1 (iter k n) → reaches1 n",
        "why": "orbit-jump: if ANY point of the forward orbit is verified, n is. "
               "Turns proving reaches1 n into computing the orbit -- constant-size proofs",
        "attempts": [
            ":= by\n  intro k\n  induction k with\n"
            "  | zero => intro n h; exact h\n"
            "  | succ j ih => intro n h; exact reaches1_of_step (ih (step n) h)",
        ],
    },
    {
        "name": "reaches1_mul_pow2",
        "statement": "theorem reaches1_mul_pow2 (k : Nat) {n : Nat} : reaches1 n → reaches1 (2 ^ k * n)",
        "why": "generalizes doubling to arbitrary power-of-two multiples in one shot",
        "attempts": [
            ":= by\n  induction k with\n"
            "  | zero => intro h; simpa using h\n"
            "  | succ j ih =>\n"
            "      intro h\n"
            "      have h2 : 2 ^ (j + 1) * n = 2 * (2 ^ j * n) := by\n"
            "        rw [Nat.pow_succ]; omega_nat\n"
            "      sorry",
            ":= by\n  induction k with\n"
            "  | zero => intro h; rw [Nat.pow_zero, Nat.one_mul]; exact h\n"
            "  | succ j ih =>\n"
            "      intro h\n"
            "      have h2 : 2 ^ (j + 1) * n = 2 * (2 ^ j * n) := by\n"
            "        rw [Nat.pow_succ, Nat.mul_comm (2 ^ j) 2, Nat.mul_assoc]\n"
            "      rw [h2]\n"
            "      exact reaches1_double (ih h)",
        ],
    },
    {
        # DELIBERATE OVERREACH: sounds plausible, but proving it would prove the
        # whole conjecture by induction from 1. The kernel must reject it.
        "name": "reaches1_add_two",
        "statement": "theorem reaches1_add_two {n : Nat} : reaches1 n → reaches1 (n + 2)",
        "why": "if true, Collatz follows by induction -- the kernel should refuse",
        "attempts": [
            ":= by\n  intro ⟨k, hk⟩\n  exact ⟨k, by omega⟩",
            ":= by\n  intro h\n  simp [reaches1, iter, step] at *\n  omega",
        ],
    },
    {
        # Also unprovable from current knowledge (would need deep structure).
        "name": "reaches1_triple",
        "statement": "theorem reaches1_triple {n : Nat} : reaches1 n → reaches1 (3 * n)",
        "why": "plausible-sounding multiplicative closure -- no known proof route",
        "attempts": [
            ":= by\n  intro ⟨k, hk⟩\n  exact ⟨k + 2, by simp [step]; omega⟩",
        ],
    },
]
