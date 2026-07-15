import Mathlib
open Module

/-!
# CDCProof.Core — the finite `𝔽₂³` facts

The parity identity `cdc_crux`, its dual form `cdc_crux_dual`, the self-duality
bridge, the local-set condition `cdc_local`, and `cdc_pairs`.  Kernel-decided.
-/

namespace CDCProof

abbrev G3 := ZMod 2 × ZMod 2 × ZMod 2
def dot (a b : G3) : ZMod 2 := a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2
def nz (a : G3) : ZMod 2 := if a = 0 then 0 else 1

set_option synthInstance.maxSize 800 in
set_option maxRecDepth 40000 in
theorem cdc_crux (x y ηa ηb : G3)
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y)
    (ha : dot ηa x = 0) (hb : dot ηb y = 0) (hc : dot (ηa + ηb) (x + y) = 0) :
    dot ηb x = nz ηa + nz ηb + nz (ηa + ηb) := by
  revert x y ηa ηb; decide

def dotL (a : G3) : Dual (ZMod 2) G3 where
  toFun b := dot a b
  map_add' b c := by simp only [dot, Prod.fst_add, Prod.snd_add]; ring
  map_smul' c b := by
    simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]; ring

@[simp] lemma dotL_apply (a b : G3) : dotL a b = dot a b := rfl

theorem exists_dot_eq (φ : Dual (ZMod 2) G3) : ∃ a : G3, φ = dotL a := by
  refine ⟨(φ (1,0,0), φ (0,1,0), φ (0,0,1)), ?_⟩
  refine LinearMap.ext fun b => ?_
  obtain ⟨b1, b2, b3⟩ := b
  have hb : ((b1,b2,b3) : G3)
      = b1 • ((1,0,0) : G3) + b2 • ((0,1,0) : G3) + b3 • ((0,0,1) : G3) := by
    simp [smul_eq_mul]
  rw [hb]
  simp only [map_add, map_smul, smul_eq_mul, dotL, dot, LinearMap.coe_mk, AddHom.coe_mk]
  ring

@[simp] lemma dotL_add (a b : G3) : dotL (a + b) = dotL a + dotL b := by
  refine LinearMap.ext fun c => ?_
  simp only [dotL, dot, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply,
    Prod.fst_add, Prod.snd_add]; ring

@[simp] lemma dotL_zero : dotL 0 = 0 := by
  refine LinearMap.ext fun c => ?_; simp [dotL, dot]

/-- `dotL a = 0 ↔ a = 0`: the standard pairing on `𝔽₂³` is nondegenerate. -/
lemma dotL_eq_zero_iff (a : G3) : dotL a = 0 ↔ a = 0 := by
  constructor
  · intro h
    have h1 : dot a (1,0,0) = 0 := by rw [← dotL_apply, h]; rfl
    have h2 : dot a (0,1,0) = 0 := by rw [← dotL_apply, h]; rfl
    have h3 : dot a (0,0,1) = 0 := by rw [← dotL_apply, h]; rfl
    obtain ⟨a1, a2, a3⟩ := a
    simp only [dot, mul_one, mul_zero, add_zero, zero_add] at h1 h2 h3
    simp only [Prod.ext_iff]
    exact ⟨h1, h2, h3⟩
  · rintro rfl; exact dotL_zero

/-- `nz` as an indicator on the dual side. -/
def nzD (φ : Dual (ZMod 2) G3) : ZMod 2 := if φ = 0 then 0 else 1

lemma nzD_dotL (a : G3) : nzD (dotL a) = nz a := by
  unfold nzD nz
  by_cases h : a = 0
  · subst h; rw [if_pos dotL_zero, if_pos rfl]
  · rw [if_neg h, if_neg]; rwa [dotL_eq_zero_iff]

/-- **Dual-form crux.**  Same statement as `cdc_crux` but for functionals
`ηa, ηb : Dual 𝔽₂ G3`, which is the form the assembly produces. -/
theorem cdc_crux_dual (x y : G3) (ηa ηb : Dual (ZMod 2) G3)
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y)
    (ha : ηa x = 0) (hb : ηb y = 0) (hc : (ηa + ηb) (x + y) = 0) :
    ηb x = nzD ηa + nzD ηb + nzD (ηa + ηb) := by
  obtain ⟨a, rfl⟩ := exists_dot_eq ηa
  obtain ⟨b, rfl⟩ := exists_dot_eq ηb
  rw [← dotL_add] at hc ⊢
  simp only [dotL_apply] at ha hb hc ⊢
  rw [nzD_dotL, nzD_dotL, nzD_dotL]
  exact cdc_crux x y a b hx hy hxy ha hb hc

/-- Membership count of `s` among the three local sets at a cubic vertex.

At a vertex the incident flows are `x`, `y`, `z = x + y` (all nonzero; the flow
law forces the sum to vanish in characteristic 2, and `x ≠ y` since otherwise
`z = 0`).  With the gauge `g(a) = 0`, `g(b) = x`, `g(c) = 0` the three sets
`{t + g(e), t + g(e) + f(e)}` are

    P_a = {t, t+x}      P_b = {t+x, t+z}      P_c = {t, t+z}

Boolean `==` rather than `if _ ∈ _` keeps this **computable**: an `if` on a `Prop`
silently picks up a classical instance, and then `decide` has nothing to run. -/
def cnt (t x y s : G3) : ℕ :=
  (if (s == t || s == t + x) then 1 else 0) +
  (if (s == t + x || s == t + (x + y)) then 1 else 0) +
  (if (s == t || s == t + (x + y)) then 1 else 0)

set_option synthInstance.maxSize 800
set_option synthInstance.maxHeartbeats 1000000
set_option maxRecDepth 40000

/-- **Local condition (1).** Every vector lies in exactly 0 or 2 of the three sets
at a vertex — never 1 or 3.

This is the entire reason the construction yields a *cycle* double cover: it makes
every `Mₛ` a disjoint union of cycles. Note it holds for **every** value of the
free parameter `t`, and that freedom is exactly what leaves room to solve the
edge-consistency system afterwards. `Γ` is finite, so the kernel checks all
8⁴ = 4096 cases outright. -/
theorem cdc_local : ∀ (t x y s : G3), x ≠ 0 → y ≠ 0 → x ≠ y →
    cnt t x y s = 0 ∨ cnt t x y s = 2 := by decide

/-- Each `Pₑ` really is a **two**-element set (the three local vectors are
distinct), which is what makes every edge lie in exactly two of the `Mₛ`. -/
theorem cdc_pairs : ∀ (t x y : G3), x ≠ 0 → y ≠ 0 → x ≠ y →
    t ≠ t + x ∧ t + x ≠ t + (x + y) ∧ t ≠ t + (x + y) := by decide

end CDCProof
