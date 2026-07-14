import Mathlib

open Finset Module

namespace CDC

/-! ## PIECE A -/

section Duality

variable {K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
  [AddCommGroup N] [Module K N]

/-- **Duality criterion.** `d` is in the range of `L` iff every functional that
kills the range of `L` also kills `d`. -/
theorem mem_range_iff_forall_dual (L : M →ₗ[K] N) (d : N) :
    d ∈ LinearMap.range L ↔
      ∀ φ : Dual K N, (∀ x : M, φ (L x) = 0) → φ d = 0 := by
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff (LinearMap.range L) d]
  constructor
  · intro h φ hφ
    refine h φ ((Submodule.mem_dualAnnihilator φ).2 ?_)
    rintro _ ⟨x, rfl⟩; exact hφ x
  · intro h φ hφ
    exact h φ fun x => (Submodule.mem_dualAnnihilator φ).1 hφ _ ⟨x, rfl⟩

variable {E Γ : Type*} [DecidableEq E] [Fintype E] [AddCommGroup Γ] [Module K Γ]

/-- Every functional on `E → Γ` (`E` finite) is a *dual family* `η : E → Dual K Γ`
paired coordinatewise: `φ y = ∑ e, η e (y e)`. -/
theorem exists_dualFamily (φ : Dual K (E → Γ)) :
    ∃ η : E → Dual K Γ, ∀ y : E → Γ, ∑ e, η e (y e) = φ y := by
  refine ⟨fun e => φ ∘ₗ LinearMap.single K (fun _ : E => Γ) e, fun y => ?_⟩
  simp only [LinearMap.comp_apply, LinearMap.coe_single]
  rw [← map_sum, Finset.univ_sum_single]

/-- **Duality criterion, dual-family form** — the shape Lemma 2.2 actually uses:
the system `L x = d` (unknown `x`) is solvable iff every family `η = (η_e)` of
functionals on `Γ` that annihilates all of `L`'s image also satisfies
`∑ e, η e (d e) = 0`. -/
theorem mem_range_iff_forall_dualFamily (L : M →ₗ[K] (E → Γ)) (d : E → Γ) :
    d ∈ LinearMap.range L ↔
      ∀ η : E → Dual K Γ, (∀ x : M, ∑ e, η e (L x e) = 0) → ∑ e, η e (d e) = 0 := by
  constructor
  · rintro ⟨x, rfl⟩ η hη; exact hη x
  · intro h
    rw [mem_range_iff_forall_dual]
    intro φ hφ
    obtain ⟨η, hηφ⟩ := exists_dualFamily φ
    rw [← hηφ]
    exact h η fun x => (hηφ (L x)).trans (hφ x)

end Duality

/-! ## PIECE B -/

section Handshake

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
variable {M : Type*} [AddCommMonoid M]

/-- A finite **multigraph**: each edge carries an ordered pair of endpoints.
The ordering is auxiliary (the local order of Lemma 2.2's gauge); nothing below
depends on it. Parallel edges and loops are allowed. -/
structure Multigraph (V E : Type*) where
  /-- first endpoint -/ fst : E → V
  /-- second endpoint -/ snd : E → V

variable (G : Multigraph V E)

/-- `e` is incident to `v`. -/
def Inc (v : V) (e : E) : Prop := G.fst e = v ∨ G.snd e = v

instance (v : V) (e : E) : Decidable (Inc G v e) := by unfold Inc; infer_instance

/-- The sum of `w` over the edges at `v`, **counted with multiplicity**: a loop at
`v` contributes twice.  This is the incidence sum `∑_{e ∋ v} w e` of Lemma 2.2. -/
def vertexSum (w : E → M) (v : V) : M :=
  ∑ e, ((if G.fst e = v then w e else 0) + (if G.snd e = v then w e else 0))

/-- The incidence sum at `v` of a weight that may itself depend on `v`
(the Lemma 2.2 *gauge* `g v e` is exactly such a weight). -/
def vertexSum' (w : V → E → M) (v : V) : M :=
  ∑ e, ((if G.fst e = v then w v e else 0) + (if G.snd e = v then w v e else 0))

/-- **Incidence exchange.**  Summing a vertex-dependent weight over all
vertex-incidences regroups it as a sum over edges of its two endpoint values:
`∑_v ∑_{e ∋ v} w v e = ∑_e (w (fst e) e + w (snd e) e)`.
This is the step `∑_e η_e(d_e) = ∑_v ∑_{e∋v} η_e(g v e)` of Lemma 2.2, read
right to left. -/
theorem sum_vertexSum' (w : V → E → M) :
    ∑ v, vertexSum' G w v = ∑ e, (w (G.fst e) e + w (G.snd e) e) := by
  simp only [vertexSum']
  rw [Finset.sum_comm]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- **Handshake lemma, weighted form.**  Summing any edge weight over all
vertex-incidences counts each edge exactly twice:
`∑_v ∑_{e ∋ v} w e = 2 • ∑_e w e`. -/
theorem sum_vertexSum (w : E → M) :
    ∑ v, vertexSum G w v = 2 • ∑ e, w e := by
  have : vertexSum G w = vertexSum' G (fun _ => w) := rfl
  rw [this, sum_vertexSum', two_nsmul]
  exact Finset.sum_add_distrib

/-- The degree of `v`: incidences, so a loop counts twice. -/
def degree (v : V) : ℕ := vertexSum G (fun _ => 1) v

/-- **Classical handshake lemma for multigraphs**: `∑_v deg v = 2 * |E|`.
(Mathlib's `SimpleGraph.sum_degrees_eq_twice_card_edges` is the simple-graph
case; this is the multigraph case, and the weighted `sum_vertexSum` above is
what Lemma 2.2 actually consumes.) -/
theorem sum_degrees_eq_two_mul_card_edges :
    ∑ v, degree G v = 2 * Fintype.card E := by
  simp only [degree]
  rw [sum_vertexSum]
  simp [Finset.card_univ, two_nsmul, two_mul]

/-- **The step Lemma 2.2 needs**: over `𝔽₂` the total vertex-incidence sum
vanishes, because every edge is counted at both of its endpoints. -/
theorem sum_vertexSum_eq_zero_two (w : E → ZMod 2) :
    ∑ v, vertexSum G w v = 0 := by
  rw [sum_vertexSum, two_nsmul]
  exact CharTwo.add_self_eq_zero _

/-- In a **loopless** multigraph the multiplicity-counted incidence sum is the
honest sum over the set of edges incident to `v`. -/
theorem vertexSum_eq_filter_sum (hG : ∀ e, G.fst e ≠ G.snd e) (w : E → M) (v : V) :
    vertexSum G w v = ∑ e ∈ Finset.univ.filter (Inc G v), w e := by
  rw [vertexSum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases h1 : G.fst e = v
  · have h2 : G.snd e ≠ v := fun h => hG e (h1.trans h.symm)
    simp [Inc, h1, h2]
  · by_cases h2 : G.snd e = v <;> simp [Inc, h1, h2]

end Handshake

/-! ## GLUE: the Lemma 2.2 system, and condition (5) -/

section System

variable {V E K Γ : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  [Field K] [AddCommGroup Γ] [Module K Γ]
variable (G : Multigraph V E) (f : E → Γ)

/-- The linear map of Lemma 2.2:
`L (t, ε)_e = t_u + t_v + ε_e • f e` for `e = uv`.  Unknowns `t : V → Γ`
(vertex potentials) and `ε : E → K` (edge signs). -/
def Lmap : ((V → Γ) × (E → K)) →ₗ[K] (E → Γ) where
  toFun p := fun e => p.1 (G.fst e) + p.1 (G.snd e) + p.2 e • f e
  map_add' p q := by
    funext e; simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul]; abel
  map_smul' c p := by
    funext e
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_add, smul_smul,
      RingHom.id_apply, smul_eq_mul]

@[simp] lemma Lmap_apply (p : (V → Γ) × (E → K)) (e : E) :
    Lmap G f p e = p.1 (G.fst e) + p.1 (G.snd e) + p.2 e • f e := rfl

/-- Applying the incidence sum of a family of functionals to a vector. -/
lemma vertexSum_apply (η : E → Dual K Γ) (t : V → Γ) (v : V) :
    vertexSum' G (fun v e => η e (t v)) v = (vertexSum G η v) (t v) := by
  simp only [vertexSum, vertexSum', LinearMap.sum_apply, LinearMap.add_apply]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases h1 : G.fst e = v <;> by_cases h2 : G.snd e = v <;> simp [h1, h2]

/-- **Condition (5).**  A dual family `η` annihilates the whole image of `L`
exactly when (a) `η_e` kills the flow value `f e` on every edge, and (b) the
incidence sum of the `η`'s at every vertex is the zero functional.

This is the "since `t` and `ε` are independent" step of the paper. -/
theorem dualFamily_annihilates_iff (η : E → Dual K Γ) :
    (∀ p : (V → Γ) × (E → K), ∑ e, η e (Lmap G f p e) = 0) ↔
      ((∀ e, η e (f e) = 0) ∧ (∀ v, vertexSum G η v = 0)) := by
  constructor
  · intro h
    constructor
    · -- test with t = 0, ε = indicator of e₀
      intro e₀
      have h0 := h (0, Pi.single e₀ (1 : K))
      have hs : ∀ e : E, η e (Lmap G f (0, Pi.single e₀ (1 : K)) e)
          = if e = e₀ then η e₀ (f e₀) else 0 := by
        intro e
        simp only [Lmap_apply, Pi.zero_apply, zero_add, add_zero, Pi.single_apply]
        by_cases he : e = e₀ <;> simp [he]
      rw [Finset.sum_congr rfl fun e _ => hs e, Finset.sum_ite_eq'] at h0
      simpa using h0
    · -- test with ε = 0, t = the single potential `s` at `v`
      intro v
      ext s
      set t0 : V → Γ := Pi.single v s with ht0
      have h0 := h (t0, (0 : E → K))
      have hs : ∀ e : E, η e (Lmap G f (t0, (0 : E → K)) e)
          = (if G.fst e = v then η e s else 0) + (if G.snd e = v then η e s else 0) := by
        intro e
        simp only [Lmap_apply, Pi.zero_apply, zero_smul, add_zero, map_add, ht0,
          Pi.single_apply]
        by_cases h1 : G.fst e = v <;> by_cases h2 : G.snd e = v <;> simp [h1, h2]
      rw [Finset.sum_congr rfl fun e _ => hs e] at h0
      show (vertexSum G η v) s = 0
      simp only [vertexSum, LinearMap.sum_apply, LinearMap.add_apply]
      rw [← h0]
      refine Finset.sum_congr rfl fun e _ => ?_
      by_cases h1 : G.fst e = v <;> by_cases h2 : G.snd e = v <;> simp [h1, h2]
  · rintro ⟨hf, hv⟩ ⟨t, ε⟩
    have key : ∑ e, η e (Lmap G f (t, ε) e)
        = ∑ e, (η e (t (G.fst e)) + η e (t (G.snd e))) := by
      refine Finset.sum_congr rfl fun e _ => ?_
      simp only [Lmap_apply, map_add, map_smul, hf e, smul_zero, add_zero]
    rw [key, ← sum_vertexSum' G (fun v e => η e (t v))]
    refine Finset.sum_eq_zero fun v _ => ?_
    rw [vertexSum_apply, hv v]
    rfl

/-- **Lemma 2.2, reduced.**  The system `L (t, ε) = d` is solvable as soon as
every dual family satisfying condition (5) pairs to zero with `d`.  Everything
graph-theoretic and everything `𝔽₂³`-specific is now isolated in the hypothesis
`h`, which is what `cdc_crux` + the handshake lemma discharge. -/
theorem lemma22_reduction {V E K Γ : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    [DecidableEq E] [Field K] [AddCommGroup Γ] [Module K Γ]
    (G : Multigraph V E) (f : E → Γ) (d : E → Γ)
    (h : ∀ η : E → Dual K Γ, (∀ e, η e (f e) = 0) → (∀ v, vertexSum G η v = 0) →
      ∑ e, η e (d e) = 0) :
    ∃ (t : V → Γ) (ε : E → K), ∀ e : E,
      t (G.fst e) + t (G.snd e) + ε e • f e = d e := by
  have hd : d ∈ LinearMap.range (Lmap G f (K := K)) := by
    rw [mem_range_iff_forall_dualFamily]
    intro η hη
    obtain ⟨h1, h2⟩ := (dualFamily_annihilates_iff G f η).1 hη
    exact h η h1 h2
  obtain ⟨⟨t, ε⟩, hp⟩ := hd
  exact ⟨t, ε, fun e => congrFun hp e⟩

end System

/-! ## BRIDGE to `cdc_crux`: `Γ = 𝔽₂³` is self-dual via `dot`

`cdc_crux` (in `verification/cdc_core.lean`) is stated with the concrete pairing
`dot : G3 → G3 → 𝔽₂`, whereas the duality criterion above produces an abstract
`η : E → Dual 𝔽₂ G3`.  These lemmas identify the two: every functional on `G3`
is `dot a` for a unique `a`, so a dual family *is* a `G3`-valued edge labelling
and `cdc_crux` applies to it verbatim. -/

section SelfDual

/-- `Γ = 𝔽₂³` (same definition as `cdc_core.lean`). -/
abbrev G3 := ZMod 2 × ZMod 2 × ZMod 2

/-- the standard 𝔽₂-bilinear pairing on `𝔽₂³` (same definition as `cdc_core.lean`) -/
def dot (a b : G3) : ZMod 2 := a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2

/-- `dot a` as a linear functional. -/
def dotL (a : G3) : Dual (ZMod 2) G3 where
  toFun b := dot a b
  map_add' b c := by simp only [dot, Prod.fst_add, Prod.snd_add]; ring
  map_smul' c b := by
    simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]; ring

@[simp] lemma dotL_apply (a b : G3) : dotL a b = dot a b := rfl

/-- **`𝔽₂³` is self-dual**: every functional is `dot a`.  Hence a dual family
`η : E → Dual 𝔽₂ G3` is the same thing as an edge labelling `E → G3`, which is
the form `cdc_crux` consumes. -/
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

/-- `dotL` is additive, so `Dual`-level hypotheses transfer to `dot`-level ones. -/
@[simp] lemma dotL_add (a b : G3) : dotL (a + b) = dotL a + dotL b := by
  refine LinearMap.ext fun c => ?_
  simp only [dotL, dot, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply,
    Prod.fst_add, Prod.snd_add]
  ring

@[simp] lemma dotL_zero : dotL 0 = 0 := by
  refine LinearMap.ext fun c => ?_
  simp [dotL, dot]

end SelfDual

/-! ## Axiom audit -- every result must show exactly
`[propext, Classical.choice, Quot.sound]`. -/

#print axioms mem_range_iff_forall_dual
#print axioms exists_dualFamily
#print axioms mem_range_iff_forall_dualFamily
#print axioms sum_vertexSum'
#print axioms sum_vertexSum
#print axioms sum_degrees_eq_two_mul_card_edges
#print axioms sum_vertexSum_eq_zero_two
#print axioms vertexSum_eq_filter_sum
#print axioms Lmap
#print axioms vertexSum_apply
#print axioms dualFamily_annihilates_iff
#print axioms lemma22_reduction
#print axioms dotL
#print axioms exists_dot_eq
#print axioms dotL_add
#print axioms dotL_zero

end CDC
