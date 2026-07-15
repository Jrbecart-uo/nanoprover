import CDCProof.Core
import CDCProof.Multigraph
import CDCProof.Duality
import CDCProof.Glue

/-!
# CDCProof.Main — the capstone

`cdc_of_cubicFlow`: **every cubic flow graph has a cycle double cover.**

A `CubicFlow` is a loopless cubic multigraph with a chosen local edge order and a
nowhere-zero `𝔽₂³`-flow.  By the 8-flow theorem *(cited, not formalized)* every
bridgeless graph, reduced to the cubic case *(Jaeger, cited)*, carries such a
flow — so this is the whole of the paper's novel step 3, assembled end to end
and kernel-checked.

Chain:
  `lemma22_reduction` (solve `t_u + t_v + ε_e f_e = d_e`, via `pairing_vanishes_cubic`)
  → build `P_e = {t_v + g(v,e), t_v + g(v,e) + f_e}`
  → `|P_e| = 2` (flow nowhere-zero) and condition (1) (`cdc_local`)
  → `lemma21`  →  a cycle double cover.
-/

open Module CDCProof

namespace CDCProof

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- the flow graph as the duality-side `Multigraph` -/
def CF.CubicFlow.toD (G : CF.CubicFlow V E) : D.Multigraph V E := ⟨G.fst, G.snd⟩

/-- the flow graph as the `lemma21`-side `MG` -/
def CF.CubicFlow.toMG (G : CF.CubicFlow V E) : G21.MG V E := ⟨G.fst, G.snd, G.loopless⟩

variable (G : CF.CubicFlow V E)

/-- `D.vertexSum` at a cubic vertex collapses to its three incident edges. -/
theorem vsum_collapse (η : E → Dual (ZMod 2) G3) (v : V) :
    D.vertexSum G.toD η v = η (G.ea v) + η (G.eb v) + η (G.ec v) := by
  unfold D.vertexSum CF.CubicFlow.toD
  rw [show (∑ e, ((if G.fst e = v then η e else 0) + (if G.snd e = v then η e else 0)))
        = ∑ e ∈ Finset.univ.filter (fun e => G.fst e = v ∨ G.snd e = v), η e from ?_,
      G.hinc v, Finset.sum_insert (by simp [G.hab v, G.hac v]),
      Finset.sum_insert (by simp [G.hbc v]), Finset.sum_singleton, add_assoc]
  · rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    by_cases h1 : G.fst e = v <;> by_cases h2 : G.snd e = v <;> simp [h1, h2]
    exact absurd (h1.trans h2.symm) (G.loopless e)

/-- the datum `d_e = g(fst e, e) + g(snd e, e)`. -/
def dEdge (e : E) : G3 := CF.cdcGauge G (G.fst e) e + CF.cdcGauge G (G.snd e) e

/-- **Lemma 2.2, solved for `G`.** The system has a solution. -/
theorem exists_solution :
    ∃ (t : V → G3) (ε : E → ZMod 2), ∀ e : E,
      t (G.fst e) + t (G.snd e) + ε e • G.f e = dEdge G e := by
  refine D.lemma22_reduction G.toD G.f (dEdge G) (fun η hf hv => ?_)
  -- hv : ∀ v, D.vertexSum G.toD η v = 0  ⟹  the cubic condition (5)
  have h5v : ∀ v, η (G.ea v) + η (G.eb v) + η (G.ec v) = 0 := by
    intro v; rw [← vsum_collapse G η v]; exact hv v
  exact CF.pairing_vanishes_cubic G η hf h5v

/-- Two 2-element sets `{a, a+k}` and `{b, b+k}` coincide when `a = b` or
`a = b + k` (both endpoints of an edge assign it the same `P`). -/
theorem pair_eq (a b k : G3) (h : a = b ∨ a = b + k) :
    ({a, a + k} : Finset G3) = {b, b + k} := by
  rcases h with rfl | rfl
  · rfl
  · rw [show b + k + k = b from by rw [add_assoc, CF.add_self_zero, add_zero]]
    exact Finset.pair_comm _ _

theorem mem_pair (x k s : G3) : s ∈ ({x, x + k} : Finset G3) ↔ (s = x ∨ s = x + k) := by
  simp [Finset.mem_insert, Finset.mem_singleton]

set_option synthInstance.maxSize 1000 in
set_option maxRecDepth 40000 in
/-- **Condition (1), the finite core.** At a cubic vertex the three local sets
`{t,t+x}`, `{t+x,t+x+y}`, `{t,t+(x+y)}` contain any `s` in 0 or 2 of them
(`x,y` nonzero, distinct). Decided over `𝔽₂³`. -/
theorem local_02 : ∀ (tv x y s : G3), x ≠ 0 → y ≠ 0 → x ≠ y →
    ((if s = tv ∨ s = tv + x then 1 else 0)
   + (if s = tv + x ∨ s = tv + x + y then 1 else 0)
   + (if s = tv ∨ s = tv + (x + y) then 1 else 0) : ℕ) = 0 ∨
    ((if s = tv ∨ s = tv + x then 1 else 0)
   + (if s = tv + x ∨ s = tv + x + y then 1 else 0)
   + (if s = tv ∨ s = tv + (x + y) then 1 else 0) : ℕ) = 2 := by decide

/-- **The capstone: every cubic flow graph has a cycle double cover.** -/
theorem cdc_of_cubicFlow (G : CF.CubicFlow V E) :
    ∃ 𝒞 : Multiset (Finset E), G.toMG.IsCDC 𝒞 := by
  obtain ⟨t, ε, heq⟩ := exists_solution G
  set P : E → Finset G3 := fun e =>
    ({t (G.fst e) + CF.cdcGauge G (G.fst e) e,
      t (G.fst e) + CF.cdcGauge G (G.fst e) e + G.f e} : Finset G3) with hP
  have hcard : ∀ e, (P e).card = 2 := by
    intro e
    rw [hP]; dsimp only
    rw [Finset.card_insert_of_notMem, Finset.card_singleton]
    simp only [Finset.mem_singleton]
    intro h
    exact G.fnz e (add_left_cancel (a := t (G.fst e) + CF.cdcGauge G (G.fst e) e)
      (by rw [add_zero]; exact h.symm))
  have Pat : ∀ e (v : V), (v = G.fst e ∨ v = G.snd e) →
      P e = {t v + CF.cdcGauge G v e, t v + CF.cdcGauge G v e + G.f e} := by
    intro e v hv
    rcases hv with rfl | rfl
    · rw [hP]
    · rw [hP]; dsimp only
      apply pair_eq
      rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (ε e) with h0 | h1
      · left
        have h := heq e; unfold dEdge at h; rw [h0, zero_smul, add_zero] at h
        have hab0 : (t (G.fst e) + CF.cdcGauge G (G.fst e) e)
                  + (t (G.snd e) + CF.cdcGauge G (G.snd e) e) = 0 := by
          rw [show (t (G.fst e) + CF.cdcGauge G (G.fst e) e)
                 + (t (G.snd e) + CF.cdcGauge G (G.snd e) e)
                 = (t (G.fst e) + t (G.snd e))
                 + (CF.cdcGauge G (G.fst e) e + CF.cdcGauge G (G.snd e) e) from by abel,
              h, CF.add_self_zero]
        rw [eq_neg_of_add_eq_zero_left hab0, CF.neg_self]
      · right
        have h := heq e; unfold dEdge at h; rw [h1, one_smul] at h
        have hab : (t (G.fst e) + CF.cdcGauge G (G.fst e) e)
                 + ((t (G.snd e) + CF.cdcGauge G (G.snd e) e) + G.f e) = 0 := by
          rw [show (t (G.fst e) + CF.cdcGauge G (G.fst e) e)
                 + ((t (G.snd e) + CF.cdcGauge G (G.snd e) e) + G.f e)
                 = ((t (G.fst e) + t (G.snd e)) + G.f e)
                 + (CF.cdcGauge G (G.fst e) e + CF.cdcGauge G (G.snd e) e) from by abel,
              h, CF.add_self_zero]
        rw [eq_neg_of_add_eq_zero_left hab, CF.neg_self]
  have hgauge : ∀ (v : V),
      CF.cdcGauge G v (G.ea v) = 0 ∧ CF.cdcGauge G v (G.eb v) = G.f (G.ea v)
      ∧ CF.cdcGauge G v (G.ec v) = 0 := fun v =>
    ⟨by unfold CF.cdcGauge; rw [if_neg (G.hab v)],
     by unfold CF.cdcGauge; rw [if_pos rfl],
     by unfold CF.cdcGauge; rw [if_neg (G.hbc v).symm]⟩
  have hloc : ∀ (v : V) (s : G3),
      G.toMG.deg (Finset.univ.filter (fun e => s ∈ P e)) v = 0 ∨
      G.toMG.deg (Finset.univ.filter (fun e => s ∈ P e)) v = 2 := by
    intro v s
    have hInc : ∀ e, G.toMG.Inc e v ↔ (G.fst e = v ∨ G.snd e = v) := by
      intro e; unfold CF.CubicFlow.toMG G21.MG.Inc
      constructor <;> (rintro (h | h)) <;> [exact Or.inl h.symm; exact Or.inr h.symm;
        exact Or.inl h.symm; exact Or.inr h.symm]
    -- ea, eb, ec are incident to v
    have hincv : ∀ w ∈ ({G.ea v, G.eb v, G.ec v} : Finset E),
        v = G.fst w ∨ v = G.snd w := by
      intro w hw
      rw [← G.hinc v, Finset.mem_filter] at hw
      exact hw.2.imp Eq.symm Eq.symm
    have iea := hincv (G.ea v) (by simp)
    have ieb := hincv (G.eb v) (by simp)
    have iec := hincv (G.ec v) (by simp)
    obtain ⟨gea, geb, gec⟩ := hgauge v
    have hxy : G.f (G.ea v) ≠ G.f (G.eb v) := by
      intro hh; apply G.fnz (G.ec v)
      have hc := G.fcons v; rw [hh, CF.add_self_zero, zero_add] at hc; exact hc
    have hz : G.f (G.ec v) = G.f (G.ea v) + G.f (G.eb v) := by
      have h3 : -(G.f (G.ec v)) = G.f (G.ea v) + G.f (G.eb v) :=
        neg_eq_of_add_eq_zero_left (G.fcons v)
      rw [← h3]; exact (CF.neg_self _).symm
    -- membership at each incident edge, gauge reduced (as if-value equalities)
    have mea : (if s ∈ P (G.ea v) then (1:ℕ) else 0)
        = (if s = t v ∨ s = t v + G.f (G.ea v) then 1 else 0) := by
      rw [Pat (G.ea v) v iea]; simp only [gea, add_zero]
      exact if_congr (by simp [Finset.mem_insert, Finset.mem_singleton]) rfl rfl
    have meb : (if s ∈ P (G.eb v) then (1:ℕ) else 0)
        = (if s = t v + G.f (G.ea v) ∨ s = t v + G.f (G.ea v) + G.f (G.eb v) then 1 else 0) := by
      rw [Pat (G.eb v) v ieb, geb]
      exact if_congr (by simp [Finset.mem_insert, Finset.mem_singleton]) rfl rfl
    have mec : (if s ∈ P (G.ec v) then (1:ℕ) else 0)
        = (if s = t v ∨ s = t v + (G.f (G.ea v) + G.f (G.eb v)) then 1 else 0) := by
      rw [Pat (G.ec v) v iec]; simp only [gec, add_zero, hz]
      exact if_congr (by simp [Finset.mem_insert, Finset.mem_singleton]) rfl rfl
    -- deg = filter over the three incident edges
    have hmem3 : ∀ e, e ∈ ({G.ea v, G.eb v, G.ec v} : Finset E)
        ↔ (G.fst e = v ∨ G.snd e = v) := by
      intro e; rw [← G.hinc v, Finset.mem_filter]; simp
    have hfilter : (Finset.univ.filter (fun e => s ∈ P e)).filter (G.toMG.Inc · v)
        = ({G.ea v, G.eb v, G.ec v} : Finset E).filter (fun e => s ∈ P e) := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hInc e, hmem3 e]
      tauto
    unfold G21.MG.deg
    rw [hfilter, Finset.card_filter, Finset.sum_insert (by simp [G.hab v, G.hac v]),
        Finset.sum_insert (by simp [G.hbc v]), Finset.sum_singleton,
        mea, meb, mec, ← add_assoc]
    exact local_02 (t v) (G.f (G.ea v)) (G.f (G.eb v)) s (G.fnz _) (G.fnz _) hxy
  exact G.toMG.lemma21 P hcard hloc

end CDCProof

#print axioms cdc_of_cubicFlow
