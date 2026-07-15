import Mathlib
import CDCProof.Core
open Module

/-!
# CDCProof.Glue — the `CubicFlow` structure, `hlocal`, and `pairing_vanishes_cubic`

The vertex-local identity (`hlocal`) that `Duality.lemma22_reduction` consumes,
and its chaining through the handshake (`pairing_vanishes_cubic`).  Reuses the
`𝔽₂³` facts from `CDCProof.Core`.
-/

namespace CDCProof.CF
open CDCProof

/-! ## The cubic flow graph and the local step `hlocal` -/

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- incidence sum of a vertex-dependent weight (same as `cdc_assembly.lean`). -/
def vertexSum' (fst snd : E → V) {M : Type*} [AddCommMonoid M]
    (w : V → E → M) (v : V) : M :=
  ∑ e, ((if fst e = v then w v e else 0) + (if snd e = v then w v e else 0))

/-- **Incidence collapse.** At a loopless vertex whose incident edges are exactly
`{a, b, c}` (distinct), the incidence sum is `w v a + w v b + w v c`. -/
theorem vertexSum'_collapse (fst snd : E → V) {M : Type*} [AddCommMonoid M]
    (v : V) (w : V → E → M) (a b c : E)
    (hloop : ∀ e, fst e ≠ snd e)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hset : Finset.univ.filter (fun e => fst e = v ∨ snd e = v) = {a, b, c}) :
    vertexSum' fst snd w v = w v a + w v b + w v c := by
  unfold vertexSum'
  rw [show (∑ e, ((if fst e = v then w v e else 0) + (if snd e = v then w v e else 0)))
        = (∑ e ∈ Finset.univ.filter (fun e => fst e = v ∨ snd e = v), w v e) from ?_,
      hset, Finset.sum_insert (by simp [hab, hac]),
      Finset.sum_insert (by simp [hbc]), Finset.sum_singleton, add_assoc]
  · rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    by_cases h1 : fst e = v <;> by_cases h2 : snd e = v <;> simp [h1, h2]
    exact absurd (h1.trans h2.symm) (hloop e)

/-- A **cubic flow graph**: a loopless multigraph in which every vertex has a
chosen local order of its three incident edges, carrying a nowhere-zero
`𝔽₂³`-flow (conservation at each vertex; char 2, so the incident flows sum to 0). -/
structure CubicFlow (V E : Type*) [Fintype E] [DecidableEq V] [DecidableEq E] where
  fst : E → V
  snd : E → V
  loopless : ∀ e, fst e ≠ snd e
  ea : V → E          -- first incident edge (local order)
  eb : V → E          -- second
  ec : V → E          -- third
  hab : ∀ v, ea v ≠ eb v
  hac : ∀ v, ea v ≠ ec v
  hbc : ∀ v, eb v ≠ ec v
  hinc : ∀ v, Finset.univ.filter (fun e => fst e = v ∨ snd e = v)
              = {ea v, eb v, ec v}
  f : E → G3
  fnz : ∀ e, f e ≠ 0
  fcons : ∀ v, f (ea v) + f (eb v) + f (ec v) = 0     -- flow conservation

variable (G : CubicFlow V E)

/-- The cdcGauge: `f(ea v)` on `eb v`, and `0` on the other two incident edges.
This is the paper's `g(v,a)=0, g(v,b)=f(a), g(v,c)=0`. -/
def cdcGauge (v : V) (e : E) : G3 := if e = G.eb v then G.f (G.ea v) else 0

/-- `-a = a` and `a + a = 0` in a `ZMod 2`-module. -/
lemma neg_self {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] (a : W) : -a = a := by
  rw [← neg_one_smul (ZMod 2) a, show (-1 : ZMod 2) = 1 by decide, one_smul]

lemma add_self_zero {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] (a : W) :
    a + a = 0 := by nth_rewrite 1 [← neg_self a]; exact neg_add_cancel a

/-- **The vertex-local identity — this is `hlocal`.**

For a dual family `η` satisfying condition (5) at `v` (each `η_e` kills `f e`, and
the three incident `η` sum to zero), the cdcGauge sum equals the parity count:
`∑_{e∋v} η_e(g v e) = ∑_{e∋v} nzD(η_e)`.

Exactly the hypothesis `pairing_vanishes` (in `cdc_assembly.lean`) consumes.  This
is the one place the cubic structure, the cdcGauge, the flow, and `cdc_crux` meet. -/
theorem hlocal (η : E → Dual (ZMod 2) G3)
    (h5f : ∀ e, η e (G.f e) = 0)
    (h5v : ∀ v, η (G.ea v) + η (G.eb v) + η (G.ec v) = 0) (v : V) :
    vertexSum' G.fst G.snd (fun v e => η e (cdcGauge G v e)) v
      = vertexSum' G.fst G.snd (fun _ e => nzD (η e)) v := by
  rw [vertexSum'_collapse G.fst G.snd v _ (G.ea v) (G.eb v) (G.ec v)
        G.loopless (G.hab v) (G.hac v) (G.hbc v) (G.hinc v),
      vertexSum'_collapse G.fst G.snd v _ (G.ea v) (G.eb v) (G.ec v)
        G.loopless (G.hab v) (G.hac v) (G.hbc v) (G.hinc v)]
  have gea : cdcGauge G v (G.ea v) = 0 := by unfold cdcGauge; rw [if_neg (G.hab v)]
  have geb : cdcGauge G v (G.eb v) = G.f (G.ea v) := by unfold cdcGauge; rw [if_pos rfl]
  have gec : cdcGauge G v (G.ec v) = 0 := by unfold cdcGauge; rw [if_neg (G.hbc v).symm]
  rw [gea, geb, gec, map_zero, map_zero, zero_add, add_zero]
  set x := G.f (G.ea v) with hxdef
  set y := G.f (G.eb v) with hydef
  have hx : x ≠ 0 := G.fnz _
  have hy : y ≠ 0 := G.fnz _
  -- char 2: x + y = f(ec)
  have hxy_sum : x + y = G.f (G.ec v) := by
    have h2 : x + y + G.f (G.ec v) = 0 := G.fcons v
    rw [eq_neg_of_add_eq_zero_left h2, neg_self]
  have hxy : x ≠ y := fun h => G.fnz (G.ec v) (by rw [← hxy_sum, h, add_self_zero])
  -- char 2: η(ea) + η(eb) = η(ec)
  have hηc : η (G.ea v) + η (G.eb v) = η (G.ec v) := by
    have hsum := h5v v
    have h' : η (G.ea v) + η (G.eb v) = - η (G.ec v) := eq_neg_of_add_eq_zero_left hsum
    rw [h', neg_self]
  rw [show nzD (η (G.ec v)) = nzD (η (G.ea v) + η (G.eb v)) by rw [hηc]]
  refine cdc_crux_dual x y (η (G.ea v)) (η (G.eb v)) hx hy hxy ?_ ?_ ?_
  · exact h5f (G.ea v)
  · exact h5f (G.eb v)
  · rw [hηc, hxy_sum]; exact h5f (G.ec v)


/-! ## Chaining `hlocal` through the handshake: the pairing vanishes -/

/-- incidence sum of an edge weight (loop counts twice) -/
def vertexSum (fst snd : E → V) {M : Type*} [AddCommMonoid M] (w : E → M) (v : V) : M :=
  ∑ e, ((if fst e = v then w e else 0) + (if snd e = v then w e else 0))

/-- incidence exchange, edge-weight form -/
theorem sum_vertexSum' (fst snd : E → V) {M : Type*} [AddCommMonoid M]
    (w : V → E → M) :
    ∑ v, vertexSum' fst snd w v = ∑ e, (w (fst e) e + w (snd e) e) := by
  simp only [vertexSum']
  rw [Finset.sum_comm]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- handshake: each edge counted at both ends, so over `ZMod 2` the total is `0` -/
theorem sum_vertexSum_zero (fst snd : E → V) (w : E → ZMod 2) :
    ∑ v, vertexSum fst snd w v = 0 := by
  have h : vertexSum fst snd w = vertexSum' fst snd (fun _ => w) := rfl
  rw [h, sum_vertexSum']
  have hstep : ∑ e, ((fun _ : V => w) (fst e) e + (fun _ : V => w) (snd e) e)
      = 2 • ∑ e, w e := by
    simp only [two_nsmul, ← Finset.sum_add_distrib]
  rw [hstep]
  have h2 : (2 : ℕ) • (∑ e, w e) = (2 : ZMod 2) * ∑ e, w e := by
    rw [nsmul_eq_mul]; norm_num
  rw [h2, show (2 : ZMod 2) = 0 from rfl, zero_mul]

/-- **The pairing vanishes for a cubic flow graph.**

`d e := g(fst e, e) + g(snd e, e)` is the paper's edge datum.  For any dual family
`η` satisfying condition (5), `∑_e η_e(d_e) = 0`.  This is exactly the hypothesis
that `lemma22_reduction` (in `cdc_lemma22.lean`) consumes to conclude the linear
system of Lemma 2.2 is solvable — so every `CubicFlow` admits the family `P`, and
`lemma21` then delivers the cycle double cover.

Chain: incidence exchange → `hlocal` at every vertex → handshake. -/
theorem pairing_vanishes_cubic (η : E → Dual (ZMod 2) G3)
    (h5f : ∀ e, η e (G.f e) = 0)
    (h5v : ∀ v, η (G.ea v) + η (G.eb v) + η (G.ec v) = 0) :
    ∑ e, η e (cdcGauge G (G.fst e) e + cdcGauge G (G.snd e) e) = 0 := by
  have step1 : ∑ e, η e (cdcGauge G (G.fst e) e + cdcGauge G (G.snd e) e)
      = ∑ v, vertexSum' G.fst G.snd (fun v e => η e (cdcGauge G v e)) v := by
    rw [sum_vertexSum' G.fst G.snd (fun v e => η e (cdcGauge G v e))]
    exact Finset.sum_congr rfl (fun e _ => by rw [map_add])
  rw [step1, Finset.sum_congr rfl (fun v _ => hlocal G η h5f h5v v)]
  have h2 : ∀ v, vertexSum' G.fst G.snd (fun _ e => nzD (η e)) v
      = vertexSum G.fst G.snd (fun e => nzD (η e)) v := fun v => rfl
  rw [Finset.sum_congr rfl (fun v _ => h2 v), sum_vertexSum_zero]


end CDCProof.CF
