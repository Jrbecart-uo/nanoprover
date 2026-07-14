import Mathlib

/-!
# CDC: the assembly — Lemma 2.2 reduced to a single vertex-local fact

This closes the chain between the pieces proved elsewhere:

* `verification/cdc_core.lean`    — `cdc_crux` (the vertex parity identity), `cdc_local`
* `verification/cdc_lemma21.lean` — `lemma21` : the family `P` ⟹ a cycle double cover
* `verification/cdc_lemma22.lean` — duality, handshake, `lemma22_reduction`

The argument of Lemma 2.2, in three moves:

    ∑_e η_e(d_e)                                   -- d_e = g(u,e) + g(v,e)
      = ∑_v ∑_{e∋v} η_e(g v e)                     -- INCIDENCE EXCHANGE
      = ∑_v ∑_{e∋v} nz(η_e)                        -- cdc_crux, at each vertex
      = 2 · ∑_e nz(η_e)  =  0  in 𝔽₂               -- HANDSHAKE (each edge twice)

Move 1 is `sum_vertexSum'`, move 3 is `sum_vertexSum`; both are proved. Move 2 is
the *only* place the cubic structure, the gauge, and the flow enter — and it is
exactly `cdc_crux` applied at one vertex.

So the theorem below discharges **everything** in Lemma 2.2 except that
vertex-local step, which is isolated as the hypothesis `hlocal`.  Stated plainly:
the global argument is finished; what remains is to build the cubic-with-local-order
structure and feed each vertex to `cdc_crux`.
-/

namespace CDC

open Finset Module

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- Finite multigraph (same model as `cdc_lemma22.lean`). -/
structure Multigraph (V E : Type*) where
  fst : E → V
  snd : E → V

variable (G : Multigraph V E)
variable {M : Type*} [AddCommMonoid M]

/-- incidence sum of an edge weight; a loop at `v` counts twice -/
def vertexSum (w : E → M) (v : V) : M :=
  ∑ e, ((if G.fst e = v then w e else 0) + (if G.snd e = v then w e else 0))

/-- incidence sum of a *vertex-dependent* weight — the gauge `g v e` is one -/
def vertexSum' (w : V → E → M) (v : V) : M :=
  ∑ e, ((if G.fst e = v then w v e else 0) + (if G.snd e = v then w v e else 0))

/-- **Incidence exchange.** `∑_v ∑_{e∋v} w v e = ∑_e (w (fst e) e + w (snd e) e)`. -/
theorem sum_vertexSum' (w : V → E → M) :
    ∑ v, vertexSum' G w v = ∑ e, (w (G.fst e) e + w (G.snd e) e) := by
  simp only [vertexSum']
  rw [Finset.sum_comm]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- **Handshake.** `∑_v ∑_{e∋v} w e = 2 • ∑_e w e` — every edge counted twice. -/
theorem sum_vertexSum (w : E → M) :
    ∑ v, vertexSum G w v = 2 • ∑ e, w e := by
  have h : vertexSum G w = vertexSum' G (fun _ => w) := rfl
  rw [h, sum_vertexSum', two_nsmul]
  exact Finset.sum_add_distrib

/-- In `𝔽₂` the handshake sum vanishes: every edge is counted at both ends. -/
theorem sum_vertexSum_eq_zero_two (w : E → ZMod 2) :
    ∑ v, vertexSum G w v = 0 := by
  rw [sum_vertexSum]
  have h : (2 : ℕ) • (∑ e, w e) = (2 : ZMod 2) * (∑ e, w e) := by
    rw [nsmul_eq_mul]; norm_num
  have h2 : (2 : ZMod 2) = 0 := rfl
  rw [h, h2, zero_mul]

/-- **The global half of Lemma 2.2.**

Assume the gauge presentation `d e = g (fst e) e + g (snd e) e`, and assume the
vertex-local fact `hlocal`: at every vertex the gauge sum of `η` equals the
**parity of how many incident `η_e` are nonzero**.  (That is precisely
`cdc_crux`, once the cubic structure and the flow are in hand.)

Then the pairing `∑_e η_e(d_e)` vanishes — which is exactly the hypothesis that
`lemma22_reduction` needs, so the linear system of Lemma 2.2 is solvable.

Everything here is graph-global: incidence exchange, then the handshake.  No
cubicity, no flow, no `𝔽₂³` — those live only inside `hlocal`. -/
theorem pairing_vanishes
    {Γ : Type*} [AddCommGroup Γ] [Module (ZMod 2) Γ]
    (f d : E → Γ) (g : V → E → Γ) (η : E → Dual (ZMod 2) Γ)
    (nz : E → ZMod 2)
    (hd : ∀ e, d e = g (G.fst e) e + g (G.snd e) e)
    (hlocal : ∀ v : V, vertexSum' G (fun v e => η e (g v e)) v
                     = vertexSum G nz v) :
    ∑ e, η e (d e) = 0 := by
  -- move 1: incidence exchange, read right-to-left
  have step1 : ∑ e, η e (d e) = ∑ v, vertexSum' G (fun v e => η e (g v e)) v := by
    rw [sum_vertexSum' G (fun v e => η e (g v e))]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [hd e, map_add]
  -- move 2: cdc_crux at each vertex   +   move 3: handshake
  rw [step1, Finset.sum_congr rfl (fun v _ => hlocal v), sum_vertexSum_eq_zero_two]

end CDC

#print axioms CDC.sum_vertexSum'
#print axioms CDC.sum_vertexSum
#print axioms CDC.sum_vertexSum_eq_zero_two
#print axioms CDC.pairing_vanishes
