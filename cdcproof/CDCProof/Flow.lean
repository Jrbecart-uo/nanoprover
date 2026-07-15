import CDCProof.Main

/-!
# CDCProof.Flow — the 8-flow reduction

A nowhere-zero `𝔽₂³`-flow is exactly **three even subgraphs covering every edge**:
each coordinate `wᵢ : E → 𝔽₂` is the indicator of an even subgraph (all degrees
even ⇔ the incidence sum is `0` in `𝔽₂`), which is precisely an `𝔽₂`-flow; the
triple is nowhere-zero iff every edge lies in some `wᵢ` (covering).

`cdc_of_covering` feeds this into `cdc_of_cubicFlow`, so the capstone's abstract
flow hypothesis is replaced by the concrete combinatorial one.  What remains of
the 8-flow theorem is then a pure statement about cubic graphs — *every
bridgeless cubic graph has three even subgraphs covering its edges* — with no
`𝔽₂³` or flow arithmetic left in it.
-/

open Module CDCProof

namespace CDCProof

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- **The 8-flow reduction.**  A cubic graph with a local edge order, together
with three "even, covering" edge indicators `w : Fin 3 → E → 𝔽₂`
(`heven`: even at every vertex; `hcover`: every edge carried by some `wᵢ`), has a
cycle double cover.

The three evenness conditions are `𝔽₂`-flow conservation coordinatewise; covering
is nowhere-zero-ness.  Everything else is `cdc_of_cubicFlow`. -/
theorem cdc_of_covering
    (fst snd : E → V) (loopless : ∀ e, fst e ≠ snd e)
    (ea eb ec : V → E)
    (hab : ∀ v, ea v ≠ eb v) (hac : ∀ v, ea v ≠ ec v) (hbc : ∀ v, eb v ≠ ec v)
    (hinc : ∀ v, Finset.univ.filter (fun e => fst e = v ∨ snd e = v)
                = {ea v, eb v, ec v})
    (w : Fin 3 → E → ZMod 2)
    (heven : ∀ (v : V) (i : Fin 3), w i (ea v) + w i (eb v) + w i (ec v) = 0)
    (hcover : ∀ e, ∃ i, w i e ≠ 0) :
    ∃ 𝒞 : Multiset (Finset E),
      ({fst := fst, snd := snd, loopless := loopless} : G21.MG V E).IsCDC 𝒞 := by
  -- the flow: each edge's triple of indicators
  let f : E → G3 := fun e => (w 0 e, w 1 e, w 2 e)
  have fnz : ∀ e, f e ≠ 0 := by
    intro e hfe
    obtain ⟨i, hi⟩ := hcover e
    have : w 0 e = 0 ∧ w 1 e = 0 ∧ w 2 e = 0 := by
      have h := hfe
      simp only [f, Prod.ext_iff, Prod.fst, Prod.snd] at h
      exact ⟨h.1, h.2.1, h.2.2⟩
    fin_cases i <;> simp_all
  have fcons : ∀ v, f (ea v) + f (eb v) + f (ec v) = 0 := by
    intro v
    simp only [f, Prod.ext_iff, Prod.mk_add_mk]
    refine ⟨?_, ?_, ?_⟩
    · exact heven v 0
    · exact heven v 1
    · exact heven v 2
  exact cdc_of_cubicFlow
    { fst := fst, snd := snd, loopless := loopless,
      ea := ea, eb := eb, ec := ec, hab := hab, hac := hac, hbc := hbc,
      hinc := hinc, f := f, fnz := fnz, fcons := fcons }

end CDCProof

#print axioms cdc_of_covering
