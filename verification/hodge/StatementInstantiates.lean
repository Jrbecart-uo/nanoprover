import HodgeConjecture.Statement

open CategoryTheory Limits AlgebraicGeometry ComplexPoint MvPolynomial ProjectiveSpace
open scoped Manifold ContDiff

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section
namespace AuditE

-- (3a) satisfiability, re-derived (after D) against the full statement closure
abbrev A := MvPolynomial (Fin 1) (ULift.{0} ℤ)
abbrev 𝒜 : ℕ → Submodule (ULift.{0} ℤ) A := homogeneousSubmodule (Fin 1) (ULift.{0} ℤ)
lemma x0_mem : (X 0 : A) ∈ 𝒜 1 := (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X _ 0)
def ev : A →+* ℂ :=
  MvPolynomial.eval₂Hom ((Int.castRingHom ℂ).comp ULift.ringEquiv.toRingHom) (fun _ => 1)
lemma ev_unit : IsUnit (ev (X 0)) := by simp [ev]
def φ : HomogeneousLocalization.Away 𝒜 (X 0 : A) →+* ℂ :=
  (IsLocalization.Away.lift (X 0 : A) ev_unit).comp
    (algebraMap (HomogeneousLocalization.Away 𝒜 (X 0 : A)) (Localization.Away (X 0 : A)))
def pt : Spec (CommRingCat.of ℂ) ⟶ Proj 𝒜 :=
  Spec.map (CommRingCat.ofHom φ) ≫ Proj.awayι 𝒜 (X 0 : A) x0_mem one_pos
def s : Spec (CommRingCat.of ℂ) ⟶ ℙ(Fin 1; Spec (CommRingCat.of ℂ)) :=
  pullback.lift (𝟙 _) pt (terminal.hom_ext _ _)
lemma s_toBase : s ≫ toBase (Fin (0 + 1)) (Spec (CommRingCat.of ℂ)) = 𝟙 _ :=
  pullback.lift_fst _ _ _
instance : IsClosedImmersion s := by
  have : IsClosedImmersion (s ≫ toBase (Fin (0 + 1)) (Spec (CommRingCat.of ℂ))) := by
    rw [s_toBase]; infer_instance
  exact IsClosedImmersion.of_comp s (toBase (Fin (0 + 1)) (Spec (CommRingCat.of ℂ)))
instance : IsProjective (𝟙 (Spec (CommRingCat.of ℂ))) := ⟨⟨⟨0, s, s_toBase⟩⟩⟩

abbrev pt0 : Over (Spec (CommRingCat.of ℂ)) := Over.mk (𝟙 (Spec (CommRingCat.of ℂ)))
instance : IsIntegral pt0.left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of ℂ)))
instance : Smooth pt0.hom := inferInstanceAs (Smooth (𝟙 (Spec (CommRingCat.of ℂ))))
instance instProjPt0 : IsProjective pt0.hom := inferInstanceAs (IsProjective (𝟙 (Spec (CommRingCat.of ℂ))))

-- the statement genuinely instantiates at this X (instances found by unification)
example (h : HodgeConjecture) (p : ℕ) :
    Hdg^p(pt0; ℚ) ≤ algebraicCycleClassSpan pt0 p := h pt0 p

end AuditE
namespace AuditE
-- the whole statement specialized: Spec ℂ carries the Hodge hypotheses
example : ∃ X : Over (Spec (CommRingCat.of ℂ)),
    IsIntegral X.left ∧ Smooth X.hom ∧ IsProjective X.hom :=
  ⟨pt0, inferInstance, inferInstance, inferInstance⟩
end AuditE
#print axioms AuditE.instProjPt0
