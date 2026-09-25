import HodgeConjecture.Definitions.AlgebraicGeometry.ProjectiveSpace
import HodgeConjecture.Mathlib.CategoryTheory.ConcreteCategory.Notation
import Mathlib

open CategoryTheory Limits AlgebraicGeometry MvPolynomial ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace SanityCheck

abbrev A := MvPolynomial (Fin 1) (ULift.{0} ℤ)
abbrev 𝒜 : ℕ → Submodule (ULift.{0} ℤ) A := homogeneousSubmodule (Fin 1) (ULift.{0} ℤ)

lemma x0_mem : (X 0 : A) ∈ 𝒜 1 := (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X _ 0)

def ev : A →+* ℂ :=
  MvPolynomial.eval₂Hom ((Int.castRingHom ℂ).comp ULift.ringEquiv.toRingHom) (fun _ => 1)

lemma ev_unit : IsUnit (ev (X 0)) := by simp [ev]

def φ : HomogeneousLocalization.Away 𝒜 (X 0 : A) →+* ℂ :=
  (IsLocalization.Away.lift (X 0 : A) ev_unit).comp
    (algebraMap (HomogeneousLocalization.Away 𝒜 (X 0 : A)) (Localization.Away (X 0 : A)))

def pt : Spec ↧ℂ ⟶ Proj 𝒜 :=
  Spec.map (CommRingCat.ofHom φ) ≫ Proj.awayι 𝒜 (X 0 : A) x0_mem one_pos

def s : Spec ↧ℂ ⟶ ℙ(Fin 1; Spec ↧ℂ) :=
  pullback.lift (𝟙 _) pt (terminal.hom_ext _ _)

lemma s_toBase : s ≫ toBase (Fin (0 + 1)) (Spec ↧ℂ) = 𝟙 _ := by
  exact pullback.lift_fst _ _ _

instance : IsClosedImmersion s := by
  have : IsClosedImmersion (s ≫ toBase (Fin (0 + 1)) (Spec ↧ℂ)) := by
    rw [s_toBase]; infer_instance
  exact IsClosedImmersion.of_comp s (toBase (Fin (0 + 1)) (Spec ↧ℂ))

instance : IsProjective (𝟙 (Spec ↧ℂ)) := ⟨⟨⟨0, s, s_toBase⟩⟩⟩

/-- The hypotheses of `HodgeConjecture` are jointly satisfiable: `Spec ℂ` over itself. -/
theorem hypotheses_satisfiable :
    ∃ X : Over (Spec ↧ℂ), IsIntegral X.left ∧ Smooth X.hom ∧ IsProjective X.hom :=
  ⟨Over.mk (𝟙 (Spec ↧ℂ)), (inferInstance : IsIntegral (Spec ↧ℂ)),
    (inferInstance : Smooth (𝟙 (Spec ↧ℂ))), (inferInstance : IsProjective (𝟙 (Spec ↧ℂ)))⟩

end SanityCheck


#print axioms SanityCheck.hypotheses_satisfiable
