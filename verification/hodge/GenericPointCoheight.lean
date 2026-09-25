import HodgeConjecture.Statement

open CategoryTheory AlgebraicGeometry ComplexPoint

namespace AuditE3

-- C4: the generic point has coheight 0, so p = 0 indexes exactly the class of X itself
-- (converse `eq_genericPoint_of_coheight_zero` is already in the repo).
theorem coheight_genericPoint (Y : Scheme) [IsIntegral Y] :
    Order.coheight (genericPoint Y) = 0 :=
  Order.coheight_eq_zero.mpr fun b _ => by
    exact Scheme.le_iff_specializes.mpr (genericPoint_specializes b)

-- so the p = 0 span contains the class indexed by the generic point
example (X : Over (Spec (CommRingCat.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] :
    cycleComponentSheafClass X (genericPoint X.left) (coheight_genericPoint X.left) ∈
      algebraicCycleClassSpan X 0 :=
  by
    unfold algebraicCycleClassSpan
    refine Submodule.mem_sSup_of_mem
      (s := Submodule.span ℚ {cycleComponentSheafClass X (genericPoint X.left)
        (coheight_genericPoint X.left)}) ?_ (Submodule.mem_span_singleton_self _)
    exact ⟨genericPoint X.left, coheight_genericPoint X.left, rfl⟩

end AuditE3

#print axioms AuditE3.coheight_genericPoint
