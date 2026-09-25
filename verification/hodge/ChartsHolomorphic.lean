import HodgeConjecture.Statement

open CategoryTheory AlgebraicGeometry ComplexPoint Point Filter Topology
open scoped Manifold ContDiff

noncomputable section
namespace AuditE2

variable (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ)

-- A3: the local topology instance in FundamentalClass.lean is literally analyticTopology
example [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    ComplexPoint.cycleComponentSheafClassAnalyticTopology X = Point.analyticTopology := rfl

-- the ChartedSpace used by the holomorphic sheaf is the étale-coordinate chart, at every point
example [SmoothOfRelativeDimension d X.hom] (z : ComplexPoint X) :
    chartAt (Fin d → ℂ) z = localChart X d z := rfl

-- the atlas covers every point
example [SmoothOfRelativeDimension d X.hom] (z : ComplexPoint X) :
    z ∈ (chartAt (Fin d → ℂ) z).source := mem_chart_source _ z

-- Task 1 sanity: every regular function s on a Zariski open V is holomorphic (at every
-- complex point of V) in the repo's complex structure.
theorem regular_isHolomorphicAt [SmoothOfRelativeDimension d X.hom]
    (V : X.left.Opens) (s : Γ(X.left, V)) (z : ComplexPoint X) (hz : z ∈ overOpen V) :
    ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ) ω (Point.evaluate V s) z := by
  set e := localChart X d z with he
  have hzs : z ∈ e.source := mem_localChart_source X d z
  have hwt : e z ∈ e.target := e.map_source hzs
  have hV : e.symm (e z) ∈ overOpen V := by rwa [e.left_inv hzs]
  have hA : AnalyticAt ℂ (fun v ↦ Point.evaluate V s (e.symm v)) (e z) :=
    analyticAt_localChart_symm_evaluate X d z hwt V s hV
  rw [contMDiffAt_iff]
  refine ⟨?_, ?_⟩
  · have hc : ContinuousAt ((fun v ↦ Point.evaluate V s (e.symm v)) ∘ e) z :=
      hA.continuousAt.comp (e.continuousAt hzs)
    refine hc.congr ?_
    filter_upwards [e.eventually_left_inverse hzs] with w hw
    simp [hw]
  · have : ContDiffAt ℂ ω (fun v ↦ Point.evaluate V s (e.symm v)) (e z) := hA.contDiffAt
    simp only [mfld_simps]
    exact this.contDiffWithinAt


lemma conj_not_differentiableAt (a : ℂ) : ¬ DifferentiableAt ℂ (starRingEnd ℂ) a := by
  intro h
  set L := fderiv ℂ (starRingEnd ℂ) a
  have h1 : HasFDerivAt (starRingEnd ℂ) (L.restrictScalars ℝ) a :=
    h.hasFDerivAt.restrictScalars ℝ
  have hfun : (⇑(Complex.conjCLE : ℂ ≃L[ℝ] ℂ)) = ⇑(starRingEnd ℂ) := funext Complex.conjCLE_apply
  rw [← hfun] at h1
  have hL := h1.unique (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).hasFDerivAt
  have e1 : L 1 = 1 := by
    have := congrArg (fun M : ℂ →L[ℝ] ℂ => M 1) hL
    simpa [Complex.conjCLE_apply] using this
  have eI : L Complex.I = -Complex.I := by
    have := congrArg (fun M : ℂ →L[ℝ] ℂ => M Complex.I) hL
    simpa [Complex.conjCLE_apply] using this
  have hlin : L Complex.I = Complex.I * L 1 := by
    simpa using L.map_smul Complex.I (1 : ℂ)
  rw [eI, e1, mul_one] at hlin
  have : (2 : ℂ) * Complex.I = 0 := by linear_combination -hlin
  simp [Complex.I_ne_zero] at this

-- Task 1 sanity: the complex conjugate of a chart coordinate is NOT holomorphic, at any point.
-- So "holomorphic" is not "continuous/smooth": the structure really is complex-analytic.
theorem conj_coordinate_not_holomorphicAt [SmoothOfRelativeDimension d X.hom]
    (z : ComplexPoint X) (i : Fin d) :
    ¬ ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ) ω
        (fun w ↦ starRingEnd ℂ (localChart X d z w i)) z := by
  intro hf
  set e := localChart X d z with he
  have hzs : z ∈ e.source := mem_localChart_source X d z
  have hwt : e z ∈ e.target := e.map_source hzs
  rw [contMDiffAt_iff] at hf
  have hcd := hf.2
  simp only [mfld_simps] at hcd
  have hD : DifferentiableAt ℂ
      ((fun w ↦ starRingEnd ℂ (localChart X d z w i)) ∘ (localChart X d z).symm) (e z) :=
    (hcd.contDiffAt Filter.univ_mem).differentiableAt (by simp)
  have hD' : DifferentiableAt ℂ (fun v : Fin d → ℂ ↦ starRingEnd ℂ (v i)) (e z) := by
    refine hD.congr_of_eventuallyEq ?_
    filter_upwards [e.open_target.mem_nhds hwt] with v hv
    simp only [Function.comp_apply]
    rw [← he, e.right_inv hv]
  have hU : DifferentiableAt ℂ (Function.update (e z) i) ((e z) i) :=
    (hasFDerivAt_update (e z) ((e z) i)).differentiableAt
  have hD'' : DifferentiableAt ℂ (fun v : Fin d → ℂ ↦ starRingEnd ℂ (v i))
      (Function.update (e z) i ((e z) i)) := by rwa [Function.update_eq_self]
  have hC := hD''.comp ((e z) i) hU
  have hfun : ((fun v : Fin d → ℂ ↦ starRingEnd ℂ (v i)) ∘ Function.update (e z) i) =
      ⇑(starRingEnd ℂ) := by
    funext t; simp
  rw [hfun] at hC
  exact conj_not_differentiableAt ((e z) i) hC

end AuditE2

#print axioms AuditE2.regular_isHolomorphicAt
#print axioms AuditE2.conj_coordinate_not_holomorphicAt
