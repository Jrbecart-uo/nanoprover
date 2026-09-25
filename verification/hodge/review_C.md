# Hodge statement audit, area C: the algebraic side (`algebraicCycleClassSpan`)

Repo: `external/hodge` (Paul-Lez/HodgeConjecture, commit 5d0b87f, Lean v4.33.1). I did not modify or build the repo, so none of the conclusions below comes from compiling it.
Paths below are relative to `HodgeConjecture/`.

## Verdict

I found **no BUG** in area C. The span is exactly the ℚ-span of the classes [Z] ∈ H^{2p}(X(ℂ);ℚ), where Z ranges over the integral closed subvarieties of codimension p. It is not accidentally 0 and not accidentally ⊤.

The argument is robust and does not require checking every internal construction:

1. **The target is the real supported cohomology.** `H_[Z]^n(X;ℚ)` is `Ext^n(ℤ_X/ℤ_{X∖Z}, ℚ_X)`, which is `Ext^n(i_*ℤ_Z, ℚ) = H^n_Z(X;ℚ)`. `forgetSupport` precomposes with `ℤ_X → ℤ_X/ℤ_{X∖Z}` and then applies `Ext(ℤ_X, –) = Sheaf.H`. This is the natural map.
2. **The class is built entirely from proven isomorphisms.** It is `iso⁻¹(s)`, where the iso `H^{2p}_Z(X) ≅ Γ(U, 𝓗^{2p}_{Z(ℂ)})` (with `U = X(ℂ)∖Z_sing(ℂ)`) is an `asIso` of a homology map. That map is proven iso by lemmas in the closure, and those lemmas contain no `sorry` or `axiom`.
3. **The section s is nonzero.** Its germ at every point of `Z_reg(ℂ)` is the pullback, under a holomorphic flattening chart, of the normalized dual of the complex orientation class of `H_{2c}(ℂ^c, ℂ^c∖0;ℚ)`. That dual is nonzero by construction, since it evaluates to 1 on a class proven nonzero. `Z_reg(ℂ)` is nonempty (proved: `dense_cycleComponent_smooth_closedPoints`).
4. **Nonzero is enough.** For irreducible Z of codimension p, H^{2p}_Z(X;ℚ) ≅ ℚ, so any nonzero element is λ·[Z]_Z with λ ∈ ℚ^×. Its image under the additive (hence ℚ-linear) `forgetSupport` is λ[Z], and the ℚ-span is insensitive to λ. Sign and orientation conventions do not matter.

## Table

| definition | file:line | verdict | reason |
|---|---|---|---|
| `instance : Preorder X` (scheme points) | Mathlib `AlgebraicGeometry/Scheme.lean:158` | OK | `specializationPreorder`, with `a ≤ b ↔ b ⤳ a` (`le_iff_specializes`). Closed points are minimal (`height_of_isClosed`: height 0) and the generic point is the top. So `coheight x` is the length of the longest chain of generizations, which is dim 𝒪_{X,x} = codim of the closure of x. No local override of the scheme order exists in the closure: the only `specializationOrder` local instances are in `Lemmas/Topology/Dimension`, `Mathlib/Topology/KrullDimension`, and they point the same way. |
| index `Order.coheight x = p` | `Definitions/AlgebraicGeometry/Cycle/FundamentalClass.lean:148` | OK | The direction is confirmed by proven repo lemmas. `eq_genericPoint_of_coheight_zero` (`Mathlib/AlgebraicGeometry/GenericPoint.lean:32`) shows p=0 is the generic point. `SmoothOfRelativeDimension.coheight_eq_dimension_of_isClosed` (`Lemmas/.../Cycle/Component/NormalCoordinates.lean:69`) shows a closed point has coheight d. `cycleComponentSmoothLocus_smoothOfRelativeDimension` (`Lemmas/.../Cycle/Component/SmoothClosedLift.lean:42`) shows Z_reg has relative dimension `dim X − p`, and its proof uses a nonempty closed point, so it is not vacuous. The index covers all scheme points, including non-closed ones, with exactly one class per point (hx is a Prop). Points correspond one-to-one to integral closed subschemes, so nothing extra is indexed. |
| `cycleComponent`, `cycleComponentι` | `Definitions/AlgebraicGeometry/Cycle/Support.lean:47,53` | OK | Reduced closed subscheme on `closure {x}` (vanishing ideal). Integral instance is proven. |
| `cycleComponentSupport` / `cycleComponentAnalyticClosedSupport` | `Cycle/Support.lean:97`; `Cycle/Component/SmoothClosedLift.lean:112` | OK | `Point.underlying ⁻¹' closure {x}`, i.e. ℂ-points (sections of X→Spec ℂ) whose closed image lies in Z. Because Spec ℂ is reduced, this equals Z(ℂ). |
| `ComplexPoint`, `Point.underlying` | `Definitions/AlgebraicGeometry/ComplexPoint/Basic.lean:74,110,419` | OK | ℂ-points over Spec ℂ, not arbitrary morphisms Spec ℂ → X. |
| `singularLocusClosed`, `reducedSmoothClosedFiltration 0` | `Definitions/AlgebraicGeometry/Stratification/Basic.lean:77,92` | OK | Z_sing is the complement of Mathlib's `smoothLocus` of Z → Spec ℂ. Filtration step 0 is Z_sing itself. |
| `cycleComponentSmoothLocusAmbientOpen`, `cycleComponentSmoothSupportAmbientOpen` | `Cycle/Component/SmoothClosedLift.lean:32`; `Cycle/Component/SmoothSupportPurity.lean:39` | OK | X ∖ Z_sing (Zariski) and X(ℂ) ∖ Z_sing(ℂ). They are not too large: the proven extension iso would be impossible if U ∩ Z(ℂ) were empty. |
| `closedImmersionHolomorphicFlatteningChart` (+ `closedImmersionFlatteningChart`, `.choose` of `exists_open_normalCriterion`) | `Definitions/AlgebraicGeometry/ClosedImmersion/HolomorphicCharts.lean:80`; `.../NormalCoordinates.lean:37,181` | OK | `.choose` of true existence statements (a left inverse of an injective derivative, and a neighbourhood). The result is an OpenPartialHomeomorph onto ℂ^m×ℂ^{d−m} with S equal to the zero set of the normal coordinate on its source. |
| `standardComplexLocalClass` | `Definitions/AlgebraicTopology/LocalHomology/ComplexClass.lean:66` | OK | Proven `≠ 0` (`standardComplexLocalClass_ne_zero_for_chart`), including c=0. The `Nat.mul_comm ▸` cast is a canonical transport. |
| `normalizedDual`, `normalizedRelativeCoclass` | `Definitions/AlgebraicGeometry/Cycle/Local/Purity.lean:51,59` | OK | `Classical.choose` of `exists_dual_eq_one` for z≠0. The functional is nonzero by construction (value 1 at z), and it is unique because H_{2c}(ℂ^c,ℂ^c∖0;ℚ) is 1-dimensional. The UCT map is an equiv, so the coclass is ≠0. |
| `chartNormalProjectionCoclass`, `smoothClosedSupportChartCoclass` | `Definitions/AlgebraicTopology/LocalHomology/NormalProjectionCoclass.lean:64`; `Definitions/.../Cycle/SmoothPair/CoclassOverlap.lean:40` | OK | Pullback under normal projection. Locally it is the Thom/orientation class of the normal slice, which generates H^{2c}(W, W∖S). |
| `smoothClosedSupportCoclassStalk` / `...Section` | `Definitions/.../Cycle/SmoothPair/CoclassSection.lean:117,169` | OK | Uses `hxS.choose` for the chart centre. Independence of that choice is proven (`exists_open_smoothClosedSupportChartCoclass_eq`). Gluing uses `sectionOfLocallyRepresentable`, the `.choose` of an ∃! whose germ property is proven. The germ is nonzero at every point of S. |
| `cycleComponentSmoothClosedLiftCoclassSection` | `Definitions/.../Cycle/Component/SmoothSupportCoclassSection.lean:55` | OK | `hdeg ▸` with `hdeg : dim X − (dim X − p) = p` (proven using `coheight_le_complex`, p ≤ dim X). The index appears only in the degree, so this is a canonical transport to degree 2p. |
| `cycleComponentSmoothSupportCoclassSection` | same file :107 | OK | Transport along the open embedding (X∖Z_sing)(ℂ) ↪ X(ℂ) through the sheaf isomorphisms `supportRelativeCohomologySheafOpenIso` and `eqToHom`. Bijective, so it stays nonzero. |
| `supportRelativeCohomologyPresheaf`, `neighborhoodSupportComplementPair` | `Definitions/AlgebraicTopology/Support/RelativeCohomologySheaf.lean:42`; `.../LocalHomology/FundamentalClass.lean:48` | OK | V ↦ H^n(V, V∖S; ℚ), with the correct complement. |
| `complexSupportInjectiveCohomologySheafIsoRelative` | `Cycle/FundamentalClass.lean:43` | OK | `asIso` of a homology map composed with a proven iso. The degree is the ℕ-cast `(n:ℤ)`. |
| `CycleComponentSupportedCohomology`, `CycleComponentSmoothCoclassSections` | `Cycle/FundamentalClass.lean:62,81` | OK | Degree `2*(p:ℤ)` and `2*p : ℕ` respectively. |
| `cycleComponentSupportExtensionIso` | `Definitions/.../Cycle/Component/SupportExtension.lean:184` | OK | `asIso` of restriction H^{2p}_Z(X) → H^{2p}_Z(U), proven iso by vanishing of H^{2p}, H^{2p+1}_{Z_sing}. The mathematics is correct: codim Z_sing ≥ p+1. |
| `cycleComponentSmoothSupportLowestSectionCohomologyIso` | `Definitions/.../Cycle/Component/SmoothSupportPurity.lean:169` | OK | Lowest-degree iso from purity (𝓗^j = 0 on U for j<2p) and flasqueness. |
| `cycleComponentSupportedClassNormalizationIso` | `Cycle/FundamentalClass.lean:93` | OK | Composite of three isos. `he ▸` with `he : ((2p:ℕ):ℤ) = 2*(p:ℤ)` only touches the ℤ homology index. |
| `cycleComponentExtendSmoothCoclass`, `cycleComponentSupportedInjectiveClass` | `:108`, `:117` | OK | `inv` of the iso applied to s≠0 gives a class ≠0. |
| `rationalSupportAddEquivSupportedInjectiveHomology` | `Definitions/AlgebraicGeometry/Cohomology/WithSupport.lean:75` | OK | A proven `≃+` between `Ext` and the injective model. |
| `cycleComponentSheafSupportedClass` | `Cycle/FundamentalClass.lean:125` | OK | `he ▸` with `he : 2*(p:ℤ) = ((2*p:ℕ):ℤ)`: canonical transport, and the degree is correct. |
| `supportH`, `relH`, `pairSheaf` | `Definitions/AlgebraicTopology/Support/Cohomology.lean:47`; `Mathlib/CategoryTheory/Sites/SheafCohomology/Pair.lean:110,123` | OK | `Ext^n(coker(ℤ[X∖Z]→ℤ[X]), F)` equals `RHom(i_*ℤ_Z, F)`, which is H^n_Z(X,F). |
| `forgetSupport` | `Definitions/AlgebraicGeometry/Cohomology/WithSupport.lean:52` | OK | Precomposes with `ℤ[X] → ℤ[X,X∖Z]`, then `H'.addEquivTerminal` (ℤ[⊤] ≅ constant ℤ) to reach `Sheaf.H`. This is the standard map. Injective for Z=⊤ (proven). |
| `cycleComponentSheafClass` | `Cycle/FundamentalClass.lean:136` | OK | forgetSupport of the class above, in degree `2*p`. |
| `algebraicCycleClassSpan` | `Cycle/FundamentalClass.lean:146` | OK | The `sSup` of singleton spans equals the span of the set of classes. |
| `fieldCohomologyModule` (ℚ-structure on H^{2p}) | `Definitions/AlgebraicGeometry/Hodge/Filtration.lean:588` | OK | Scalar action through coefficient multiplication. A ℚ-module structure on an abelian group is unique, so spans are unambiguous. |
| `sorry` / `axiom` / `opaque` / `implemented_by` / `native_decide` | whole closure (254 modules, grep) | OK | None. Every `Classical.choose`/`choice` is of a proven ∃ (charts, neighbourhoods, a dual functional, a glued section, a presentation). `Classical.arbitrary` appears only in proofs or out-of-area files (`Hodge/HolomorphicDeRham.lean:156`, area B). |

## Ranked concerns (all minor; none changes the span)

1. **(Low) The file has not been compiled.** The repo is not built, so the absence of `sorry` and `axiom` rests on grep only.
   Sanity check: `#print axioms HodgeConjecture` should list only `propext, Classical.choice, Quot.sound`.
2. **(Low) Nonvanishing of the supported class is true but not stated as a lemma.** The fidelity argument depends on s ≠ 0, which holds mathematically but is not recorded anywhere.
   Suggested lemma: `cycleComponentSmoothSupportCoclassSection X x hx ≠ 0`, or equivalently `cycleComponentSheafSupportedClass X x hx ≠ 0`. It should follow from the germ lemma `smoothClosedSupportCoclassStalk_eq_chartGerm` plus the fact that the local Thom germ is nonzero.
3. **(Low) The docstring's normalization claim is not pinned down.** "Evaluates to 1 on complex orientation classes of normal spaces" depends on `normalizedDual` (a `Classical.choose`). It is unique only because the space is 1-dimensional, and there is no lemma stating the resulting class is independent of choices. This is irrelevant to the ℚ-span.
   Sanity lemma: `normalizedRelativeCoclass z hz` pairs to 1 with z (definitional).
4. **(Low) Sanity checks on the ends of the degree range.** The p=0 case, and the closed-point case (p = dim X, Z = a point, class = point class ≠ 0), are not stated.
   Suggested lemmas:
   - `Order.coheight (genericPoint X.left) = 0` (the converse already exists).
   - `cycleComponentSheafClass X (genericPoint X.left) h0 = 1`, the unit in H^0.
   - `algebraicCycleClassSpan X 0 = ⊤`.
   - For `IsClosed {x}`: `Order.coheight x = dim X.left` (exists as `coheight_eq_dimension_of_isClosed`), and `cycleComponentSheafClass X x hx ≠ 0`. This one needs compactness of X, since forgetSupport is not injective in general.
5. **(Info) Nonvanishing in H^{2p}(X) needs projectivity, which is present.** `cycleComponentSheafClass ≠ 0` for p ≥ 1 needs projectivity (deg Z ≠ 0). The statement assumes `IsProjective`, so this is fine. If the ≠ 0 lemma were stated, it would be a real theorem, not a sanity check, so it is not needed for fidelity.
6. **(Info) Notation clash risk.** `open AlgebraicTopology.Singular` in `FundamentalClass.lean` also brings the singular-cohomology notation `H^n(X; R)` into scope. It would only elaborate for `X : TopCat`, so `H^(2*p)(X; ℚ)` resolves to sheaf cohomology `Sheaf.H` of the constant sheaf. This matches the statement: the `≤` would not typecheck otherwise.
