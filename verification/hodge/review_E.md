# Hodge conjecture statement audit, area E: charts, coverage gaps, and machine sanity checks

Repo: `external/hodge` (Paul-Lez/HodgeConjecture), Lean v4.33.1. This was a read-only audit: I did not
modify the repo and did not run `lake build`. Paths are relative to `hodge/HodgeConjecture/`. The Lean
checks are scratch files in
`/tmp/claude-1000/-home-jbecart-tmp-mathTest-nanoprover/d46b9b24-f0da-4c40-91d4-15c0dea51629/scratchpad/auditE/`
(`E1.lean`, `E2.lean`, `E3.lean`, `Edges.lean` + `parents.py`). Each ran with `lake env lean` and
compiles with no errors and no `sorry`. `#print axioms` gives only `[propext, Classical.choice, Quot.sound]`.

## Verdict

**No bug found.** B's open concern C1 is closed. "Holomorphic" in the repo is the classical complex-analytic
structure on X(ℂ). The chart system cannot be degenerate, and the repo contains the lemmas needed for
that conclusion. I also added two kernel checks that pin the structure from both sides.

All 19 coverage-gap modules are accounted for. Fifteen enter only as intermediate objects or maps
inside isomorphisms whose iso-ness is kernel-checked. Four enter through values that matter:
- `LinearDual`: the definition of singular cochains.
- `SingularClosedFiltration`: Z_sing, U and Z_reg.
- `ComplexOrientation`: the orientation homeomorphism ℂ^c ≅ ℝ^{2c}.
- `OpenInjectiveResolution`: the chosen injective resolution.

I read all four and each is correct. None can be zero or degenerate in a way that changes the statement.

---

## Task 1: the complex structure on X(ℂ) (B's concern C1)

### How the charts are built

`chartAt z = localChart X d z`. This holds by `rfl` (checked in `E2.lean`), with d = `dim X.left`.

| layer | definition (file:line) | what it is | can it be degenerate? |
|---|---|---|---|
| étale coordinates | `LocalEtaleCoordinates`, `localEtaleCoordinates` (`Lemmas/…/ComplexPoint/SmoothCoordinates.lean:100,127`) | Affine open `W ∋ x` plus an **étale** ℂ-algebra map `ℂ[t₁..t_d] → Γ(W)`. Chosen by `Classical.choice` from `nonempty_localEtaleCoordinates`, which is proved from Mathlib's `exists_etale_mvPolynomial`. | No. The structure carries a proof `etale`, so the coordinates cannot be constant. d is fixed by the proved instance `SmoothOfRelativeDimension (dim X.left)`. |
| affine points ↔ algebra homs | `affineSpecHomeomorph` (`…/AffineScheme.lean:210`); `affineAlgebraHomTopology` (:45) | `X(ℂ)` of `Spec R` ≃ₜ `R →ₐ[ℂ] ℂ` with pointwise convergence | No. It is a `Homeomorph`, and continuity in both directions is proved against `analyticTopology`. |
| open subscheme | `openHomeomorph` (`…/Open.lean:173`) | `W(ℂ) ≃ₜ {z ∈ X(ℂ) ∣ z ∈ W}` | No. It is a `Homeomorph`. |
| localization | `localizationAwayAlgHomHomeomorph`, `localizationAwayAlgHomMap` (`…/Localization.lean:149,157`) | `Hom(S_f,ℂ) ≃ₜ {u ∣ u f ≠ 0}`, an open embedding | No. It is a `Homeomorph` plus a proved open embedding. |
| polynomial ring | `mvPolynomialAlgHomHomeomorph` (`…/StandardEtale.lean:73`) | `Hom(ℂ[t],ℂ) ≃ₜ ℂ^d`, φ ↦ (φ(tᵢ))ᵢ | No. It is a `Homeomorph`. |
| standard étale chart | `standardEtaleProjectionChart` (`…/Etale.lean:454`), built on `standardEtaleImplicitOpenPartialHomeomorph` (:161, implicit function theorem) | An `OpenPartialHomeomorph` with `toFun x = x.1.1` (projection to the base coordinates). The inverse is the implicit-function branch. | No. It is a structure with proved `open_source`, `open_target`, `continuousOn_invFun`, `left_inv'` and `right_inv'`. The junk value `z` of `standardEtaleChartInverse` off the target (:274) is never used. |
| étale chart | `etaleAlgHomProjectionChart` (`…/Etale.lean:627`) | The standard chart on a chosen standard-étale localization (`etaleStandardNeighborhood`, :614, `Classical.choice` of a proved ∃), lifted along an open embedding | No, for the same reasons as the rows above. |
| ambient chart | `ambientProjectionChart` (`…/SmoothCoordinates.lean:361`), `localChart` (`Lemmas/…/Manifold.lean:80`) | `.trans` of the homeomorphisms above, then `lift_openEmbedding` into `X(ℂ)` | No. See the next table. |

The endpoints of every `.trans` are fixed. The source is `(ComplexPoint X, analyticTopology)`, which area A
validated. The target is Euclidean `Fin d → ℂ`. Each intermediate topology (for example
`affineAlgebraHomTopology`) is tied to both ends by kernel-checked `Homeomorph`s. So no intermediate
definition can change which charts are local homeomorphisms.

### Proven facts that pin the structure

| fact | lemma (file:line) |
|---|---|
| Each chart is an `OpenPartialHomeomorph` of `X(ℂ)` with the analytic topology, onto an open set of ℂ^d | type of `localChart` (Manifold.lean:80) |
| The atlas covers X(ℂ): `z ∈ (localChart z).source` | `mem_localChart_source` (Manifold.lean:88); re-checked as `mem_chart_source` in `E2.lean` |
| **Chart components are regular functions**: `localChart z q i = evaluate W (tᵢ) q` | `localChart_apply_component_eq_evaluate` (Manifold.lean:149) ← `ambientProjectionChart_apply_of_mem`, `algebraicCoordinates_eq_analyticCoordinates` (SmoothCoordinates.lean:386, 298) |
| **Every regular function is analytic along every inverse chart**: `AnalyticAt ℂ (evaluate V s ∘ (localChart z).symm) w` | `analyticAt_localChart_symm_evaluate` (Manifold.lean:130) ← `analyticAt_ambientProjectionChart_symm_evaluate` (SmoothCoordinates.lean, end) ← `analyticAt_etaleAlgHomProjectionChart_symm_apply` (Etale.lean, end) |
| Transition maps are analytic, so `IsManifold 𝓘(ℂ,ℂ^d) ω` | `analyticAt_localChart_transition`, `isManifold_omega` (Manifold.lean:215) |

**Why this equals the classical structure.** Let ψ be any classical holomorphic chart of X^an whose components are
regular functions g_j. Such charts exist at every point (étale coordinates plus the holomorphic inverse
function theorem). Let φ be a repo chart.
- φ∘ψ⁻¹ has components (regular function)∘ψ⁻¹. These are classically holomorphic, by the chart-components row above.
- ψ∘φ⁻¹ has components g_j∘φ⁻¹. These are analytic by `analyticAt_localChart_symm_evaluate`.

Both maps are homeomorphisms between opens, by the `OpenPartialHomeomorph` row and area A's topology result.
So every repo chart lies in the classical maximal atlas, and `ContMDiffAt … ω`
means holomorphic in the classical sense. The same argument shows that another choice made by `Classical.choice`
(of coordinates, standard presentation or localization) gives the same maximal atlas.

Holomorphic forms use exactly these charts (`extChartAt … z`, `chartSectionDomain`, ADF.lean:95). The kernel
`chartEvaluationKernel` (ADF.lean:677) ranges over **all** z and all points of each chart domain. Because
the atlas covers X(ℂ), it is exactly the set of forms that vanish pointwise. It is not larger.

### New kernel checks for C1 (`E2.lean`)

```lean
theorem regular_isHolomorphicAt [SmoothOfRelativeDimension d X.hom]
    (V : X.left.Opens) (s : Γ(X.left, V)) (z : ComplexPoint X) (hz : z ∈ overOpen V) :
    ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ) ω (Point.evaluate V s) z            -- proved
theorem conj_coordinate_not_holomorphicAt [SmoothOfRelativeDimension d X.hom]
    (z : ComplexPoint X) (i : Fin d) :
    ¬ ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ) ω
        (fun w ↦ starRingEnd ℂ (localChart X d z w i)) z                  -- proved
```

These are B's suggested sanity lemma, proved for arbitrary X and not just 𝔸¹. Regular functions are
holomorphic, and the conjugate of a coordinate is not holomorphic at any point. So the class of holomorphic
functions is neither "all continuous" nor "constants only". `E2.lean` also re-checks `chartAt z = localChart X d z` by `rfl`.

---

## Task 2: coverage-gap modules

Method: I recomputed the statement's dependency graph with the same traversal as
`hodge_TrustedSurface.lean` (`Edges.lean`, 7244 local edges). For each gap-module constant I listed its
consumers outside the gap set (`parents.py`), then read the consumer and the module.

Why "iso-internal" is enough: the cycle class is
`forgetSupport(ε⁻¹(N⁻¹(s)))`, where
- `N = cycleComponentSupportedClassNormalizationIso` is a composite of `asIso`s and `NatIso`s,
- `ε = rationalSupportAddEquivSupportedInjectiveHomology` is an `≃+`,
- `s = cycleComponentSmoothSupportCoclassSection`.

The endpoints are fixed outside the gap modules: `H_[Z]^{2p}` Ext (A, C) and `Γ(U, 𝓗_[S]^{2p})`, the
sheafified `V ↦ H^{2p}(V, V∖S; ℚ)` (C). Since `H^{2p}_Z(X;ℚ) ≅ ℚ`, only **s ≠ 0** and iso-ness matter (C's argument).
The internal construction of an iso cannot change either.

| module | constants in the trusted surface | how it enters | value matters? | verdict |
|---|---|---|---|---|
| `Definitions.Algebra.Homology.LinearDual` | `linearDualCochainComplex`, `linearDualMap`, `linearDualIso`, `linearDualHomologyEquiv`, `dualHomologyComparisonExplicit`, … | `RelativeCochainComplex := (C_*(X)/C_*(A)).linearDualCochainComplex`, which **defines singular cochains**. `relativeCochainComplexMap := linearDualMap` defines pullback. `relativeCohomologyEquivDualHomology` (UCT), used by `normalizedRelativeCoclass` | **yes** (it defines the values of local classes and the restrictions in `𝓗_S`) | OK. Degree n is `Module.Dual R (K.X n)`, `d = (K.d (n+1) n).dualMap`, and maps are `dualMap`. The UCT map is literally `[φ] ↦ ([z] ↦ φ z)` (`dualHomologyComparisonExplicit_mk_apply_mk`, rfl), and its bijectivity over a field is proved. Chains are Mathlib's `singularChainComplexFunctor`, and relative chains are a `coker`. |
| `Singular.Sheaf.Cochain` | `singularCochainPresheaf/Sheaf/…Complex`, `constantsToSingularCochain…`, `OpenChains/OpenCochains` | Model complex `C^•_sing` feeding `SingularFlasqueModel` | no, intermediate object | OK (iso-internal). Its role as a resolution is used only through the proved `QuasiIso` instance `complexSupportedSingularToAmbientInjective_quasiIso`. |
| `Singular.Sheaf.CochainOpenCone`, `…CochainOpenSections` | `openRawSingularRestrictionCone…`, `openSingularSheafRestriction…` | Inside `supportedRationalSingularSectionCohomologyEquiv…`, which lies inside `supportedSingularCohomologyPresheafIsoRelative` | no | OK (iso-internal) |
| `Support.SingularFlasqueModel` | `rationalSingularCochainComplex`, `supportedRationalSingularCochainComplex`, `singularToConstantInjective…`, `supportedSingularToInjectiveComplex` | Middle object of `complexSupportInjectiveCohomologySheafIsoRelative = (asIso (homologyMap f n)).symm ≪≫ supportedSingularCohomologySheafIsoRelative` (FundamentalClass.lean:43) | no | OK. The comparison map f's value matters only via its proved `QuasiIso`. |
| `Cohomology.SupportedSingularModel` | `complexSupportedSingularToAmbientInjective` | The f above, specialised to X(ℂ) | no | OK (`QuasiIso` instance proved in the same file) |
| `Support.SingularCohomologySheafComparison` | `supportedSingularCohomologyPresheafIsoRelative`, `…SheafIsoRelative` | Second factor of the iso above. It is a `NatIso.ofComponents` with the naturality proof, sheafified by `presheafToSheaf.mapIso` | no | OK (iso) |
| `Support.SingularSectionCohomology` | `supportedRationalSingularSectionCohomologyEquiv{Relative,SupportComplement}`, `openIntersection…` | Components of the NatIso above (`≃ₗ` plus homeomorphism of pairs) | no | OK (iso) |
| `Support.SectionRestrictionCone` | `sectionComplexRestriction`, `supportRestrictionSectionsConeIso`, … | `cycleComponentSupportSectionRestriction`, which is used only in `cycleComponentSupportExtensionIso = asIso …` (IsIso proved in `…_homology_isIso`) | no | OK (iso) |
| `Support.NeighborhoodPairImage` | `neighborhoodSupportPairImage{Iso,CohomologyIso,CohomologyEquiv}`, `…ComplementImageHomeomorph` | `supportRelativeCohomologyPresheafOpenIso`, which transports s along the open embedding. It is `homologyFunctor.mapIso (linearDualIso (relativeChainFunctor.mapIso (iso of pairs)))`, and the pair iso is built from a `Homeomorph` with proved inverse laws | no, but s passes through it | OK. A functorial iso preserves s ≠ 0. |
| `Sheaf.CohomologySection`, `Sheaf.CohomologyStalkVanishing`, `Sheaf.FlasqueLowestCohomology` | `sectionCohomologyPresheaf(OnOpenIso)`, `…SheafificationIso`, `lowestSectionCohomologyIso`, `…_isIso_lowest` | Inside `supportedSingularCohomologySheafIsoRelative` and `openRestrictedLowestSectionCohomologyIso` | no | OK (iso-internal) |
| `Sheaf.OpenRestrictedLowestCohomology` | `openRestrictedLowestSectionCohomologyIso`, `openRestriction…Iso` | `cycleComponentSmoothSupportLowestSectionCohomologyIso`, one factor of N | no | OK (iso) |
| `Sheaf.OpenInjectiveResolution` | `ambientConstantInjectiveResolution` | `ambientRationalInjectiveComplex`, the model used for H_Z and 𝓗_S | model choice | OK. It is Mathlib `injectiveResolution` (a genuine `InjectiveResolution` structure), connected to `Ext` by the canonical `≃+` (A). The choice is irrelevant. |
| `Singular.RelativeCochainCone`, `…ConeNaturality` | `relativeDualCochainShortComplex{Int,Nat}`, `relativeCochainRestrictionInt`, `relativeCochainConeCohomologyEquivCanonical`, … | The short exact sequence of the pair (with a proved `_shortExact`) and cone ≅ relative. Used inside `CochainOpenCone` | no | OK (iso-internal) |
| `Cycle.Component.SingularClosedFiltration` | `cycleComponentSingular{Ambient,Analytic}ClosedFiltration`, `cycleComponentSmoothLocusOver` | **Defines** Z_sing ⊂ X, U = X(ℂ)∖Z_sing(ℂ) (`cycleComponentSmoothSupportAmbientOpen`), and Z_reg as a ℂ-scheme (the domain of the normal charts that build s) | **yes** | OK. `S₀ = singularLocusClosed` (the complement of Mathlib's `smoothLocus` of Z→Spec ℂ). The analytic version is `underlying⁻¹(S₀)`. Z_reg is Mathlib's `smoothLocus.ι ≫ ι_Z` over ℂ. It cannot be too large: then U∩Z(ℂ)=∅, `Γ(U,𝓗_S)=0`, and the proved iso would force `H^{2p}_Z=0`. It cannot be too small: `cycleComponentSmoothLocusOver_hom_smoothOfRelativeDimension` is a proved instance. |
| `Lemmas.LinearAlgebra.ComplexOrientation` | `Complex.piBasisOneI`, `Complex.piCoordCLE` | `complexRealHomeomorph` → `standardComplexRealPairIso` → `standardComplexLocalClass` | normalization only | OK. `piCoordCLE` is a continuous ℝ-linear **equivalence** ℂ^n ≃ ℝ^{2n} (re₀, im₀, re₁, …), so the class's non-vanishing (proved, C) is unaffected. The ordering only fixes a sign, and the ℚ-span ignores signs. |

Nothing in these modules can be zero or degenerate in a way that affects the statement. The only
value-level input to the cycle class that is still unproved is `s ≠ 0`. It is argued in C and is not
changed by anything in these modules.

---

## Task 3: machine checks

| # | check | file | result |
|---|---|---|---|
| a | `IsProjective (𝟙 Spec ℂ)` (explicit closed immersion into ℙ⁰ via `Proj.awayι`, adapted from D's `Sanity.lean`), plus `IsIntegral`, `Smooth` by `inferInstance`. Then `∃ X, IsIntegral X.left ∧ Smooth X.hom ∧ IsProjective X.hom`, and `h pt0 p : Hdg^p(pt0; ℚ) ≤ algebraicCycleClassSpan pt0 p` elaborates (the statement's instance arguments are found at this X) | `E1.lean` | ✔ compiles; axioms standard |
| b1 | A-concern 3: `cycleComponentSheafClassAnalyticTopology X = Point.analyticTopology := rfl` | `E2.lean` | ✔ |
| b2 | B-C1: `chartAt z = localChart X d z := rfl`; charts cover; regular ⇒ holomorphic; conj(coord) not holomorphic | `E2.lean` | ✔ (all four) |
| b3 | C-concern 4: `Order.coheight (genericPoint Y) = 0` for integral Y (converse already in the repo), and `cycleComponentSheafClass X (genericPoint X.left) _ ∈ algebraicCycleClassSpan X 0` | `E3.lean` | ✔ |

Not attempted, because each is a real theorem and not a few-line check:
- A-1: injectivity of `H^n(X;ℚ) → H^n(X;ℂ)`.
- B-C2/C3/C4: `hodgeFiltration = ⊥` for p>n, involutivity of conj, `Hdg^0 = ⊤`.
- C-2: `s ≠ 0`.

---

## Concerns, most severe first (all LOW or INFO; none changes the meaning)

1. **(LOW, carried over from C)** `cycleComponentSmoothSupportCoclassSection ≠ 0` is still not stated.
   After this audit it is the only value-level fact in the cycle-class construction that is argued but not
   proved. Its ingredients (LinearDual/UCT, local classes, Z_reg) were each read and are correct. If it failed, every
   class would be 0 and the statement would become *false* (Hdg⁰ ∋ 1 ≠ 0), not vacuous.
2. **(LOW)** Only a 0-dimensional witness is machine-checked. Satisfiability is shown only for `Spec ℂ`.
   There, dim = 0 and every chart and form question is trivial. No positive-dimensional X (for example ℙ¹ or an
   elliptic curve) was shown to satisfy `Smooth ∧ IsProjective` in Lean. Smoothness of `ℙ(n; S)` does not seem
   to be available in the pinned Mathlib or the repo, so I did not attempt it.
3. **(INFO)** "Repo atlas = classical atlas" is a paper argument from three proved lemmas, not a Lean theorem.
   It cannot be one, because Mathlib has no independent analytification to compare against. `E2.lean` adds both
   directions of B's sanity test, for all X.
4. **(INFO)** There are `Classical.choice` points in the chart construction: `localEtaleCoordinates`,
   `etaleStandardNeighborhood`, `chosenStandardEtalePresentation`. Each is a choice from a proved-nonempty
   type. By the argument above, any choice gives the same maximal atlas, but choice-independence is not
   stated in the repo.
5. **(INFO)** `affineAlgebraHomTopology` is a **global instance** on `R →ₐ[ℂ] ℂ` (AffineScheme.lean:45). It gives
   pointwise convergence, which is the right topology. Any conflict would surface as a failure of the kernel-checked
   `Homeomorph` compositions, and none occurred.
