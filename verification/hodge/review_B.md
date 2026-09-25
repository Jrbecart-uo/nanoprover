# Hodge conjecture statement: fidelity audit, area B (de Rham / Hodge side)

Repo: `external/hodge` (Paul-Lez/HodgeConjecture, Lean v4.33.1). Scope: everything feeding `hodgeClasses`
(`HodgeConjecture/Definitions/AlgebraicGeometry/Hodge/Filtration.lean:875`), except the definition of
constant-sheaf cohomology `Sheaf.H` itself. Method: read every def/abbrev/instance on the path; proofs read only
where a definition depends on a choice. Nothing was compiled, because another process was building `.lake` while
this audit ran. The sanity lemmas below have not been type-checked.

Abbreviations: `F.lean` = `Definitions/AlgebraicGeometry/Hodge/Filtration.lean`, `HdR.lean` =
`Definitions/AlgebraicGeometry/Hodge/HolomorphicDeRham.lean`, `ADF.lean` =
`Definitions/AlgebraicGeometry/Hodge/AnalyticDifferentialForms.lean`, `L/` = `Lemmas/`.

## Overall verdict

**No bug found in area B.** Unfolded, the carrier of `Hdg^p(X; ℚ)` is

`{ α ∈ H^{2p}(X(ℂ); ℚ) | ι(α) ∈ F^p H^{2p}  ∧  conj(ι(α)) ∈ F^p H^{2p} }`

Here:
- `ι` is induced by `ℚ_X[0] → ℂ_X[0] → Ω^•_hol`.
- `F^p` is the set-theoretic image of `ℍ^{2p}(σ_{≥p} Ω^•_hol) → ℍ^{2p}(Ω^•_hol)`.
- `conj` is the map induced on `H^*(X; ℂ)` by complex conjugation of the constant coefficient sheaf. It is moved to `H_dR` through the holomorphic Poincaré lemma quasi-isomorphism, which is proved in the repo.

This is `H^{2p}(X,ℚ) ∩ F^p ∩ \bar F^p = H^{2p}(X,ℚ) ∩ H^{p,p}` (Voisin I, 7.3 and 8.1; Deligne, Clay description). It is the
standard definition. All five listed traps were checked and do not apply (details below). The closure has no
`sorry`, `axiom`, `opaque` declaration, `implemented_by`, `native_decide` or `extern`. The only hit for "opaque"
is in a docstring (`Definitions/Algebra/DeRham/Basic.lean:99`).

## Definition table

| definition | file:line | verdict | reason |
|---|---|---|---|
| `holomorphicFunctionSheafToTypes` / `holomorphicFunctionPresheaf` / `holomorphicFunctionSheaf` | `Definitions/AlgebraicGeometry/ComplexPoint/AnalyticSheaf.lean:48,64,78` | OK | Sections are `C^ω⟮𝓘(ℂ, Fin d → ℂ), U; ℂ⟯`, i.e. complex-analytic (holomorphic) functions in the charts. Over `𝕜 = ℂ`, `ω` means analytic. It is not C^∞ over ℝ. |
| `ChartedSpace (Fin d → ℂ) (ComplexPoint X)` (charts `localChart`) | `L/AlgebraicGeometry/ComplexPoint/Manifold.lean:122` | OK (boundary with area A) | The charts are evaluations of algebraic étale coordinates `MvPolynomial (Fin d) ℂ →ₐ Γ(U)` (`SmoothCoordinates.lean:100-129`). These coordinates are chosen with `Classical.choice` on a type that is proved nonempty. Every choice is a subatlas of the standard holomorphic atlas (`isManifold_omega` is proved), so the resulting `𝒪` does not depend on the choice. |
| `SmoothOfRelativeDimension.of_isIntegral` (d = `dim X.left`) | `L/AlgebraicGeometry/Smooth/Equidimensional.lean:156` | OK | This is a Prop instance with a real proof. `dim` (`Definitions/Topology/Dimension/Basic.lean:35`) has a junk value 0 for infinite dimension, but the instance proves `dim X = n` for the actual relative dimension. |
| `Algebra.DeRham.Form`, `extDeriv`, `differential` | `Definitions/Algebra/DeRham/Basic.lean:315,389,394` | OK | `⋀^p_A Ω_{A/ℂ}` with the universal odd derivation. Correctness does not depend on this construction, because the forms are compared with analytic `extDerivWithin` (next row). |
| `chartSection`, `chartSectionDifferential`, `chartDerivation`, `chartWedge`, `chartEvaluationHolo`, `chartEvaluation` | `ADF.lean:140,193,340,487` | OK | The derivative is `fderivWithin ℂ` into `(Fin d → ℂ) →L[ℂ] ℂ`: ℂ-linear covectors, so these are (p,0)-forms and not real 1-forms. `chartEvaluation_differential` (ADF.lean:634) proves that the algebraic `d` matches the analytic `extDerivWithin`. |
| `chartEvaluationKernel` | `ADF.lean:677` | OK | Kernel of evaluation at every point of every chart domain meeting U, i.e. forms that vanish pointwise. |
| `HolomorphicForm X d U p` | `ADF.lean:820` | OK | `⋀^p Ω_{𝒪(U)/ℂ}` modulo the pointwise-zero forms. This is exactly the image in holomorphic p-forms on U. Locally it is surjective, because chart coordinates lie in `𝒪(U)`, so `Σ f_I dz_I` is realized. After sheafification it is `Ω^p_hol`. Consistent with the proved `holomorphicForm_eq_zero_of_lt` (vanishes for p > d; C^∞ complex forms would survive up to degree 2d). |
| `holomorphicFormDifferential`, `holomorphicFormRestriction`, `holomorphicFormOfConstant` | `ADF.lean:828,838,852` | OK | Descent of `d` and restriction to the quotient. The constant `c` maps to the class of the constant function. |
| `holomorphicDeRhamPresheaf` / `…Differential` / `…PresheafComplex` | `HdR.lean:61,96,117` | OK | Degree p holds p-forms; `CochainComplex.of` gives `d p (p+1)`. |
| `holomorphicDeRhamSheaf` (sheafification) / `…SheafDifferential` / `holomorphicDeRhamComplex` | `HdR.lean:222,239,250` | OK | Sheafified term by term with `presheafToSheaf`. |
| `constantsToHolomorphicDeRhamZero(Sheaf)` / `constantsToHolomorphicDeRhamComplex` | `HdR.lean:135,353,487` | OK | ℂ goes to constant 0-forms. |
| `constantsToHolomorphicDeRhamComplex_quasiIso` (holomorphic Poincaré lemma) | `HdR.lean:520` (+ `…quasiIsoAt_zero/succ` 501,512) | OK | Proved (no sorry). It is a strong check on the complex: its cohomology sheaves are ℂ in degree 0 and 0 elsewhere. |
| `holomorphicDeRhamComplexInt` `Ω•(X)` | `HdR.lean:561` | OK | `extend embeddingUpNat` (n ↦ n) puts `Ω^p` in ℤ-degree p and 0 in negative degrees. d = `dim X.left`. |
| `constantComplexSheafComplexInt`, `constantsToHolomorphicDeRhamComplexInt` (+ quasiIso instance) | `HdR.lean:532,600,607` | OK | `ℂ_X[0] → Ω•`. Quasi-iso via `quasiIso_extendMap_iff`. |
| `conjConstantComplexPresheaf` / `conjConstantComplexSheaf` / `conjConstantComplexComplex` / `conjConstantComplexSheafComplexInt` | `HdR.lean:333,343,541,553` | OK | `starRingEnd ℂ` on each section of the constant presheaf, then sheafified. It is antilinear and not the identity. `complexScalarComplexInt_comp_conj` (`L/…/HolomorphicDeRham.lean:343`) proves `c ∘ conj = conj ∘ c̄`. |
| `AnalyticAdditiveSheaf`, local `HasDerivedCategory.standard` | `F.lean:68,71,444` | OK | Local instance only. `SmallShiftedHom` and the group structure transported through `DerivedCategory.Q` are canonical (any localization gives the same result). |
| `Hypercohomology` `ℍ^n(X; K)` | `F.lean:271` | OK | `SmallShiftedHom W (ℤ_X[0]) K n` with W = quasi-isos of ℤ-indexed complexes of abelian sheaves on X(ℂ). This is `Hom_{D(Sh)}(ℤ_X, K[n]) = ℍ^n(X, K)`. |
| `hypercohomologyAddCommGroup` | `F.lean:303` | OK | Transported through `SmallShiftedHom.equiv … DerivedCategory.Q`. It does not affect any carrier below, because all carriers are images and preimages of set maps. |
| `hypercohomologyMap` | `F.lean:352` | OK | Post-composition with `mk₀ f`. Any sign convention of the shift does not change images or preimages. |
| `DeRhamHypercohomology` `H_dR^n(X)` | `F.lean:331` | OK | `ℍ^n(X; Ω•(X))`, holomorphic de Rham hypercohomology. |
| `complexConstantCohomologyDeRhamEquiv` / `…AddEquiv` | `F.lean:341,782` | OK | `postcompEquiv` by a proved quasi-iso. It is a true bijection `H^n(X;ℂ) ≅ H_dR^n`. |
| `hypercohomologyAddEquivConstantCohomology` | `F.lean:478` | OK (touches the excluded `Sheaf.H`) | `precompEquiv.symm ≫ postcompEquiv` by the canonical isos `extendSingleIso` and `ULift ℤ ≅ ℤ`. No automorphism or sign twist. Naturality is proved (`_map`, `_symm_map`). |
| `fieldToComplexConstantSheaf`, `constantFieldSheafComplexInt`, `fieldToComplexConstantSheafComplexInt`, `fieldToHolomorphicDeRhamComplexInt` | `F.lean:78,87,99,110` | OK | `algebraMap K ℂ` on constant sheaves, then composed with `ℂ_X → Ω^0`. |
| `fieldToDeRhamCohomology` / `…Linear` | `F.lean:656,676` | OK | `ι = hypercohomologyMap(K[0]→Ω•) ∘ (equiv to Sheaf.H)^{-1}`. K-linearity is proved. |
| `SMul ℂ H_dR` / `deRhamHypercohomologyComplexModule` / `deRhamHypercohomologyModule` (restrictScalars) | `F.lean:615,627,636` | OK | c acts through `scalarHolomorphicDeRhamComplexInt c` = sheafified `c • id` on forms (`L/…/HolomorphicDeRham.lean:51-107`). It is a genuine ℂ-action, not conj. It does not affect the carrier of `Hdg`. |
| `hodgeFilteredDeRhamComplex` `F^p Ω•` | `F.lean:687` | OK | `stupidTrunc (embeddingUpIntGE p)` = `(K.restriction e).extend e` with `e n = p + n`. It keeps `Ω^q` in degree q for q ≥ p and puts 0 below. This is the stupid (bête) truncation σ_{≥p}, with no degree shift. |
| `hodgeFilteredDeRhamInclusion` (`stupidTruncInclusion`) | `F.lean:697`; `HodgeConjecture/Mathlib/Algebra/Homology/StupidTruncation.lean` | OK | The iso `stupidTruncXIso` on retained degrees and 0 elsewhere. The chain-map property is proved using `IsTruncGE` (a Mathlib instance for `embeddingUpIntGE`). The `Classical` `choose` is over a unique preimage of an injective map, so it is harmless. |
| `FilteredDeRhamHypercohomology`, `filteredToDeRhamCohomology` | `F.lean:726,733` | OK | `ℍ^n(σ_{≥p}Ω•) → ℍ^n(Ω•)`. |
| `hodgeFiltration` / `hodgeFiltrationComplexSubmodule` `F^p H_dR^n` | `F.lean:741,761` | OK | `AddMonoidHom.range`, i.e. the image, which is Deligne's definition. For p ≤ 0 it is ⊤. For p > n it should be ⊥ (source concentrated in degrees > n). It is not identically ⊤ or ⊥. |
| `deRhamConj` / `deRhamConjSemilinear` | `F.lean:822,846` | OK | `e ∘ H(conj) ∘ e^{-1}` with `e : H^n(X;ℂ) ≅ H_dR^n`. This is conjugation for the real structure `H(X;ℝ)⊗ℂ`. Semilinearity is proved (`deRhamConj_smul`), so it is not ℂ-linear and not the identity. |
| `conjHodgeFiltrationComplexSubmodule` | `F.lean:856` | OK (see C3) | `comap conj F^q`. It equals `conj(F^q)` because conj is an involution. The involution property is true but not stated in the repo. |
| `hodgePiece` | `F.lean:865` | OK | `F^p ⊓ conj⁻¹F^q`, which is `H^{p,q}` for projective X and p+q=n. |
| `hodgeClasses` / `Hdg^p(X; K)` | `F.lean:875,884` | OK | `comap ι (restrictScalars K (hodgePiece p p (↑(2p))))`. The casts `(p:ℕ)→ℤ` and `(2*p:ℕ)→ℤ` agree on both sides (the `comap` would not type-check otherwise). |

## Traps from the brief

1. **Holomorphic vs C^∞.** Holomorphic. The functions are `C^ω` over ℂ, the derivatives are `fderivWithin ℂ` into `→L[ℂ]` covectors, and `Ω^p = 0` for `p > d` is proved (`holomorphicDeRhamSheaf_isZero_of_lt`, HdR.lean:229). With smooth complex forms, degrees up to 2d would be nonzero.
2. **Truncation direction and indexing.** `embeddingUpIntGE p` has image `{n ≥ p}`. Stupid truncation keeps degrees, with no shift. `Ω•` sits in degrees `0..d` through `embeddingUpNat`. The ℕ→ℤ casts are consistent.
3. **Conjugation.** `starRingEnd ℂ` on the constant coefficient sheaf, moved across a proved quasi-isomorphism. It is proved conjugate-linear, so it is neither the identity nor ℂ-linear.
4. **F^p always ⊤ or ⊥.** No. F^p is the image of a non-degenerate map, and both complexes are the genuine ones. `Hypercohomology` is built from the real derived-category Hom and is not a junk type.
5. **Junk, choice, local instances, axioms.** Choices use `Classical.choice` only on proved-nonempty types (étale coordinates) and on the unique preimage in `stupidTruncInclusionApp`. The `dim` junk value is ruled out by a proved instance. The local `HasDerivedCategory` instance is canonical. No sorry, axiom, opaque, implemented_by or native_decide.

## Ranked concerns (all minor; none changes the truth value of the statement)

**C1 (low, cross-area dependency).** "Holomorphic" means holomorphic for the charts of `ComplexPoint X` from `localEtaleCoordinates`, and for the topology `analyticTopology` (`Definitions/AlgebraicGeometry/ComplexPoint/Basic.lean:257`, area A). The charts are proved to be homeomorphisms whose inverse maps make regular functions analytic, which pins them to the standard structure. Faithfulness of area B still depends on area A's topology being the classical one.
Sanity lemma: for `X = 𝔸^1_ℂ` (or an open of it), the coordinate function evaluation `Point.evaluate ⊤ T` is a section of `holomorphicFunctionSheaf X 1` over `⊤`, and `z ↦ conj z` is **not** one.
```lean
example : ∃ U, (fun z => starRingEnd ℂ (coord z)) ∉ (holomorphicFunctionSheafToTypes A1 1).presheaf.obj U
```

**C2 (low, unstated property).** `hodgeFiltration X p n = ⊥` when `p > n` is true, but it is not stated anywhere. It is the cleanest guard against a reversed or shifted truncation: σ_{≤p} or an off-by-one shift would give ⊤ or a nonzero result.
```lean
lemma hodgeFiltration_eq_bot_of_lt [IsIntegral X.left] [Smooth X.hom] {p n : ℤ} (h : n < p) :
    hodgeFiltration X p n = ⊥
lemma hodgeFiltration_eq_top_of_nonpos [IsIntegral X.left] [Smooth X.hom] {p : ℤ} (h : p ≤ 0) (n : ℤ) :
    hodgeFiltration X p n = ⊤          -- via stupidTruncInclusion_isIso + IsStrictlyGE 0
```

**C3 (low, comap vs image).** `conjHodgeFiltrationComplexSubmodule` is `comap conj F^q`. This equals `conj(F^q)` only because conj is an involution, which is not proved. For `hodgeClasses`, p = q, so the intersection is symmetric anyway. The rational condition further reduces to `ι α ∈ F^p` once `conj ∘ ι_ℚ = ι_ℚ`.
```lean
lemma deRhamConj_involutive (n : ℤ) (α : H_dR^n(X)) : deRhamConj X n (deRhamConj X n α) = α
lemma deRhamConj_fieldToDeRham (n : ℕ) (β : H^n(X; ℚ)) :
    deRhamConj X n (fieldToDeRhamCohomology ℚ X n β) = fieldToDeRhamCohomology ℚ X n β
lemma mem_hodgeClasses_iff_rat (p : ℕ) (β : H^(2*p)(X; ℚ)) :
    β ∈ Hdg^p(X; ℚ) ↔ fieldToDeRhamCohomology ℚ X (2*p) β ∈ F^p H_dR^(2*p)(X)
```

**C4 (low, non-triviality of conj and F^p is not witnessed).** No lemma shows that `deRhamConj` is non-trivial on a nonzero class, or that `F^1 H^1` is a proper nonzero subspace (for example on an elliptic curve). The definitions are right by inspection, but a witness would guard against a degenerate `Hypercohomology` group structure.
```lean
lemma deRhamConj_zero_unit [Nonempty (ComplexPoint X)] (c : ℂ) :
    deRhamConj X 0 (c • one) = (starRingEnd ℂ c) • one      -- `one` = image of the constant 1 ∈ H^0(X;ℚ); also `one ≠ 0`
lemma hdg_zero_eq_top : Hdg^0(X; ℚ) = ⊤                    -- guards F^0 = ⊤ and the cast (2*0)
```

**C5 (informational).** The ℂ-module structure on `H_dR` and the group structure on `ℍ` are transported from the derived category. They do not enter the carrier of `Hdg^p`, which is built only from set images and preimages. The K-module structure on `H^n(X;K)` that `algebraicCycleClassSpan` uses (`fieldCohomologyClass`/`fieldScalarSheaf`, F.lean:579-601) is the natural one. The span itself belongs to another area.

## Not done
- Nothing was compiled and `#print axioms HodgeConjecture` was not run, because a concurrent `.lake` build was in progress. Recommended once the build finishes: `#print axioms AlgebraicGeometry.ComplexPoint.hodgeClasses` and the C2/C3 lemmas as `example`s.
