# Hodge conjecture statement audit, area D: statement-level and repo-wide hygiene

* Repo: `external/hodge` (github.com/Paul-Lez/HodgeConjecture), HEAD `5d0b87f`.
* Toolchain: Lean v4.33.1, Mathlib `0df444a` (tag v4.33.1).
* Statement: `HodgeConjecture/Statement.lean:43-46`.
* Import closure: 255 local modules (`hodge_closure.txt`). Every search below strips comments and covers exactly those 255 files.

**Verdict for area D: no BUG found.** The hypotheses match "non-singular complex projective variety". They are satisfiable, which was checked by machine. Both sides of `≤` live in the same ℚ-module. The closure has no axiom, `sorry` or checker-weakening option. The remaining items are CONCERNs about trust surface and process.

## Machine checks

All checks ran out of tree in the scratchpad. The repo and its `.lake` were not changed.
Scratchpad root: `/tmp/claude-1000/-home-jbecart-tmp-mathTest-nanoprover/d46b9b24-f0da-4c40-91d4-15c0dea51629/scratchpad/sanity/`.

* `build.py` compiled all 255 closure modules with `lean -o` into `sanity/out`, against the repo's pinned Mathlib oleans. Result: 255 OK, 0 failed.
* `src/StmtCheck.lean` (imports `HodgeConjecture.Statement` and `Sanity`, which imports all of `Mathlib`) gave these results:
  * `#print axioms HodgeConjecture` reports only `[propext, Classical.choice, Quot.sound]`. There is no `sorryAx` and no custom axiom.
  * `#print HodgeConjecture` with full names gives `∀ (X : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of ℂ))) [AlgebraicGeometry.IsIntegral X.left] [AlgebraicGeometry.Smooth X.hom] [AlgebraicGeometry.IsProjective X.hom] (p : ℕ), Hdg^p(X; ℚ) ≤ AlgebraicGeometry.ComplexPoint.algebraicCycleClassSpan X p`.
    * `IsIntegral` and `Smooth` are Mathlib's.
    * `IsProjective` is the repo's.
    * `↧ℂ` elaborates to `CommRingCat.of ℂ`.
    * There is no capture by other `Smooth`/`IsIntegral` names (for example root `IsIntegral` or `RingHom.Smooth`).
  * `Hdg^p(X; ℚ) = hodgeClasses ℚ X p := rfl` checks. The notation hits the right constant, not `HodgeStructure.Pure.hodgeClasses`.
  * `(inferInstance : Module ℚ (Sheaf.H (constant ℚ sheaf on X(ℂ)) n)) = fieldCohomologyModule ℚ X n := rfl` checks.
  * `Hdg^p(X;ℚ) ≤ algebraicCycleClassSpan X p ↔ ∀ c, c ∈ Hdg^p(X;ℚ) → c ∈ algebraicCycleClassSpan X p := Iff.rfl` checks. So `≤` is plain inclusion of carriers inside the same type.
  * With `pp.explicit`, the type is `@LE.le (@Submodule Rat (Sheaf.H …constantSheaf… (AddCommGrpCat.of ℚ)…))`. The topology is `Point.analyticTopology`, built on the standard metric topology of ℂ (`Complex.instNormedField`). No exotic ring or topology instance appears.
  * `example (h : HodgeConjecture) (p) : Hdg^p(ptX; ℚ) ≤ algebraicCycleClassSpan ptX p := h ptX p` checks, with `ptX := Over.mk (𝟙 (Spec ↧ℂ))`.
* `src/Sanity.lean` is the non-vacuity sanity lemma, suggested for upstream.
  * It proves `IsProjective (𝟙 (Spec ↧ℂ))` by building an explicit presentation. The section `Spec ℂ → ℙ(Fin 1; Spec ℂ)` goes through `Proj.awayι` at `x₀` and `x₀ ↦ 1`. It is a closed immersion by `IsClosedImmersion.of_comp`, because `toBase` is proper, hence separated.
  * It then proves `∃ X : Over (Spec ↧ℂ), IsIntegral X.left ∧ Smooth X.hom ∧ IsProjective X.hom`.
  * Axioms used: the standard three only.

```lean
-- core of Sanity.lean (builds against HodgeConjecture/Definitions/AlgebraicGeometry/ProjectiveSpace.lean)
def s : Spec ↧ℂ ⟶ ℙ(Fin 1; Spec ↧ℂ) := pullback.lift (𝟙 _) pt (terminal.hom_ext _ _)
lemma s_toBase : s ≫ toBase (Fin (0 + 1)) (Spec ↧ℂ) = 𝟙 _ := pullback.lift_fst _ _ _
instance : IsClosedImmersion s := by
  have : IsClosedImmersion (s ≫ toBase (Fin (0 + 1)) (Spec ↧ℂ)) := by rw [s_toBase]; infer_instance
  exact IsClosedImmersion.of_comp s (toBase (Fin (0 + 1)) (Spec ↧ℂ))
instance : IsProjective (𝟙 (Spec ↧ℂ)) := ⟨⟨⟨0, s, s_toBase⟩⟩⟩
```

## Findings

| # | item | file:line | verdict | reason |
|---|------|-----------|---------|--------|
| 1 | Base `Over (Spec ↧ℂ)` | Statement.lean:44; Mathlib/CategoryTheory/ConcreteCategory/Notation.lean:108-121 | OK | `↧` is a custom `elab_rules`. It elaborates to `CommRingCat.of ℂ` with the standard ring structure (checked by `#print`). The universe is 0, so `X.left : Scheme.{0}`, which is harmless. |
| 2 | `Smooth X.hom` | Mathlib `AlgebraicGeometry/Morphisms/Smooth.lean:62`; `RingTheory/RingHom/Smooth.lean:74`; `RingTheory/Smooth/Basic.lean:540` | OK | Mathlib's scheme `Smooth` is affine-locally `RingHom.Smooth = Algebra.Smooth = FormallySmooth ∧ FinitePresentation`. That is the right notion (locally finite presentation included). It is not formally-smooth-only and not étale. |
| 3 | `IsProjective X.hom` | Definitions/AlgebraicGeometry/ProjectiveSpace.lean:52-53,128-150 | OK (trust surface, see 16) | **This is repo-defined, not Mathlib's**: Mathlib at this commit has no `IsProjective` for schemes. It means: there exist `d` and a closed immersion `X → ℙ^d_T` with `i ≫ toBase = f`. Here `ℙ^d_T := T ×_{Spec ℤ} Proj(ℤ[x₀..x_d])`, a pullback over the terminal object, using the total-degree grading `MvPolynomial.gradedAlgebra` / `homogeneousSubmodule` and `ULift ℤ`. That is Hartshorne-projective. Over the affine base `Spec ℂ` it coincides with EGA/Stacks projective. It also gives `IsProper` (line 152), hence finite type and separated. |
| 4 | `IsIntegral X.left` | Mathlib `AlgebraicGeometry/Properties.lean:240` | OK | Mathlib's notion: nonempty, and every nonempty open has integral sections. Restricting to integral X is standard and harmless. A smooth projective X is the disjoint union of its connected components. Each component is integral (a regular local ring is a domain, and connected + locally irreducible Noetherian implies irreducible). `H^{2p}(X;ℚ)`, the Hodge decomposition and cycles all split over components, and the empty X is trivial. Nothing in the repo proves this reduction for its specific definitions, but that is a proof obligation, not a fidelity gap. |
| 5 | Joint satisfiability (vacuity risk) | — | OK (checked by machine) | `Spec ℂ` satisfies all three instances (`Sanity.lean`), and `HodgeConjecture` instantiates at it (`StmtCheck.lean`). So the statement is not vacuous through the hypotheses. The repo itself has **no** such lemma, and no instance for any concrete variety (see 17). |
| 6 | Hypotheses are `Prop` classes | Statement.lean:44-45 | OK | All three binders are `Prop`-valued, so `hodgeClasses` and `algebraicCycleClassSpan` cannot depend on a choice of instance data. |
| 7 | Same ambient module and meaning of `≤` | Statement.lean:46; Hodge/Filtration.lean:875-884; Cycle/FundamentalClass.lean:146-148 | OK (checked by machine) | Both sides have type `Submodule ℚ (H^(2*p)(X; ℚ))` with the same `Module` instance (`fieldCohomologyModule`). `H^n(X;ℚ)` is Mathlib `Sheaf.H` of the constant sheaf ℚ on `X(ℂ)^an` (`Filtration.lean:294`). `≤` is `Iff.rfl` to membership inclusion. The degree is `2 * p : ℕ` on both sides. `algebraicCycleClassSpan` = `sSup` of spans = the ℚ-span of the component classes, matching Deligne's "rational linear combination of cl(Z)". |
| 8 | ℚ-module structure on `Sheaf.H` is repo-defined | Hodge/Filtration.lean:579-600 | OK | This is an orphan global instance on a Mathlib type. It acts by `Sheaf.H.map` of scalar multiplication on the coefficient sheaf and is built with `Module.ofMinimalAxioms` (axioms proved). A ℚ-module structure on an additive group is unique, so span and `≤` mean what they should. Mathlib only has a ℤ-linear structure on `Ext` here, so there is no diamond with K = ℚ. |
| 9 | `axiom` / `opaque` / `sorry` / `admit` | closure (255 files) | OK | 0 hits for each. `#print axioms` confirms this. |
| 10 | `implemented_by` / `extern` / `native_decide` / `unsafe` / `ofReduceBool` / `trustCompiler` | closure | OK | 0 hits. |
| 11 | `set_option` | closure: 312 hits | OK | The options used: `backward.isDefEq.respectTransparency` ×175, `backward.defeqAttrib.useBackward` ×85, `backward.isDefEq.respectTransparency.types` ×21, `linter.*` ×28, `maxHeartbeats 800000` ×2 (Lemmas/AlgebraicTopology/Support/CohomologyInjectiveModel.lean:105, CohomologyFlasqueModel.lean:69), and `quotPrecheck false` ×1 (Definitions/AlgebraicGeometry/Cohomology/WithSupport.lean:44, a notation declaration only). All are elaborator or linter options. There is no `debug.skipKernelTC` and no `allowUnsafeReducibility`, and the kernel checks everything. |
| 12 | Reducibility attributes | e.g. Filtration.lean:63, WithSupport.lean:66, LinearDual.lean:51, ComplexPoint/Basic.lean:238,256 | OK | `attribute [local implicit_reducible]` and `@[instance_reducible]` affect elaboration only. There are no `@[irreducible]`, `irreducible_def` or attribute erasures (`attribute [-…]`). |
| 13 | Local copy of the topology instance on `ComplexPoint X` | Cycle/FundamentalClass.lean:36-37 | OK | `local instance … := Point.analyticTopology` duplicates the global instance (ComplexPoint/Basic.lean:257) with the same term, so there is no semantic change. Open PR #216 removes it for kernel-time reasons. |
| 14 | Other `local instance` / `attribute [local instance]` (50 sites) | e.g. Support/DerivedSections.lean:113,117; DerivedSectionsLocalization.lean:100,104; Hodge/Filtration.lean:71,444; Cohomology/GlobalSections.lean:140; AmbientInjectiveResolution.lean:78; Singular/Sheaf/CochainOpenCone.lean:30 | OK / note for A and C | Most are local `HasDerivedCategory` instances. These are *data*: a choice of derived-category model. The statement's objects avoid depending on that choice. `Hypercohomology` uses `Localization.SmallShiftedHom` (Filtration.lean:86-90), and `Sheaf.H` uses `HasExt`, which is `Prop`-valued (Filtration.lean:283-288). Any class routed through a chosen model is canonical only up to the canonical identification, so reviewers A and C should confirm that no final class depends on the model. The rest are `overSpecAlgebra`, `MvPolynomial.gradedAlgebra`, `specializationOrder` (KrullDimension), `chartFieldModule`/`chartFieldTower` and local algebra structures on coordinate rings. None overrides the ring structure of ℂ or ℚ, the ℚ-module structure, or the topology on points. |
| 15 | Global orphan instances on Mathlib types | ComplexPoint/Basic.lean:257 (`TopologicalSpace (Point R X)`); Lemmas/…/ComplexPoint/AffineScheme.lean:45 (`TopologicalSpace (R →ₐ[ℂ] ℂ)`); Lemmas/…/ComplexPoint/Projective.lean:63 (`TopologicalSpace (Projectivization ℂ _)`); Filtration.lean:579,588 (see 8) | OK | I searched Mathlib at this commit: it has no competing `TopologicalSpace` instance on `AlgHom` or `Projectivization`, so there is no diamond. The two topology orphans are in the `Lemmas` layer. |
| 16 | Notations used by the statement: `Hdg^`, `H^`, `F^`, `H_dR^`, `ℍ^`, `H_[Z]^` | Filtration.lean:279,294,335,692,769,884; Lemmas/AlgebraicTopology/Singular/Cohomology.lean:58,73,113; Definitions/AlgebraicTopology/Singular/Cohomology.lean:61,71,113,125,144; Cohomology/WithSupport.lean:47; Support/Cohomology.lean:52 | OK | All are `scoped`, except `ℤᵘᵖ` (Mathlib/Algebra/Homology/Notation.lean:20) and the `𝓒…` constant-sheaf notations (Sheaf/Constant.lean:48-76). `H^` has three scoped variants (ComplexPoint, Singular, and relative Singular). Collisions are resolved by elaboration, and the statement's two sides unify, as the machine checks confirm. Importing all of `Mathlib` together with the statement in `StmtCheck.lean` caused no notation clash. There are no `macro_rules` that redefine notation used in the statement. |
| 17 | No in-repo non-vacuity or non-triviality sanity lemmas | repo-wide | CONCERN | The repo has no instance showing that any concrete X, even `Spec ℂ` or `ℙ^n_ℂ`, satisfies `[IsIntegral][Smooth][IsProjective]`. It also has no proof of the reverse inclusion "algebraic ⇒ Hodge" (#205), and no Hodge or non-Hodge example (#211, #212). The only theorems are for codimension 0 and dimension 0 (Other/AlgebraicGeometry/Hodge/CodimensionZeroNonvanishing.lean:59-68, DimensionZero.lean:49). They are conditional on the instances, so they do not rule out vacuity. Suggested additions: (a) `Sanity.lean` above; (b) `IsProjective`, `Smooth` and `IsIntegral` for `ProjectiveSpace.toBase (Fin (n+1)) (Spec ↧ℂ)`. `IsProjective` there is trivial (take the presentation `𝟙`); `Smooth` and `IsIntegral` need work. |
| 18 | `IsProjective` is a local definition, not upstream | ProjectiveSpace.lean:147 | CONCERN (minor) | It is correct as stated (item 3), but it is part of the trusted surface. The file says it tracks mathlib4#26061. When that PR lands, the local definition should be replaced by Mathlib's, or an equivalence with it should be proved. |
| 19 | Guide copies of the statement | HodgeGuide/Overview.lean:44-50; HodgeGuide/Statement.lean:130-136 | OK | Same proposition: the text is identical and `example : @Guide…HodgeConjecture = @HodgeConjecture := rfl` is checked. Caveats: `HodgeGuide` is not a default target (lakefile.toml:3), and CI builds the guide only on push to `main` (`lake exe hodge-guide`, skipped for PRs). So a drifted guide copy is caught only after merge. The guide also imports `Other`, but the `rfl` guards against `Other` instances changing the elaboration. |
| 20 | `scripts/CheckStatementImports.lean` | scripts/CheckStatementImports.lean:38-46; lakefile.toml:3,26-29 | OK | It does what it claims: it is a default target, and it fails the build if any module under the `Other` prefix is in `allImportedModuleNames` after `import HodgeConjecture.Statement`. **What it does not do**: check for axioms or `sorry`, or run any semantic check. `check_import_layers.py` is syntactic reachability only. `PropOnlyDefinitions.lean` is a report and is not run in CI. |
| 21 | No CI guard against `sorry` or axioms | .github/workflows (single workflow) | CONCERN (process) | The statement is `sorry`-free now (item 9), but nothing enforces it. `trust-action` only exports an index. Suggest a `run_cmd` next to `CheckStatementImports` that fails if `collectAxioms `HodgeConjecture` is not ⊆ {propext, Classical.choice, Quot.sound}. See also open PR #132. |
| 22 | Codimension convention (`Order.coheight x = p`) | FundamentalClass.lean:146-148 | OK (for area C) | Consistency check from `Other`: `coheight_genericPoint_eq_zero` and `algebraicCycleClassSpan_zero_eq_top` (CodimensionZeroNonvanishing.lean:59) show that coheight 0 is the generic point, which is the right orientation for codimension. Area C should verify the full claim. |
| 23 | Matching Deligne (Clay) | Statement.lean:24-46 | OK | "X non-singular complex projective variety; every Hodge class in H^{2p}(X,ℚ) is a ℚ-linear combination of cl(Z)" maps to: smooth + projective + integral over ℂ; `Hdg^p(X;ℚ) ⊆ span_ℚ{cl(Z) : Z integral of codim p}`, for all `p : ℕ`. Only the inclusion is asserted, as in Deligne. Whether `Hdg^p` really picks out the (p,p) classes (F^p ∩ conj F^p in `H_dR`) belongs to area B, and whether `cl(Z)` is the right class belongs to area C. |

`HodgeConjecture/Variants.lean` (Lefschetz (1,1), dim ≤ n, abelian varieties) is outside the statement closure and was not audited.

## Already-known upstream concerns (do not re-report)

Open unless marked otherwise.

* **#57**: https://github.com/Paul-Lez/HodgeConjecture/issues/57. The Borel–Moore layer rests on 14–15 hypothesis structures that are never inhabited. Only `Other`, so not the statement.
* **#100**: https://github.com/Paul-Lez/HodgeConjecture/issues/100. `RationalDualizingComplex` (and its orientation input) is inhabited by trivial data. Only `Other`.
* **#47**: https://github.com/Paul-Lez/HodgeConjecture/issues/47. `HodgeStructure.Pure.hodgeClasses` shadows or duplicates the statement's `hodgeClasses` and is not connected to it.
  * Current state: it is in `Lemmas/LinearAlgebra/HodgeStructure.lean:70` under namespace `HodgeStructure.Pure`, and I checked that the notation resolves to the correct constant.
  * The connection is PR #103 (open): https://github.com/Paul-Lez/HodgeConjecture/pull/103. It connects the Hodge-structure API only *given* a Hodge decomposition hypothesis.
* **#46**: https://github.com/Paul-Lez/HodgeConjecture/issues/46. The statement import closure contains many modules that contribute nothing, so the audit surface is large. The maintainer has since commented that the central number was wrong.
* **#173** (hypercohomology is done ad hoc: https://github.com/Paul-Lez/HodgeConjecture/issues/173), **#174** (do singular cohomology properly: https://github.com/Paul-Lez/HodgeConjecture/issues/174), **#15** (check cohomology definitions: https://github.com/Paul-Lez/HodgeConjecture/issues/15). Acknowledged design debt in the definitions areas A and B review.
* **#205** (prove every algebraic class is Hodge), **#211** (Hodge class examples), **#212** (non-Hodge examples), **#204**/**#203** (compute fundamental classes explicitly). This is the acknowledged lack of non-triviality sanity checks (my item 17). Related open PRs: #8, #26 (non-Hodge example handoffs) and #201 (hyperplane class in ℙ², unchecked autoformalisation).
* **#177** (hunting bad definitions), **#164** (remove tactic-mode defs), **#106** (make local instances global), **#108** (should coefficient sheaves be ℂ-linear?).
* **PR #216**: https://github.com/Paul-Lez/HodgeConjecture/pull/216. Removes the local analytic-topology copy in FundamentalClass.lean (my item 13).
* **PR #132**: https://github.com/Paul-Lez/HodgeConjecture/pull/132. Kernel-dependency audit of the statement (related to my item 21).
* **PR #12**: https://github.com/Paul-Lez/HodgeConjecture/pull/12. Self-contained challenge file.
  * Known defect (comment by @Deicyde): the generator drops instance hypotheses of data definitions whose use is elided with `sorry`, for example `[IsClosedImmersion i.left]` and `[Algebra.Etale …]`.
  * The committed snapshot is stale (pre-#19 `hodgeClasses`).
  * So that file must not be used as an audit proxy for the current statement.
* Closed or resolved and relevant: #53 and PR #89 (global notations scoped), #13 (statement must not depend on `Other`, now enforced by `CheckStatementImports`), PR #19 (Hodge classes defined by the (p,p) condition, not F^p alone).
