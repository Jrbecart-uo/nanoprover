# Independent fidelity audit: Lean statement of the Hodge conjecture

Target: github.com/Paul-Lez/HodgeConjecture @ `5d0b87f` (2026-09-24), Lean v4.33.1,
Mathlib `0df444a360` (same pin as formal-conjectures). Audited 2026-09-25.
The statement is not yet in formal-conjectures; FC maintainers point to this repo as
"currently being checked and refined" (FC #4685). Hodge is the Millennium problem with
rumored AI progress, so this is the statement a claim would likely be judged against.

**Scope:** does the Lean proposition say what Deligne's Clay statement says? Not a
proof, not a claim about the conjecture's truth.

## The statement
```lean
def HodgeConjecture : Prop :=
  ∀ (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (p : ℕ),
    Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p
```
`Hdg^p(X; ℚ)` = classes in H^{2p}(X(ℂ); ℚ) whose de Rham image lies in F^p ∩ conj(F^p);
`algebraicCycleClassSpan X p` = ℚ-span of fundamental classes of closures of points of
coheight p (integral codimension-p subvarieties).

## Machine checks (all reproducible; files in `verification/hodge/`)
| check | result |
|---|---|
| `lake build HodgeConjecture.Statement` | 4520 jobs, success (only linter warnings); rebuild is a no-op |
| `#print axioms HodgeConjecture` | propext, Classical.choice, Quot.sound — no `sorry` in any definition it uses |
| trusted surface (`TrustedSurface.lean`: constants reachable via types+values of defs, types of theorems) | **499 repo-local constants** (408 defs, 83 theorem statements, 4 inductives) in 78 modules — `trusted_surface.tsv` |
| repo-wide grep of the 255-module import closure | no `axiom`/`opaque`/`sorry`/`admit`/`implemented_by`/`extern`/`native_decide`/`unsafe`; no `set_option` weakening the kernel |
| `HypothesesSatisfiable.lean` | `Spec ℂ` over itself satisfies IsIntegral ∧ Smooth ∧ IsProjective (not vacuous) |
| `StatementInstantiates.lean` | the statement instantiates at that X |
| `ChartsHolomorphic.lean` | for every X: regular functions are holomorphic; the conjugate of a chart coordinate is holomorphic nowhere (the complex structure is genuinely complex, not real) |
| `GenericPointCoheight.lean` | generic point has coheight 0; its class lies in the p = 0 span (order direction correct) |

## Review (5 independent passes; `review_{A..E}.md`, definition-level tables)
| area | verdict | key points |
|---|---|---|
| A: X(ℂ) topology, sheaf cohomology | **OK** | one global topology instance = the analytic topology (Hausdorff, compact for projective X, complex manifold); `H^n(X;K)` = Mathlib `Sheaf.H` = Ext from constant ℤ-sheaf (so the Zariski-flasque trap that would make Hdg^p = 0 does not apply); supports = relative pair; `forgetSupport` = LES map |
| B: holomorphic forms, de Rham, F^p, conj | **OK** | forms holomorphic (Ω^p = 0 above dim proved); holomorphic Poincaré lemma proved as a quasi-iso; F^p = image of stupid truncation σ_{≥p}; conj conjugate-linear (proved) |
| C: algebraic cycle classes | **OK** | Mathlib order on scheme points is specialization (generic point on top) so coheight = codimension; class built from proven isos applied to a section nonzero on the smooth part of Z(ℂ) ⇒ nonzero multiple of [Z]; degree casts only transport indices |
| D: hypotheses, `≤`, hygiene | **OK** | Mathlib `Smooth` (incl. finite presentation), `IsIntegral`; repo-defined `IsProjective` (closed immersion into ℙ^d over the base) is correct; guide copies of the statement are the same proposition (`rfl`) |
| E: chart modules + 35 uncited modules | **OK** | charts cover X(ℂ), are proper local homeomorphisms with analytic transitions; of 19 gap modules, 15 enter only through kernel-checked isomorphisms, 4 carry values and are correct (`LinearDual`, `SingularClosedFiltration`, `ComplexOrientation`, `OpenInjectiveResolution`) |

**Verdict: no misformalization found.** The statement matches Deligne's Clay
formulation, is not vacuous, and every step we could reduce to a machine check passed.

## Residual gaps (argued, not machine-checked) — candidate upstream contributions
1. **Nonzero cycle class**: `cycleComponentSmoothSupportCoclassSection X x hx ≠ 0` is argued
   (all ingredients correct), not proved. If it failed the statement would become false
   (every class 0), not trivially true.
2. **Positive-dimensional witness**: satisfiability is only machine-checked for `Spec ℂ`
   (dimension 0); smoothness of ℙⁿ_ℂ is not in the pinned Mathlib or the repo.
3. **Unstated sanity lemmas** (true, useful as regression tests): `F^p H^n = ⊥` for p > n;
   `deRhamConj` involutive; injectivity of H^n(X;ℚ) → H^n(X;ℂ); `Hdg^0(X;ℚ) = ⊤`;
   `algebraicCycleClassSpan X 0 = ⊤`.
4. **CI**: no automated `#print axioms` / `sorry` gate on the statement (upstream PR #132
   related); the statement is clean today but nothing enforces it.
5. "Repo complex structure = classical analytification" cannot be a Lean theorem yet
   (Mathlib has no independent analytification to compare with).

Known upstream items not re-reported (see `review_D.md`): #57, #100, #47/#103, #46,
#173, #174, #15, #205, #211, #212; PR #216 removes a duplicated local topology instance.
