# Pre-emptive audit of Millennium-problem Lean statements (2026-09-25)

Rationale: the Navier–Stokes claim was judged with Comparator against formal-conjectures'
(FC) pre-existing statement. Future AI claims will be judged the same way, so a
misformalized statement is the cheapest way for a false claim to pass — or a true one to
be rejected. Auditing statements *before* a claim lands is work a small team can do well.

| Problem | Where stated | Verdict | Notes |
|---|---|---|---|
| Navier–Stokes (C)/(D) | FC `Millennium/NavierStokes.lean` | **faithful** | full audit + two-kernel Comparator: `NS_AUDIT.md` |
| Riemann Hypothesis | FC → Mathlib `RiemannHypothesis` | **faithful** | Mathlib's `riemannZeta` is the true continuation; s = 1 (junk value) excluded explicitly. FC deliberately omits ERH (naive Dedekind zeta has junk zeros). |
| P vs NP | FC `Millennium/PvsNP.lean` + `ForMathlib/Computability/{Complexity,BitstringEncoding}.lean` | **faithful** | Mathlib `TM2ComputableInPolyTime` (finite-state multi-stack TMs, time polynomial in encoded length). `List Bool` encoded via the generic list instance (3 bits/bit), pairs via self-delimiting blocks — linear blowups, so P/NP unchanged. NP = poly verifier + poly-bounded witness (Arora–Barak Def. 2.1). |
| BSD (weak, ℚ) | FC `Millennium/BSD.lean` + `Wikipedia/HasseWeil.lean` + Mathlib `EllipticCurve/LFunction.lean` | **faithful for ℚ** (the Clay case) | Euler factors per Silverman on local minimal models (good: 1−aT+qT², a = q+1−#E(F_q) incl. ∞; split/non-split mult.: 1∓T; additive: 1); compared with the continuation only on Re s > 3/2 (no junk-value leak); order at s = 1 matches Clay's "c(s−1)^r". Mordell–Weil taken as hypothesis `[AddGroup.FG …]`. Over K without a continuation the statement is vacuous (documented). |
| Hodge | **not in FC**; in progress at github.com/Paul-Lez/HodgeConjecture (`HodgeConjecture/Statement.lean`) | **TO AUDIT** (pick) | ~83k lines, ~9.8k lines of definitions in 61 files, 0 `sorry`, active daily; "autoformalisation tools were used extensively"; FC maintainer (2026-09-22): "currently being checked and refined". Hodge is the problem with rumored OpenAI progress. |
| Yang–Mills | not formalized (Zulip effort mentioned in FC #4685) | — | FC rejects opaque-placeholder statements. |

## Pick: independent audit of the Hodge statement
Statement: `∀ X : Over (Spec ℂ), [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (p : ℕ),
Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p` — matches Deligne's Clay text in shape.
Faithfulness rests on the definitions of `Hdg^p` (rational classes in H^{2p}(X(ℂ)^an; ℚ)
landing in H^{p,p} via the Hodge filtration), the cohomology (constant-sheaf cohomology,
Ext groups), and `algebraicCycleClassSpan` (fundamental classes of codim-p subvarieties).

Plan:
1. Trace the definition graph from `Statement.lean`; list every definition it depends on.
2. Check each against the standard mathematics (Deligne; Voisin, *Hodge Theory and Complex
   Algebraic Geometry I*), hunting junk values, degree/indexing errors, wrong topology,
   ℚ vs ℂ coefficient slips, and vacuity (definitions that collapse to ⊥ or ⊤).
3. Sanity theorems that would expose a collapse: e.g. p = 0 case provable; H^0 of an
   integral X is 1-dimensional; the class of X itself is nonzero; Lefschetz (1,1) shape.
4. Report findings as brief issues/PRs upstream (their AGENT.md: ASD-STE100 English,
   one-sentence commits).
