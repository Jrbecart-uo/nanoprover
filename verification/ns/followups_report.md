# Follow-up questions after the OpenAI Navier–Stokes and Euler blowup results

Research date: 2026-09-24. Sources were read directly where possible: both OpenAI PDFs, extracted with pypdf; the Lean repo, cloned; and the Constantin–Ignatova–Vicol PDF. Items marked **(secondhand)** come only from a web or news summary.

---

## 1. How the OpenAI proofs work

### Navier–Stokes (166 pp.; Theorem 1.1, with Cor. 10.6 for T³)

- **Statement.** For every ν>0 there is a force f ∈ C_c^∞(R³×(0,∞)) and a smooth (u,p) on R³×[0,1) with the following properties:
  - u(0)=0, and the solution has fixed compact support K.
  - The energy stays bounded: sup ‖u‖₂ < ∞.
  - limsup_{t↑1} ‖u‖_∞ = ∞.
  - This gives Clay (C). Compact support then gives (D).
- **The force is a residual.** They choose (u,p) and define f := ∂ₜu + u·∇u − νΔu + ∇p. The whole job is to make this residual extend C^∞ through t=1 while u blows up. This "manufactured solution" approach is why the forcing is essential.
- **Leading flow.** An axisymmetric swirling vortex whose leading profile is self-similar but anisotropic:
  - Scales: ℓ_r ≍ τ^{1/2}, ℓ_z ≍ τ^{1/2−h}, with 0<h<1/100 and τ=1−t.
  - Velocities: |u_θ|, |u_z| ≍ τ^{−1/2−h} (Type II), and u_r = O(τ^{−1/2}).
  - Viscosity stays in the leading radial balance: Re_r = O(1) while Re_θ ~ τ^{−h} → ∞.
  - The profiles E, U, Π are built analytically. There is ODE/moment matching (App. A, B), a "heat exterior" that solves the radial heat equation exactly, and an all-order correction in powers q^{2nh} (§5).
- **Where the force would blow up.** Joining the core to the exterior leaves a singular residual in an annulus. It has the form −div(annular stress T).
- **Cancelling that residual.** Two families of oscillatory, ring-shaped pulses are added. Each is seeded by an exponentially small force and grows by extracting energy from the background shear (Lifschitz–Hameiri / Friedlander–Vishik WKB, Craik–Criminale-type waves). Their averaged quadratic flux ⟨w⊗w⟩ supplies T. The idea resembles convex integration (Daneri–Székelyhidi): the "admissible stress cone" gives T = c₁v₁ + c₂v₂ with c₁, c₂ > 0 (Prop. 7.5, App. C). Later corrections (§§6–9) make the residual "flat" (O(q^N) for all N) at the singular point. The result is then localized in space (§10).
- **No computer-assisted bounds.** A grep of the paper finds no interval arithmetic or numerics used as proof. Everything is analytic, and all of it is formalized in Lean.
- **Relation to earlier work.** It builds on the Córdoba–Martínez-Zoroa(–Zheng) programme of forced amplification across scales, but uses the amplified pulses differently. Here they are not a cascade of layers; they "supply the missing force on a collapsing background vortex" (paper §1.1).
- **The Euler paper (57 pp.) is unforced.** Theorem 1.1 gives u₀ ∈ C_c^∞ divergence-free on R³ with 0 < T* < ∞, limsup ‖∇u‖_∞ = ∞, and ∫‖curl u‖_∞ = ∞ (consistent with BKM).
  - Mechanism: an infinite iteration of exact odd Euler solutions U_j. At each stage a localized high-frequency WKB packet is added. It is amplified by the parent's rank-one shear along the central trajectory, and at the target time its gradient becomes the parent shear for the next packet.
  - The WKB packet obeys the ODEs F_t = MF, m_t = −Mᵀm, v_t = −Mv + 2m(m·Mv)/|m|².
  - A uniform upper bound on the pressure Hessian (H ≤ K⁺I) keeps a displacement boundary-value problem coercive.
  - Initial-data increments are summable in every H^m, and stability of Euler solutions forces T* ≤ T∞.
  - This is the first unforced smooth, compactly supported blowup on R³ with no boundary. Chen–Hou had a boundary and were computer-assisted; Elgindi and others had only C^{1,α} data.

### Lean formalization (github.com/openai/NavierStokesAndEuler)

- About 2,659 .lean files and about 641k lines. NS is 816 files and 429k lines; Euler is 1,839 files and 212k lines.
- Toolchain: Lean v4.34.0-rc2 with Mathlib at the same tag.
- 0 `sorry`, no custom axioms (only propext, Classical.choice, Quot.sound). A grep found no `axiom`, `native_decide` or `implemented_by`. **So there is no "axiomatized lemma" gap to fill.**
- The NS Comparator challenge is a verbatim copy of the formal-conjectures `Millennium/NavierStokes.lean` statement (FC commit 8bf45ed).
- **The Euler challenge is OpenAI's own adaptation** of that FC file, with ν=0 and f=0, plus a long quantitative statement `exists_compact_smooth_euler_singularity`. It has no independent upstream reference.
- `formalization.yaml` says `review.status: "self-assessed"` and names the model "GPT-6 Astra" (Codex).
- The HEAD commit f9e8bc5 (Sep 10) differs from the commit 8937a8f (Sep 8) that FC's `formal_proof` tag points to. The diff has 173 added and 15 modified files. It adds paper-aligned statements (`NavierStokesR3.theorem_1_1`, `theorem_1_1_with_dissipation`, `PeriodicPaper.periodic_corollary`) that are stated through OpenAI's own `CandidateProperties` definition.
- The local clone at `external/NavierStokesAndEuler` is at f9e8bc5. Its laptop build was at 8943 of 9580 jobs when I checked (`external/ns_build.log`).

## 2. What remains open, and who says so

| Question | Status and source |
|---|---|
| **Unforced NS, Clay (A)/(B)** | Wide open. The OpenAI blog, Silvestre ("the Clay problem is settled, but the main problem for Navier–Stokes is not", *Scientific American*), Tao, Quanta, and Petrillo–Glimm arXiv 2609.23868 all say so. |
| **Can this construction be made unforced?** | Probably not. Stan Palasek (Sept 8, Tao's blog) argues that viscous energy loss beats instability amplification across widely separated frequencies. Tao welcomed this and suggested a simpler model to isolate the interaction **(secondhand)**. Cheskidov–Dai–Palasek, arXiv 2609.26790, study cascade/dyadic analogues. |
| **Regularity of the forcing: real-analytic or vanishing near the singularity** | Constantin–Ignatova–Vicol, arXiv 2609.20803 (Sep 17). Take any construction with (i) anisotropic Type II bounds on the angular mean and (ii) exact axisymmetry on a core B(c√−t), with force bounded in C². Then the force **can neither vanish near the singular point nor be real-analytic in x**. Remark 1.2(e): a C³ bound on the non-axisymmetric part alone would also give regularity, and the OpenAI construction violates it. **Open:** breakdown with a real-analytic, Gevrey or entire force, or with a force vanishing near the singularity, by any other mechanism. |
| **Stability / genericity** | Cao–Chi–Nie, arXiv 2609.10262: blowup-producing forces are dense in L¹ₜH^s exactly when s < 1/2. They say explicitly that this is not typicality and not an open basin. Open: fixed-force instability, classifying singular data at a fixed force, and nonzero data at the critical exponent. |
| **Physical relevance** | Contested. The incompressible model fails before the singularity (Schneider on Tao's blog; Callens repo). Duraiswami, arXiv 2609.17642, finds "nothing … suggests the mechanism is reachable in a flow one computes or builds". Not a mathematical open problem. |
| **Hypodissipative NS** | Córdoba–Martínez-Zoroa–Zheng: forced blowup for small dissipation orders. The threshold (22−8√7)/9 is recovered by Santibañez-Leal (Zenodo 22820521), who also claims smooth forcing caps the exponent at 1/480 in that scheme. Buckmaster says he and Alpöge have an unreleased hypo-/low-dissipation NS result awaiting Lean **(secondhand)**. |
| **Hyperdissipative window 1 < γ < 5/4 (forced)** | *My inference; I did not find it stated anywhere.* γ ≥ 5/4 is globally regular (Lions). Nobody seems to have asked whether the OpenAI mechanism works for γ ∈ (1, 5/4). |
| **Type I vs Type II** | The OpenAI blowup is Type II (τ^{−1/2−h}). CIV Remark 1.4(b) and §1.5 note that axisymmetric Type I is excluded in the unforced setting. Whether *forced* Type I or self-similar blowup exists is, as far as I can tell, not addressed. |
| **Euler: stability, rate, a self-similar profile on R³** | Ganeshram–Duruisseaux–(George)–Anandkumar, arXiv 2609.10867 and 2609.10860, propose a PINN-discovered stable self-similar profile. The proof is "conditional on rigorous certification of the estimates and constants" and says the remaining work is "largely quantitative". Chen–Hou already covered smooth data with a boundary. The OpenAI Euler blowup is an iterative, non-self-similar construction, and its rate and stability are unstudied. |
| **Removing forcing in the shell models** | Palasek, arXiv 2605.13827, Remark 1.4: in his viscous Obukhov model (α ∈ (2, 5/2], the "3D" range) "the inclusion of an external force is necessary", citing **S. Looi, to appear**. It is unproved in print. He also writes: "it is reasonable to conjecture that the regularity mechanisms extend for 'smooth' forcing" (geometric scales). |

## 3. Follow-up papers, preprints and posts (September 2026)

★ marks items that pose explicit open questions or targets.

**Competing and earlier work**
- Buckmaster–Alpöge (+Coiculescu), Sep 7: forced blowup for IPM (arXiv [2609.16470](https://arxiv.org/abs/2609.16470)), 2D Boussinesq, and 3D Euler ([euler.pdf](https://cims.nyu.edu/~tristanb/euler.pdf)). Lean at [tristanbuckmaster/fluid_lean](https://github.com/tristanbuckmaster/fluid_lean). The README says Mathlib must be compiled from source for Lean 4.32.2 ("~100 GB memory"), so a laptop is not realistic.
- Tao blog, Sep 7: [finite time blowup with smooth forcing…](https://terrytao.wordpress.com/2026/09/07/finite-time-blowup-with-smooth-forcing-term-for-the-incompressible-porous-medium-boussinesq-and-incompressible-euler-equations/). ★ In the comments, Palasek raises the obstruction to the unforced case and Tao suggests a toy model.

**Mathematical follow-ups**
- ★ [2609.20803](https://arxiv.org/abs/2609.20803) Constantin–Ignatova–Vicol: regularity under analytic forcing, so OpenAI-type forces can't be analytic or vanish near the singularity. Appendix A deduces the construction's properties from the manuscript and says "we do not claim to have verified" it.
- ★ [2609.10262](https://arxiv.org/abs/2609.10262) Cao–Chi–Nie: forces are dense exactly for s < 1/2. Uses the OpenAI theorem and its Lean as a black box, lists open questions in its §8, and mentions its own Lean4 project.
- [2609.10269](https://arxiv.org/abs/2609.10269) Cao–Chi: whole-space density thresholds. **Withdrawn Sep 11.**
- ★ [2609.26790](https://arxiv.org/abs/2609.26790) Cheskidov–Dai–Palasek: cascade mechanisms. Instantaneous Type I blowup in Obukhov and Desnyansky–Novikov–Obukhov (DNO) dyadic models, compared with the OpenAI result.
- [2609.21312](https://arxiv.org/abs/2609.21312) Z. Zhang: sharp thresholds for the unforced viscous Katz–Pavlović dyadic model. The threshold is α = 1/(b+2) for super-exponential scales. Unrefereed, pure ODE.
- ★ [2609.23868](https://arxiv.org/abs/2609.23868) Petrillo–Glimm: proposes the "positive defect problem" as a target for unforced blowup (a positive defect implies a negative answer to (B)). Includes numerics and some Lean.
- [2609.17642](https://arxiv.org/abs/2609.17642) Duraiswami: an exact 1998 porous-wall swirl solution recast in OpenAI's similarity variables (Chebyshev collocation and continuation). Leaves spectrum convergence open. Numerical and tangential.
- [2609.10867](https://arxiv.org/abs/2609.10867) and ★ [2609.10860](https://arxiv.org/abs/2609.10860) Ganeshram–Duruisseaux–(George)–Anandkumar: a stable self-similar Euler singularity on R³. The target is certifying a finite list of constants.
- [2609.18808](https://arxiv.org/abs/2609.18808) Ruf: claimed global regularity for NS. **Withdrawn Sep 17** because of an error in (27). Crank-adjacent.
- Not about this result: [2609.26050](https://arxiv.org/abs/2609.26050) (OpenAI "whole-cube" coding bound) and [2608.14673](https://arxiv.org/abs/2608.14673) (see §4).

**Blogs and news**
- Tao's blog: guest posts Sep 13 (Guillen) and Sep 23 (Schneider, "headlines and inside stories"). Both are philosophical.
- [Fortnow, Computational Complexity](https://blog.computationalcomplexity.org/2026/09/navier-stokes-and-lean.html): Lean as a "time-stamp", and the risk of mis-stated definitions.
- Quanta, *Scientific American* ("Did OpenAI solve the wrong problem?"), the Wikipedia page "Navier–Stokes priority controversy", and lilting.ch (the dispute timeline).
- whataifound.org lists the NS, Euler and IPM results as "Claimed / self-assessed".

## 4. Independent checks of the Lean formalization

- **[CrystalArchitect/navier-stokes-lean-check](https://github.com/CrystalArchitect/navier-stokes-lean-check)**, credible.
  - The (C) statement is byte-identical to FC upstream 8bf45ed apart from namespaces and imports.
  - The build (11,251 jobs, macOS) exited 0 with no sorryAx and only the three standard axioms. The four `sorry` warnings are all in the challenge stubs.
  - Caveat: (D) adds pressure periodicity, which is from Clay's errata.
  - It did **not** run the nanoda kernel replay (needs Linux) and did not check the prose.
- **Santibañez-Leal, [Zenodo 22820521](https://zenodo.org/records/22820521)**, reasonable but self-published with a retraction history.
  - Rebuilt 11,424 jobs and replayed the kernel from an empty environment (NS 2,972 s, Euler 1,588 s).
  - Recovers the CMZ–Zheng threshold and claims the 1/480 cap.
  - States explicitly that it proves no blowup.
- **[xaviercallens/OpenAI-NSE-Epistemic-Audit](https://github.com/xaviercallens/OpenAI-NSE-Epistemic-Audit)**, **low quality and crank-leaning.**
  - It concedes "the proof is correct".
  - Its "thermodynamic censorship" argument is physics (Mach 0.3 reached about 6.7 ps before the blowup time).
  - It has many version-numbered releases, and its Lean files prove toy predicates.
  - No mathematical content about the proof.
- **[Jexposition/Define-Intelligence](https://github.com/Jexposition/Define-Intelligence)**: two commits and no findings. Ignore it.
- **arXiv 2608.14673 (Sienicki & Sienicki), "A Human Audit of OpenAI's AI-Generated Mathematical Proofs"**: **not about Navier–Stokes.** It audits OpenAI's ten results announced on August 1, 2026. It found no substantive errors in the principal results and one corrected polarity error.
- **Gaps that nobody has closed:**
  - (a) No independent review of the **Euler** challenge statement or of `CandidateProperties` against the paper's Theorem 1.1.
  - (b) No nanoda or Comparator run by a third party that I could find.
  - (c) No one has checked CIV's Appendix A claims (the anisotropic bounds and axisymmetric core) against the formal object.
  - Clay has not verified anything, and the result has no peer review.

## 5. Ranked shortlist for a small Lean/Mathlib team

Honest summary: **nothing on the PDE side is small.** The analytic-forcing, unforced, stability, Type-I and hyperdissipative questions all need serious harmonic analysis or PDE work that Mathlib cannot support. What is realistic: statement-level and formal-infrastructure work, ODE/dyadic-model work, and exact arithmetic checks.

1. **An independent Euler-blowup statement in formal-conjectures, plus a Comparator bridge.**
   - *Question:* does OpenAI's `Euler.euler_breakdown_R3` / `exists_compact_smooth_euler_singularity` say what the paper says? Today it is checked only against OpenAI's own adaptation.
   - *Deliverable:* write `FormalConjectures/…/EulerBlowup.lean` (solved, with a `formal_proof` link) using FC's definitions. Then prove in a scratch project that OpenAI's theorem implies it; this is short definitional glue.
   - Also update FC's NS `formal_proof` commit (8937a8f vs HEAD f9e8bc5), add the open variants from §2 (analytic-force breakdown; unforced hypodissipative), and optionally add the CIV-style "force cannot vanish near the singularity" question as a comment.
   - *Infrastructure:* all already in Mathlib (fderiv, ContDiff, MemLp, lintegral, EuclideanSpace). Our local build (≈ 9.6k jobs, nearly done) supports the bridge. Running Comparator/nanoda on Linux would also be the first published third-party nanoda replay.
   - *Risk:* low novelty, and FC maintainers may already be doing it. "Open" status for new variants must be sourced, which is weak for the Gevrey and hyperdissipative variants.
2. **The Palasek/Looi claim that forcing is necessary in the viscous Obukhov model.**
   - *Question:* for X_k' = −νN_k²X_k + N_{k−1}^α X_{k−1}X_k − N_k^α X_{k+1}² with N_k = N₀^{b^k} and α ∈ (2, 5/2] (or (2,3)), do smooth *unforced* solutions stay regular?
   - This is the shell-model form of the Palasek obstruction that Tao suggested isolating. It is claimed in print only as "Looi, to appear".
   - *Why it's small:* countably many scalar ODEs, energy and trapping-region arguments, no PDE theory. Palasek's own proofs are elementary ODE arguments.
   - *Infrastructure:* ℓ²/`lp` sequences, Galerkin truncation (finite-dimensional Picard–Lindelöf is in Mathlib), Gronwall (`gronwallBound`), and Arzelà–Ascoli (`BoundedContinuousFunction.arzela_ascoli`) for passing to the limit.
   - *Risk:* Looi may publish first. It may be a routine energy estimate, so small novelty. Formalizing infinite ODE systems has real friction.
3. **A Lean formalization of a dyadic-model blowup theorem connected to the follow-ups.** Options:
   - Palasek Thm 1.8: inviscid, unforced Obukhov with super-exponential scales, blowup in every C^s.
   - Zhang's 2609.21312 sharp threshold α = 1/(b+2) for unforced viscous Katz–Pavlović. It is unrefereed, so a formal check has real value.
   - *Why it's small-to-medium:* purely ODE, with proofs of tens of pages. Probably 3–10k Lean lines.
   - *Infrastructure:* the same as item 2, plus real-power and exponent inequalities.
   - *Risk:* medium effort. The results are "models", so they have less headline value than the PDE. Zhang's result may already be well known.
4. **Exact-arithmetic check of the exponent budgets.**
   - Formalize the CMZ–Zheng hypodissipative exponent-budget system and its optimum (22−8√7)/9. Then test Santibañez-Leal's claims: the trade-off α < δ/(4Q), the 1/480 cap under smooth forcing, and a frequency-ratio interval that closes at the threshold.
   - *Why it's small:* finitely many polynomial and real-algebra inequalities (nlinarith, polyrith, `Real.sqrt`).
   - *Risk:* it checks the *bookkeeping*, not the PDE, so it only has value if it finds a discrepancy. The Zenodo source is self-published.
5. **Distilling or bridging the OpenAI development** (medium, higher risk).
   - Option (a): formally derive, from OpenAI's Lean objects, the properties CIV assume in Appendix A: angular-mean bounds up to 2nd order with anisotropic scaling, exact axisymmetry on B(c√(1−t)), and a C² force bound. That would make "the OpenAI force is not real-analytic" formally grounded for the actual object.
   - Option (b): extract Mathlib-quality lemmas from the 641k lines, such as the WKB packet ODE identities (m·v preserved, det F = 1), the positive-cone representation that is stable under perturbation, and closed-interval jet algebra. Upstream them.
   - *Infrastructure:* only what the repo already builds, but you have to navigate AI-generated, undocumented definitions.
   - *Risk:* the needed quantitative bounds may not be exposed in a usable form, and (a) could balloon. (b) has low research value.

**Explicitly not recommended:**
- Certifying the Anandkumar-group Euler profile constants. That is interval-arithmetic numerics at a large scale.
- Anything on analytic or Gevrey forcing, Type I forced blowup, or the unforced problem.
- Rebuilding Buckmaster's fluid_lean (it needs about 100 GB of RAM).
