# BACKLOG — pending tasks & proposals for future sessions

Durable handoff. A new session can read this + the auto-memory (`nanoprover-project`,
`nanoprover-env`, `nanoprover-roadmap`, `cdc-formalization`, `naskrecki-problem`)
and propose next tasks. Ranked by leverage within each track. Last updated
2026-09-24.

## Session-start ritual
1. `export PATH="$HOME/.elan/bin:$PATH"`
2. `cd ~/tmp/mathTest/nanoprover && python3 tools/repl.py start` (warm ~6s; cold
   page cache = minutes — don't kill it early). Poll `repl.py status` until ready.
3. Read `KNOWN_TRAPS.md` before proving anything.
4. Verify lemma names via `python3 tools/premise_index.py query <name>` BEFORE writing.

---

## Track A — Putnam scalps (theorem-mode; where we are strongest)
Current: **21 scalps**. Reachable wins live here.
- [ ] **Re-examine the scoped-out list** — "too hard" was judged under old 6–8s
      checks; `putnam_1996_a5` and `putnam_2001_a5` both fell once re-examined
      with the REPL. Remaining flagged: `putnam_2007_a5` (McKay counting via
      `Equiv.Perm.card_compl_support_modEq` + `vectorsProdEqOne` rotation —
      plumbing-heavy), `putnam_1974_b3` (Niven-style, needs an algebraic-integer
      argument mathlib may lack — check first).
- [ ] **Mine the ~310 unsolved pure-proof PutnamBench problems** — number-theory
      / congruence ones fall well to full developments. Use `analogy.py match`
      to find the closest solved proof, then the REPL loop.
- [ ] **Exercise `salt.py` / `angles.py` on a real scalp** — built this session
      but only REPL+`premise_index` were used end-to-end (on 2001_a5). Confirm
      the supposition-triage / reframing tools actually help on a stuck goal.

## Track B — IMO 1985 P6 (the honest wall, now more tractable)
- [ ] `∃! a, ∀ n>0, 0 < f n a < f (n+1) a < 1` for the given recurrence. Needs a
      ~100-line real-analysis construction (build `a` as a sup / nested-interval
      limit; monotonicity + continuity in `x`; uniqueness by amplification).
      The REPL's proofState stepping is the tool that makes a long construction
      feasible. Higher risk than a Putnam scalp; a never-solved-tier scalp if it
      lands. File: `miniF2F-lean4/MiniF2F/Test/imo_1985_p6.lean` (statement uses
      `f : ℕ → NNReal → ℝ` — expect cast friction).

## Track C — CDC formalization (DEPRIORITISED 2026-09-24)
NOTE: the full CDC proof (incl. classical parts) has reportedly been formalized in Lean 4
several times since July (OpenAI endpoint for finite loopless bridgeless multigraphs;
Guo, Bajpai, Okur). Finishing our own copy is no longer novel — verify before investing.
The paper's **novel argument is fully certified** (`cdcproof/`: `cdc_of_cubicFlow`,
`cdc_of_covering`, clean axioms, one lake project). What remains is CLASSICAL and
needs multigraph infrastructure Mathlib lacks (its matching/Tutte theory is
`SimpleGraph`-only; no flow/cycle-space/even-subgraph-cover; parallel edges are
essential here — a digon must be a cycle).
- [ ] **The 8-flow core**: *every bridgeless cubic multigraph has three even
      subgraphs covering its edges.* This is exactly what `cdc_of_covering`
      consumes. Large: needs multigraph flow/matching built from scratch.
- [ ] **Jaeger's reduction**: bridgeless ⇒ suffices to treat cubic (vertex
      splitting preserving CDC-liftability).
- [ ] (optional) A clean write-up / artifact of the CDC verification — we
      certified the novel content of a famous-conjecture proof within ~2 days of
      the claim. Distinctive; low effort. Files: `verification/STATUS.md` is the
      honest summary; `verification/cdc*.py` are the computational checks
      (Petersen, flower snarks, 133 random cubic graphs — no flaw found).
- Boundary, always state honestly: this is NOT a certification of the conjecture.

## Track F — Erdős / formal-conjectures (NEW 2026-09-24; see `erdos/TRIAGE.md`)
- LESSON: Tao's AI-contributions wiki froze 2026-06-30; since July the whole Erdős long
  tail is swarmed (GPT-5.6/6 Astra, Claude, Codex users + Justin Sun Prize bounty with
  hundreds of Lean PRs). ALWAYS check `erdosproblems.com/forum/thread/N/proof-claims`
  and FC issues before attacking anything.
- ✅ 2026-09-25: 357/44/184/80/319 reported on FC tracking issue #6448 (comment
      5832484464); 261 already filed as #6538 by an automated LM audit (`ai-audit` label —
      such audits now sweep FC continuously; search before filing). Follow-up: a PR
      re-tagging them needs the Google CLA signed.
- [ ] Only residual genuine target: #1110 density clause — positive lower density of
      representables for (7,2) or (4,3) (finite-certificate search + Lean counting).
- ✅ 261 proof re-checked in the FC environment (clean axioms).

## Track G — Navier–Stokes (OpenAI, Sep 2026) — AUDIT DONE 2026-09-24
- ✅ `verification/NS_AUDIT.md`: statements faithful to Clay (C)/(D); Euler statement
  audited; full build + Comparator in a fresh clone; **nanoda + Lean kernels accept both
  challenges**; clean axioms. Tools built locally in `external/tools/` (landrun
  best-effort: WSL Landlock ABI v3 only).
- [ ] Follow-up candidates (`external/ns_followups_report.md`): independent Euler
      statement for FC; Looi's unforced viscous Obukhov-model regularity (ODE);
      exact-arithmetic checks of exponent thresholds (e.g. (22−8√7)/9).
- Item 4 PICKED 2026-09-25: no Millennium problem is attackable head-on at our scale; instead
  pre-emptive statement audits (`verification/MILLENNIUM_STATEMENTS.md`): RH, P vs NP, BSD
  judged faithful. ✅ 2026-09-25 Hodge statement (Paul-Lez/HodgeConjecture @ 5d0b87f) audited:
  no misformalization (`verification/HODGE_AUDIT.md`). User decision 2026-09-25: NOT reported
  upstream (a negative result, modest value) — focus on our own project.

## Track D — Discovery engine / open problems (LOWER priority — see lesson)
- LESSON (paid for twice): construction-search over WELL-STUDIED open problems
  hits disjointness-threshold walls. Erdős #791 (Rohrbach 2-bases) and #840
  (quasi-Sidon) both confirmed: the obvious construction knob sits at a
  disjointness-threshold optimum; the finite-size δ "improvements" are mirages
  (must test as N→∞). See `discovery/FINDINGS_erdos791.md`, `FINDINGS_erdos840.md`.
- [ ] Only worth it on a GENUINELY idea-bottlenecked, un-attacked target. If
      trying: Erdős #819 (Erdős–Freud sumset, but it has "path to solution in
      comments" — check first) was the other scout candidate. Otherwise defer.
- [ ] Discovery-engine housekeeping if revisited: engine uses the `search(prev,
      deadline, rng)` heuristic contract (not `construct`); ALWAYS verify any
      claimed record as a family across growing N (the independent-verify step).
- [ ] Roadmap item 5 (corpus mutation for `scalp_run`) — never built; low value
      now that theorem-mode is the proven path.
- [ ] Write the 9 missing `analogy.py` STORIES (see `tools/analogy.py` index).

## Track E — Project Euler (renewable, uncontaminated demo)
- [ ] **#1008** (and later) when it drops — proven pipeline, 3/3 site-confirmed
      (#1005 award, #1006 first-15-worldwide, #1007). Solve week-of-publication
      for the clean no-contamination demonstration. Files: `euler/`.

## Explicitly DECLINED
- **Naskręcki's problem** — it is a FrontierMath **Tier-4 held-out benchmark
  item**, not a public open problem. Attacking it would burn a held-out eval the
  field uses to measure frontier ability, and contradicts our own
  no-contamination stance. Do NOT pursue. (See `naskrecki-problem` memory.)

## Housekeeping / decisions pending
- [ ] Repo is public-ready but still PRIVATE — user decision whether/when to
      open it (`https://github.com/Jrbecart-uo/nanoprover`).
- [ ] `tools/repl.py` daemon survives across sessions (double-fork). It may still
      be running; `repl.py status` to check, `repl.py stop` to reclaim RAM.
