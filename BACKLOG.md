# BACKLOG — pending tasks & proposals for future sessions

Durable handoff. A new session can read this + the auto-memory (`nanoprover-project`,
`nanoprover-env`, `nanoprover-roadmap`, `cdc-formalization`, `naskrecki-problem`)
and propose next tasks. Ranked by leverage within each track. Last updated
2026-09-30 (end of session).

## Where the last session (2026-09-29/30) left off — START HERE
- **NEXT (proposed to the user 2026-09-30, ranked; user had not picked yet):**
  1. Project Euler #1012 (publishes Sat 2026-10-03; post-cutoff, solve week-of-publication).
  2. #1110 ASSEMBLY theorems in Lean on top of `E1110G.lean` (cheap, checkable):
     (a) (4,3): representables have positive lower density AND non-representables density >= 1/2
         (n ≢ 2 mod 3, n ≢ 2 mod 4: 1/3 + 1/4 - 1/12); (b) (9,2): representables >> x^0.8967 AND
         non-representables density >= 1/4 (n ≡ 3,6 mod 9 never representable; 9m rep iff m rep);
     (c) bridge `putnam_2005_a1` to `Representable 3 2` = the {2,3} direction of Erdős–Lewin.
  3. Harvest reusable lemmas from today's scalps into `lemmas.lean` (divisor-sum parity via involution in
     ZMod 2, cyclic lemma, bipartite walk parity, quad_nonneg / discrim bounds, rpow-from-integer-power helpers
     `rpow_div_le_of_pow_le` / `lt_rpow_div_of_pow_lt` in E1110G.lean).
  4. Medium Putnam leftovers: 1995_b1 (Finpartition block sizes: |S1|,|S2| <= 3, s ∣ fiber size), 1997_b4
     (generating function 1/((1-y)(1+y^2))). Harder ones listed in `bench/putnam_retriage_notes.md`.
  5. Probabilist note on the exact (e,k) reformulation for (9,2)/(5,3) (user's call on posting).
  6. Expert review of (7,2)/(4,3) — only the user can arrange.
  Not worth it: pushing the (9,2)/(5,3) exponent (~0.005 ratio per extra window digit, D=28 ~90 min).
  Helper used this session: a `save.py` that splices PutnamBench's `open` line + doc comment into
  `bench/solved_putnam/NAME.txt` (keep `open X in` lines in place); rebuild it if needed (it lived in scratch).
- **2026-09-30 (afternoon): RIGOROUS POWER LOWER BOUNDS for the two open pairs** (`erdos/1110/NOTEPOW.md`):
  #{n <= x representable} >> x^{851/949} (0.8967) for (9,2) and >> x^{69/77} (0.8961) for (5,3). New general Lean
  theorem `E1110G.pow_lower_bound` (certificate with drift ABOVE threshold -> x^alpha) + instances
  `erdos1110_92_pow`, `erdos1110_53_pow` in `erdos/1110/lean/E1110G.lean` (clean axioms, `lake env lean` exit 0).
  Certificates exact-checked by `verifyd` + independent Python probe (404/404 states agree). Tables in
  `erdos/1110/data_pow/` (gitignored). Not posted anywhere (user's call); not expert-reviewed. Exponent is near the
  practical ceiling of the method (ratio improves ~0.005 per extra digit of window; D=28 is ~90 min/run).
- **2026-09-30 (evening): +13 Putnam scalps → 113 + 1 vacuous** (+ 1976_b6 quasiperfect, 1999_a6): 2005_a1 (Erdős–Lewin {2,3}), 2025_a1, 2017_a2,
  1973_b1, 1966_b4 (Mirsky), 2007_b5, 2003_a4, 2017_b1, 1970_a2, 1995_a4 (cyclic lemma), 1965_b5 (bipartite); all `verify_scalps.py --kernel` ok. PE: #1012 not out until Oct 3.
- **Project Euler #1008, #1009, #1010, #1011 SOLVED 2026-09-29** (all published Sep 5-26, after the model's
  training cutoff; #1011 within its publication week). Code in `euler/` (`p1008.c` + `p1008_ref.py`, `p1009.py` +
  `p1009_check.py`, `p1010.py`, `p1011.c` + `p1011_check.py` + `p1011_brute.py`); each answer cross-checked by an
  independent implementation and brute force at small sizes. Answers were given to the user in chat (not
  committed: PE asks not to publish); **the user submits them** — record site confirmations when reported.
- **#1110 (9,2)/(5,3): positive density very likely TRUE but unproven** (`erdos/1110/FINDINGS.md`, last two
  sections). Finite-window (online) certificates are dead: they would need ~300 bits of look-ahead in every
  base. KEY NEW RESULT (2026-09-30): an **exact integer reformulation** of the offline problem. Relative to a
  reference line of rate rho < mu, each candidate staircase is an integer pair (e,k) with z = 9^e z_ref + k,
  |k| <= C 9^e; transitions in `exactsp.c`, validated vs big ints (`check_ek.py`, 60k steps, 0 errors). So the
  problem is exactly a branching process on integer pairs in an iid random environment. Exact runs: dies at
  rho = 0.3125 (0.9906 mu), 3/5 targets survive at rho = 0.315 (0.9985 mu) -> margin <= ~1%. The relevant
  population is DEEP (pruning to 3 levels behind the front kills it), so no small certificate either.
  Also: carry-free "window model" is p-universal (~0.307/bit); all p-dependence = carries (real term sizes).
  Next options offered to the user: (1) write the exact reformulation as a short note for a probabilist
  (user's call on posting); (2) rigorous partial result #R(X) >= X^0.88 for (9,2),(5,3) via existing VI
  certificates + a Lean variant for lambda > s*mu; (3) other tracks. Tools: `rolloutg.c`, `viterbi.c`,
  `exactsp.c`, `nbrw.c` (WINSEL env = one-per-window selection), `exactmin.c`, `hmean.c`, `rollout.c`.
- Forum (erdosproblems.com/forum/thread/1110): no comments yet on the (7,2) claim (checked 2026-09-29 afternoon).
- Work is on `main`; REPL daemon stopped. nanoprover repo still PRIVATE. Public results repo:
  https://github.com/Jrbecart-uo/erdos-1110-72 (root = (7,2); `4-3/` = (4,3); release `v43-certificate` = 410 MB table).
- **Erdős #1110 (density of non-representables), our results:**
  - **(7,2) positive lower density** — `erdos/1110/NOTE.md`, Lean reduction `erdos/1110/lean/E1110.lean`.
    POSTED by the user on the erdosproblems.com proof-claims page (2026-09-29). Watch it for comments.
  - **(4,3) positive lower density** — `erdos/1110/NOTE43.md`, GENERAL Lean reduction `erdos/1110/lean/E1110G.lean`
    (`pos_lower_density` for any coprime bases with a viable set; `erdos1110_43_density`; clean axioms). Certificate
    base 4, s=2, D=14: g = 2.5148 < 2·29/23; `verifyd.c` PASS ×2; Python big-int probe 16/16. Public on GitHub, but the
    **forum claim is HELD by the user** (wants expert review first) — do not post without explicit go-ahead.
  - Neither result is human-expert-reviewed yet (the most valuable next step; only the user can arrange it).
- **Open for #1110:** (9,2), (5,3). Exact MC (`repdfs.c`): flat densities ≈0.06 / ≈0.04 up to 2^64 / 2^80 (likely
  positive). The later session showed finite-window certificates cannot reach them (see START HERE above).
  Also suggestive: (5,2) 99.94% representable at 2^48 → "almost all representable" conjecture (no approach yet).
- Tools built 2026-09-29 (all in `erdos/1110/`, see `FINDINGS.md`): `repdfs.c` exact representability test;
  `gvid.c` D-digit/s-block look-ahead value iteration with dead states + viable set (transposed V layout);
  `verifyd.c` exact certificate checker; `verify43_probe.py` independent big-int spot check; `shadow.c`, `gvik.c`,
  `gvis1.c`, `gvi2.c` (exploration). Long jobs: run detached (`nohup setsid bash -c '…' &`) — they outlive the
  10-min Bash cap; poll with an `until … do sleep; done` in a background Bash.
- Other tracks unchanged since 2026-09-28: Putnam 100 scalps (+1 vacuous; all re-verified with
  `verify_scalps.py --kernel`); re-triage in `bench/putnam_retriage_notes.md` (~15 cost-3 left, geometry/ε-δ heavy;
  analysis tiers of `bench/putnam_retriage.tsv` untriaged). IMO 1985 P6 solved. Project Euler: next is #1012 (weekly).
  Tooling tip: sympy finds `linear_combination` multipliers (install with `pip --target` into scratch).
  2026-09-28 cleanup deleted ~58 GB of clones in `external/` (NS evidence kept in `verification/ns/`).

## Session-start ritual
1. `export PATH="$HOME/.elan/bin:$PATH"`
2. `cd ~/tmp/mathTest/nanoprover && python3 tools/repl.py start` (warm ~6s; cold
   page cache = minutes — don't kill it early). Poll `repl.py status` until ready.
3. Read `KNOWN_TRAPS.md` before proving anything.
4. Verify lemma names via `python3 tools/premise_index.py query <name>` BEFORE writing.

---

## Track A — Putnam scalps (theorem-mode; where we are strongest)
Current: **113 scalps + 1 vacuous** (2026-09-30: +13 — 2005_a1, 2025_a1, 2017_a2, 1973_b1, 1966_b4, 2007_b5, 2003_a4, 2017_b1, 1970_a2, 1995_a4, 1965_b5, 1976_b6, 1999_a6; 2026-09-28: +47 real — 22 cost-1–2 then 25 of the cost-3 wave; 1991_a6 vacuous — the whole cost-1–2 tier of `bench/putnam_retriage_notes.md`, plus 2012_a1/1982_a5/1983_b4/2008_b4/1970_b3/1968_b6 from the NEXT list). 2026-09-25: +30. Reachable wins live here.
- ✅ **Scoped-out list cleared** (4/4 fell when re-examined: 1996_a5, 2001_a5, 1974_b3,
      2007_a5). 1974_b3 needed no algebraic integers (denominators 3^(2^k) grow under
      angle doubling); 2007_a5 passed first try via `card_fixedPoints_modEq` on the
      `vectorsProdEqOne` rotation. LESSON: our "too hard" labels were wrong 4 times out of 4.
- [~] **Mine the unsolved pure-proof PutnamBench problems** (2026-09-25 sweep: 160 with no
      analysis keywords triaged by 3 agents → 16 solved in a row, most first-try:
      1971_b1 1972_a2 1978_a4 2012_a2 2000_a2 1995_a1 1997_a4 1968_a2 1967_b2 1965_a4
      1992_a1 1987_a1 1966_a1 1962_a6 1965_b3 1978_a1 2007_b1 1963_a2).
      Then (same day): 1995_a3 1965_b2 1964_b2 1971_a1 1992_b2 2002_a5 1986_b3 2018_b2
      1964_a4 1972_b4 1962_b1 2009_b1.
      NEXT from the ranked lists: 2012_a1 (sort d, Fibonacci growth), 1983_b4, 1982_a5,
      2000_b5, 2008_b4, 2017_a2, 2003_b4, 2005_a1, 2004_b1, 2025_a1, 1978_b4, 1978_b6,
      1973_b2, 1965_a6, 1968_b6, 1970_b3; plus the 143 unsolved problems never triaged
      (the ones with analysis keywords — re-triage with a finer filter).
      Findings: 2017_b3 is FALSE as formalized (`Irrational (f 1/2)` parses as (f 1)/2);
      1991_a6 is VACUOUS (`→` binds looser than `∧` in `hA`) — if proved, label as such.
      ALWAYS finish with `python3 tools/verify_scalps.py --kernel NAME`.
- [ ] **Exercise `salt.py` / `angles.py` on a real scalp** — built this session
      but only REPL+`premise_index` were used end-to-end (on 2001_a5). Confirm
      the supposition-triage / reframing tools actually help on a stuck goal.

## Track B — IMO 1985 P6 — ✅ SOLVED 2026-09-28
- `bench/solved_imo/imo_1985_p6.txt` (~190 lines, 3 kernel rounds): existence via a = sSup of
  the "too small" set + continuity (no inverse functions / IVT needed), uniqueness via the
  amplification Dₙ₊₁ ≥ (3/2)Dₙ. Checked by the REPL and independently by `lake env lean`
  spliced into miniF2F's own file; axioms clean. Standard textbook proof (contamination caveat).

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
      such audits now sweep FC continuously; search before filing).
      ✅ 2026-09-30: maintainer mo271 opened PRs for all five (357 → #6744, 44 → #6750,
      184 → #6745, 80 → #6751, 319 → #6747), each marking the variant `research solved` with
      the literature reference we gave. No CLA/PR needed from us anymore; just watch them merge.
- [~] #1110 density: (7,2) ✅ posted; (4,3) ✅ verified + public on GitHub, forum claim held; (9,2), (5,3) open —
      out of reach of finite certificates (quenched-rate analysis 2026-09-29, `erdos/1110/FINDINGS.md`).
      Earlier (5,2): Ding–Li–Liu–Zhang claim.
- ✅ 261 proof re-checked in the FC environment (clean axioms).

## Track G — Navier–Stokes (OpenAI, Sep 2026) — AUDIT DONE 2026-09-24
- ✅ `verification/NS_AUDIT.md`: statements faithful to Clay (C)/(D); Euler statement
  audited; full build + Comparator in a fresh clone; **nanoda + Lean kernels accept both
  challenges**; clean axioms. Tools built locally in `external/tools/` (landrun
  best-effort: WSL Landlock ABI v3 only).
- [ ] Follow-up candidates (`verification/ns/followups_report.md`): independent Euler
      statement for FC; Looi's unforced viscous Obukhov-model regularity (ODE);
      exact-arithmetic checks of exponent thresholds (e.g. (22−8√7)/9).
- Item 4 PICKED 2026-09-25: no Millennium problem is attackable head-on at our scale; instead
  pre-emptive statement audits (`verification/MILLENNIUM_STATEMENTS.md`): RH, P vs NP, BSD
  judged faithful. ✅ 2026-09-25 Hodge statement (Paul-Lez/HodgeConjecture @ 5d0b87f) audited:
  no misformalization (`verification/HODGE_AUDIT.md`). User decision 2026-09-25: NOT reported
  upstream (a negative result, modest value) — focus on our own project.

## Track H — Claim-check readiness (DONE 2026-09-25)
- ✅ `tools/claimcheck.py`: setup / probe / selftest / fetch / build / axioms / surface /
  comparator / status. Validated: sandbox probe blocks all escape routes; comparator's 20
  adversarial self-tests agree under the sandbox (attacks rejected for the right reason);
  `surface` reproduces the Hodge audit's 499-constant list exactly; lock refuses concurrent
  builds. Not yet re-run end-to-end on a Mathlib-scale comparator claim (NS takes ~3 h).

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
- [x] **#1008-#1011** solved 2026-09-29 (answers with the user for submission; site confirmation pending).
- [ ] **#1012** (and later) when it drops — proven pipeline, 3/3 site-confirmed before this batch
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
