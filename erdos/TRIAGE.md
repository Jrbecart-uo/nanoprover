# Erdős shortlist — triage (2026-09-24)

Pipeline: `external/erdosproblems/data/problems.yaml` (1221 problems, 590 `open`)
∩ formal-conjectures Lean file with a `research open` theorem (335)
− problems in Tao's AI-contributions wiki (data frozen 2026-06-30)
− prize problems  → **243 candidates** (`candidates_raw.json`), read by 4 triage
passes over the Lean statements (`triage_batch{0..3}.txt`). ~226/243 judged hopeless
for a laptop-scale team (deep analytic NT, famous conjectures, independence).

## Literature check (2026-09-24) — the long tail is being swarmed
Tao's wiki froze on 2026-06-30; since July, AI-assisted users (GPT-5.6/6 Astra, Claude,
Codex) plus the Justin Sun Prize bounty (github.com/TheJustinSunPrize/awards, hundreds of
Lean PRs since mid-Sep) have hit exactly this tail. Proof claims live at
`erdosproblems.com/forum/thread/N/proof-claims`. Verdicts (details: `litcheck_{A,B,C}.md`):
- 1063 `better_upper`: already Lean-proved (2^{3k/4}, 2026-09-17); our relaxation is far weaker than White's bound. DROP.
- 700(ii): solved (Price, GPT-5.6, accepted; needs Maynard). DROP.
- 273, 203: many negative AI/SAT searches since Jul 2026; lcm ≥ 393120 claimed. SKIP.
- 348: solved (Geneson arXiv:2609.25107) + Lean (ljhfafa). DROP.
- 289: solved + ~9k-line Lean (Land, 2026-09-04). DROP.
- 774: genuinely hard (Sidon ⇔ finite union of dissociated?). DROP.
- 1110: infinitude clause Lean-proved for all pairs (Sep 2026). **Density clause open**: show positive
  lower density of representables for (7,2) or (4,3) (heuristic exponents 1.13 / 1.12 > 1;
  empirical 23.9% / 17.4% ≤ 2·10⁵). Only residual target from this pass.
- 197: open, SAT-searched (arXiv:2609.02939); low priority.

## Original triage list (pre-literature-check)
| # | FC theorem | score | angle |
|---|---|---|---|
| 1063 | `erdos_1063.better_upper` | 7 | answer fn may be n_k itself ⇒ only need n_k = o(k·lcm(1..k-1)); relax one prime in (k/2,k) of Cambie's construction |
| 273 | `erdos_273` | 5 | finite search: covering system with moduli p−1 (p≥5 prime); if found, Lean `decide` mod L |
| 700 | `erdos_700.parts.ii` | 5 | ∞ many composite n with min_k gcd(n,C(n,k))² > n; ~140 examples < 3000 (pqr); need a Lucas-digit family |
| 1110 | `erdos_1110` | 5 | residue obstructions give non-representable classes for many (p,q); risk: answer may be "no" |
| 348 | `erdos_348` | 5 | ∀-reading makes achievable (m,n) monotone; need (m,m+1) for all m; (1,2) found, search (2,3) |
| 774 | `erdos_774` | 4 | fractional vs integer chromatic gap realised by additive relations at separated scales |
| 197/203 | `erdos_197`, `erdos_203` | 4 | SAT/covering searches (203 ties to 273) |
| 289 | `erdos_289` | 4 | pure construction: interval-reciprocal gadget |
| 655 | `variants.general_position` | 4 | formaliser-added variant, lightly studied; ℝ² geometry cost |
| 786 | `parts.ii` (Finset reading) | 4 | elementary density question |

## Tagged open but apparently KNOWN / TRIVIAL (formal-conjectures hygiene)
| # | theorem | finding | status |
|---|---|---|---|
| 261 | `variants.two_representations` | true via 4/2⁴ = 5/2⁵+6/2⁶ (3/8 two ways) | **KERNEL-PROVED** `erdos/erdos_261_two_reps.lean` (clean axioms); already noted on forum 2026-04-27; "two" likely a misprint for 2^ℵ₀ |
| 357 | `variants.hegyvari` | known: Hegyvári, Acta Math. Hungar. 48 (1986) | CONFIRMED-KNOWN |
| 44 | `variants.empty_start` | Singer 1938 + p_{n+1}/p_n→1 | CONFIRMED-KNOWN (answer True) |
| 184 | `variants.covering` | Pyber, Combinatorica 5 (1985) 67–79 | CONFIRMED-KNOWN (answer True) |
| 80 | `erdos_80` | Fox–Loh, Combinatorica 32 (2012), arXiv:1106.0290 | CONFIRMED-KNOWN (answer False; `variants.log` still open) |
| 319 | `variants.isTheta` | c(N) ≤ N trivial + solved `variants.lb` | CONFIRMED-KNOWN (answer `fun N ↦ N`) |

## Possible misformalizations (statement ≠ intent)
- 885: 0 ∈ D(n) for squares — minor, does not trivialize (checked).
- 887 `rosenfeld_4`: C existentially quantified inside the set — much stronger than intended.
- 1056: interval {1} allowed ⇒ k=2 trivial via Wilson; main ∀k statement still open (docstring fix).
- 1055: NOT a bug — two competing open conjectures, normal FC practice.
- 1175 (`aleph_one`), 1068: negative answer consistent (Shelah) ⇒ likely independent of ZFC.
- 786: Finset forbids repeated factors (docstring acknowledges).
- 332, 319, 361, 409, 450, 452, 538, 552, 272, 33, 195, 168: `answer(sorry)` fillable by the defining expression — ill-posed as "find the value".
- 357 `monotone.*`: distinct-sums forces StrictMono ⇒ duplicates `parts.i/ii`.

**Reported 2026-09-25**: 357/44/184/80/319 posted as a comment on tracking issue #6448
(https://github.com/google-deepmind/formal-conjectures/issues/6448#issuecomment-5832484464).
261 NOT posted: duplicate of #6538 (opened 2026-09-24 15:41 UTC by an automated LM audit,
label `ai-audit`, with a compiled trivial proof). Our proof was re-checked in the FC
environment (Lean v4.33.1, FC definitions, `answer(True)`): clean axioms.
