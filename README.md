# nanoprover

**A minimal LLM-guided theorem prover with a real Lean 4 kernel.
The agent proposes; the kernel disposes.**

nanoprover is to AlphaProof what nanoGPT is to GPT: a small, readable,
runnable implementation of the architecture behind LLM-guided formal theorem
proving. ~1,500 lines of commented Python, no GPU, no API key required, runs
on a laptop in minutes.

```
        intuition (untrusted)                 truth (trusted)
  ┌─────────────────────────────┐      ┌──────────────────────────┐
  │  agent: LLM / heuristics /  │      │  Lean 4 kernel           │
  │  you at a terminal          │─────▶│  accepts or rejects      │
  │  "try tactic X"             │      │  every single step       │
  └─────────────────────────────┘      └──────────────────────────┘
              ▲                                     │
              └───────── new goal state ◀───────────┘
```

The one property everything rests on: **a hallucinated proposal can waste a
step, but it can never introduce a false theorem.** The only door into the
database is the kernel.

## Quickstart

```bash
./setup.sh          # installs elan (Lean toolchain manager), venv, clones the demo repo
source .venv/bin/activate
export PATH="$HOME/.elan/bin:$PATH"
```

### 1. Prove a theorem yourself, turn by turn (`sherpa`)

You are the intuition engine; Lean checks every move:

```bash
python sherpa.py                    # theorem: a + b + c = a + c + b
```

```
Current goal:
  a b c : Nat
  ⊢ a + b + c = a + c + b
tactic> rw [add_assoc]
[accepted]
Current goal:
  ⊢ a + (b + c) = a + c + b
tactic> rw [add_comm b]
...
*** NO GOALS REMAIN -- theorem proved! ***
```

Bad tactics are rejected with the kernel's error; `:undo`, `:reset`, `:proof`
navigate. Prove your own goals with `--sig "(p q : Prop) : p ∧ q → q ∧ p"`.

### 1b. Real mathematics: mathlib mode

Fetch mathlib's prebuilt binaries once (`./setup.sh --mathlib`, ~7GB, no build,
no tracing) and sherpa can check goals over the real numbers with the full
mathlib tactic arsenal:

```bash
python sherpa.py --theorem binom_sq     # (a b : ℝ) : (a+b)^2 = a^2 + 2ab + b^2
python sherpa.py --theorem sq_nonneg    # try: positivity
python sherpa.py --mathlib --sig "(p : ℕ) : p.Prime → 2 ≤ p" \
    --preamble "import Mathlib.Data.Nat.Prime.Basic"
```

Each check takes ~2-3s (mathlib import overhead per probe).

Mathlib **is** the theorem database — ~319,000 proved theorems. Query it live
with the `exact?` tactic (library search), or dump it for your own tooling:

```bash
python tools/dump_mathlib_db.py                          # all ~319k names, ~10s
python tools/dump_mathlib_db.py --prefix Nat.Prime --types   # names + statements
```

### 2. Automated search against the real kernel

Best-first backward search where a portfolio of proposers (built-in tactics,
optionally Claude) compete on each goal:

```bash
python core/real_run.py             # proves two theorems with zero LLM calls
python core/run.py --mock           # offline demo of the search loop, no Lean needed
```

### 3. The Collatz campaign — a two-loop discovery system

The showcase. We formalized the Collatz conjecture and built the full
inner/outer loop around it:

- **Inner loop**: grow a database of kernel-verified numbers using closure
  lemmas (`collatz/collatz_discover.py`).
- **Stall**: backward search saturates at **82% coverage of 1..100 even with
  10,000 theorems** — n=27 is unreachable (its orbit climbs through 9232).
- **Outer loop** (`collatz/outer_loop.py`): an LLM proposes *new lemmas* —
  new gear, not more search. The kernel filters them:

  | proposed lemma | verdict |
  |---|---|
  | `reaches1_of_step` (parity-free 1-step closure) | ✅ proved |
  | `reaches1_iter` (orbit-jump) | ✅ proved |
  | `reaches1_mul_pow2` | ✅ proved (2nd attempt) |
  | `reaches1_add_two` — *would prove the whole conjecture* | ❌ **rejected** |
  | `reaches1_triple` | ❌ rejected |

- **Payoff**: with the surviving gear, the same 999-theorem budget goes from
  **22% to 100% coverage of 1..1000**, every proof one line, all
  kernel-checked in ~30s (`collatz/collatz_discover2.py`).

```bash
cd collatz
python outer_loop.py                          # watch the kernel filter the gear
python collatz_discover2.py --upto 1000       # regenerate the database
cd ../lean4-example && lean /tmp/collatz_db2.lean   # kernel-check all 999 theorems
```

The lesson, in one sentence: *one new concept beat 25× more compute* — and the
kernel made it safe to let an LLM propose that concept.

### 4. Baseline: what do builtins actually solve? (`bench/`)

12 mathlib-style goals, best-first search, one-shot tactics (`bench/bench_mathlib.py`):

- **builtins alone: 11/12** — `ring`/`simp`/`omega`/`positivity` take the computational
  goals, and mathlib's `exact?` (library search over all 319k theorems) takes
  every single-lemma goal.
- **+ premise retrieval (LibraryAgent): 11/12** — no lift on this suite, honestly
  reported: `exact?` already covers one-lemma retrieval. The index's real role is
  feeding *statements* to an LLM proposer (premise selection), not replacing `exact?`.
- **the residual** (`(|a|-|b|)² ≤ (a-b)² ∨ |a-b| ≤ |a|+|b|`) needs two steps
  (`right`, then the lemma) — structurally out of reach for one-shot tactics, and
  solved in sherpa by an LLM/human in exactly two moves. That gap is the
  portfolio slot an LLM proposer fills.

### 4b. Tier 2: where the LLM slot is measured, then filled

8 goals chosen to need multi-step reasoning (`--tier 2`): case splits,
induction, existential witnesses, hypothesis manipulation.

| config | solve rate |
|---|---|
| A: builtins (incl. `exact?`) | **0/8** |
| B: + premise retrieval | **0/8** |
| C: + multi-step proposals (LLM channel) | **8/8** |

Config C is the proposal channel (`ProposalFileAgent` + `bench/proposals_tier2.json`):
an external proposer — Claude via API, a session LLM, or you — submits complete
tactic scripts, and the kernel filters each as a whole proof. The winning scripts
include a full induction (`cube_dvd`: divisibility of n³+3n²+2n) and a case-split
proof of `max a b = (a+b+|a-b|)/2`. Every proposal was written by an LLM reading
the goal + retrieved premises; the kernel accepted 8/8 first-choice candidates.

`ClaudeAgent` speaks the same protocol automatically: goal + top-10 premises from
the index → multi-step script candidates (needs `ANTHROPIC_API_KEY`).

### 4c. External benchmark: miniF2F (goals we did not write)

To rule out self-play bias, `bench/minif2f.py` imports the **full miniF2F test
split — all 244 competition problems** (AIME/AMC/IMO/MATH) — and re-checks them
against our mathlib, probes batched so one `import Mathlib` amortizes over a
whole chunk (~20s per 4-goal chunk; full split in ~4 background waves):

- **builtins: 62/244 (25%)** — dead-center in the published tactic-only
  baseline range. First-tactic wins: `norm_num` 23, `linarith` 17, `omega` 14,
  `nlinarith` 4, `exact?` 4. All 244 statements elaborate (usable).
- **+ LLM proposals on 5 attempted residuals: 5 solved**, including Bernoulli
  via `one_add_mul_le_pow`, a quadratic-factoring Finset argument, and
  `mathd_numbertheory_353` — which resisted three *blind* proposal rounds and
  fell in one round of the **error-feedback retry loop** (below).

### 5. The retry loop: error feedback closes the gap

`core/retry.py` + `bench/retry_run.py`: proposals loop through
propose → kernel error → revised proposal. The 353 case study: blind attempts
died on a hallucinated lemma name; the retry loop surfaced the kernel's
`Unknown constant 'Nat.Ico_succ_right'`, the premise index supplied real names,
and the corrected double-Gauss proof was accepted next round. Proposers:
`ClaudeRetryProposer` (API, premises + failure history in prompt),
`InteractiveProposer` (human/terminal), `ScriptedProposer` (replay).
- Found-and-fixed during this run: a **self-reference leak** where `exact?`
  cited a sibling `sorry`'d variant of the same statement (probes now use
  anonymous `example`, which never enters the environment). Benchmarks lie
  in subtle ways; the first (wrong) run scored 8/8.

### 6. Two IMO problems from the never-solved tier

We aimed the retry loop (session LLM as proposer) at the three miniF2F IMO
problems most cited as unsolved-by-machines:

| problem | result | proof shape |
|---|---|---|
| **imo_1981_p6** (Ackermann: `f 4 1981 = g 1983 − 3`) | ✅ **solved, 2 rounds** | four stacked inductions deriving closed forms `f 1..f 4`, linked to the tower `g` (~50 lines) |
| **imo_1977_p6** (`f(f(n)) < f(n+1) ⟹ f(n) = n`) | ✅ **solved, 1 round** | invariant `n+1 ≤ m → n+1 ≤ f m` by induction, monotonicity bootstrap, squeeze |
| **imo_1985_p6** (unique `a` with `fₙ(a)` increasing in `(0,1)`) | ❌ honest fail | needs a nested-interval/completeness construction (~100+ lines) — the wall is real |
| **imo_1983_p6** (triangle inequality `a²b(a−b)+b²c(b−c)+c²a(c−a) ≥ 0`) | ✅ **solved, 1 round** | `nlinarith` with a hand-picked certificate hint set (triangle-positivity products × difference squares) |
| **imo_1964_p2** (Schur-type: `a²(b+c−a)+… ≤ 3abc` for triangle sides) | ✅ **solved, 1 round** | same certificate strategy, first hint set |

Proof scripts: `bench/solved_imo/`. Caveats stated plainly: the proposer knew
the classical proof ideas (these are famous problems — contamination applies
to any LLM), and "solved with an informed multi-step plan" is exactly the
claim being demonstrated, not one-shot magic.

The 1985 attempt also caught a **soundness hole in our harness**: a proposal
containing `sorry` was accepted, because `declaration uses 'sorry'` is only a
warning (exit 0). `LeanCLIEnv` now rejects any proof whose output mentions
sorry. The kernel was never fooled — our wrapper was. Second benchmark lesson
kept in the open.

### 7. PutnamBench + a live competition problem

**PutnamBench** (`bench/putnam.py`): the harder successor to miniF2F — 672
Putnam problems; we run the 326-problem pure-proof subset (answer-construction
problems excluded: their official answers sit in reference comments).
Result: **builtins 0/315 (0.0%)** — Putnam has no one-tactic proofs; every
solve must come through the proposal channel. First scalp:
`putnam_2000_b2` (`n ∣ gcd(m,n)·C(n,m)`) via Bézout + `Nat.succ_mul_choose_eq`
(both located with the premise index), 2 feedback rounds
(`bench/solved_putnam/`).

**Project Euler #1005** (`euler/`), published days before this run: median
increasing-prime list summing to 2026. Counting DP + lexicographic unranking
over 59,284,153,745,615 lists (enumeration impossible); reproduces the
problem's worked example and matches brute force on N=5..80. The found list's
certificate — 24 elements all prime, strictly increasing, sum 2026, product
ending [withheld] — is **kernel-verified** (`euler/p1005_verify.lean`).
Median-ness rests on the cross-validated DP; stated honestly.

### The premise database

Mathlib **is** the theorem database — we export and index it locally:

```bash
python tools/dump_mathlib_db.py --types --shard 0 --num-shards 6 --out data/thms_types_0.tsv
# ... (6 shards, ~15 min total)                    → 319,184 name+statement rows
python tools/premise_index.py build "data/thms_types_*.tsv"   # → 158MB SQLite FTS5
python tools/premise_index.py goal "|a + b| ≤ |a| + |b|"      # ranked lemmas, ~ms
```

## What's in the box

| path | what it is |
|---|---|
| `sherpa.py` | interactive turn-by-turn prover (you are the agent) |
| `core/proof_env.py` | the kernel boundary: `LeanDojoEnv` (interactive states) + `MockEnv` |
| `core/lean_cli_env.py` | lightweight real kernel via the `lean` binary — no tracing needed |
| `core/agents.py` | proposers: built-in tactics, Claude (Anthropic SDK), portfolio merger |
| `core/search.py` | best-first backward search over proof states |
| `collatz/` | the full Collatz campaign: formalization, closure lemmas, both generations of the discovery loop, and the kernel-checked theorem databases |
| `prop_poc/` | chapter zero: the original 150-line propositional PoC (forward chaining, `A→B` + `B→C` ⇒ `A→C`) |
| `tools/` | mathlib database export (sharded) + SQLite FTS5 premise index |
| `bench/` | the builtins-vs-retrieval baseline (results in `bench/results.json`) |

## What this is NOT

Honesty section, because this field is prone to overclaiming:

- **It will not resolve open conjectures.** Everything the loop can derive is
  a *consequence of existing knowledge*. Collatz/Goldbach-class problems need
  new mathematical machinery, not better search. (Our own experiment shows
  this sharply: the only proposed lemma strong enough to imply the conjecture
  was precisely the one the kernel rejected as unprovable.)
- **It is not competitive with research systems** (AlphaProof,
  DeepSeek-Prover, ReProver). It is the readable version of their shared
  architecture, for learning and experimentation.
- **The `LeanCLIEnv` backend is whole-proof checking**, not incremental proof
  states — multi-subgoal branching is where you'd graduate to the LeanDojo
  backend (included, but requires tracing the target repo once). Note that
  plain *mathlib imports* do NOT need the trace — `setup.sh --mathlib` uses
  mathlib's prebuilt cache and works with the CLI backend.

## Where it could go

- Point the automated search loop at **mathlib** goals (mathlib mode already
  works in sherpa) and at open lemma nodes in `lean-blueprint` formalization
  projects — small, real, creditable targets.
- Make the outer loop iterate: stall → propose gear → filter → re-run,
  autonomously.
- Counterexample hunting: a loop that *disproves* conjectures only needs one
  witness — that's a search problem, and search is what this does.

## License

MIT
