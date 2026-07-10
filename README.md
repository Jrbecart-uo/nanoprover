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
