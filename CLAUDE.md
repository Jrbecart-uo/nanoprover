# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this is

nanoprover: a minimal LLM-guided theorem prover over a real Lean 4 kernel — "the
agent proposes; the kernel disposes." In practice the **session LLM is the
proposer** (the user runs keyless by choice): you write Lean proofs, the kernel
accepts or rejects them. Nothing counts as solved until the kernel says so.

## Read first, every session

1. `BACKLOG.md` — ranked pending work across tracks (Putnam scalps, IMO 1985 P6,
   CDC formalization, discovery, Project Euler) + explicitly DECLINED items.
2. `KNOWN_TRAPS.md` — soundness/tactic/name/env traps. **Append to it after every
   failed kernel round**; that file growing is the project's improvement loop.
3. Longer-lived context (scoreboard, env notes, CDC status) is in auto-memory under
   `~/.claude/projects/-home-jbecart-tmp-mathTest/memory/` (the PARENT dir's project,
   not this one) — it may lag the repo; the repo wins on conflict.

## Environment & commands

```bash
export PATH="$HOME/.elan/bin:$PATH"        # always; Lean toolchain v4.32.0-rc1
source ../.venv/bin/activate               # venv lives in the parent dir (~/tmp/mathTest/.venv)

python3 tools/repl.py start                # boot the Lean REPL daemon (full `import Mathlib`)
python3 tools/repl.py status               # poll until ready; ~6s warm, MINUTES on cold page cache — don't kill early
python3 tools/repl.py check proof.lean     # check a whole file (~0.5s); prints PASS/FAIL + REPL JSON
python3 tools/repl.py check proof.lean --lemmas   # with lemmas.lean (namespace Nanoprover) in scope
python3 tools/repl.py code 'example : 2+2=4 := by norm_num'
python3 tools/repl.py tactic N 'TAC'       # step proofState N (ONE tactic per call; parenthesize `(t1; t2)`)
python3 tools/repl.py stop                 # reclaim RAM; the daemon survives across sessions (double-fork)

python3 tools/premise_index.py query <name>        # verify a lemma name exists BEFORE using it
python3 tools/premise_index.py goal "<statement>"  # ranked relevant mathlib lemmas
grep -x '<name>' data/all_names.txt                # fastest existence check

python3 tools/analogy.py match --text "<goal>"     # nearest solved proof + its transferable "story"
python3 tools/salt.py shake stuck.lean --n 40 --seed 7   # triage candidate `have`s (KEY/BRIDGE/RESTATEMENT/TRUE/POISON)
python3 tools/angles.py stuck.lean                 # ~20 reframings; FILE holds one theorem ending `:= by sorry`

python3 bench/scalp_run.py --bench putnam --name <problem> --scripts cands.json  # preflight names + batch-check candidates

cd cdcproof && lake build                  # CDC lake project, ~60s warm (requires ../mathlib4 cache)

# Checking someone else's claimed Lean proof (pipeline behind verification/NS_AUDIT.md, HODGE_AUDIT.md)
python3 tools/claimcheck.py setup v4.34.0-rc2       # landrun/nanoda + lean4export/comparator for that Lean
python3 tools/claimcheck.py probe                   # sandbox self-test (must print PROBE OK)
python3 tools/claimcheck.py selftest v4.34.0-rc2    # comparator's 20 adversarial cases under the sandbox
python3 tools/claimcheck.py fetch NAME URL [--rev R]  # pristine clone in external/claims/NAME/src
python3 tools/claimcheck.py comparator NAME cfg.json --detach   # fresh clone only; never `build` first
python3 tools/claimcheck.py build NAME TARGET --detach; ... axioms NAME MOD DECL; ... surface NAME MOD ROOT
python3 tools/claimcheck.py status NAME             # waits: grep the CLAIMCHECK_DONE line, never pgrep -f

python tests/test_offline.py               # only test suite (no Lean/network); this is what CI runs
```

Without the daemon, a one-off check is `lake env lean <file>` with cwd=`mathlib4/`
(~6-15s per file).

## Proof-acceptance rules (non-negotiable)

- A proof is accepted only if it checks with **no `sorry`** (a `sorry` is only a
  warning, exit 0 — reject any output mentioning it) and `#print axioms <thm>`
  prints exactly `[propext, Classical.choice, Quot.sound]`. No `native_decide`.
- Probe variants must be anonymous `example`, never named `theorem` (named ones
  enter the env and let `exact?` "prove" a sibling by citing it). The REPL checks
  against the pristine base env by default — keep it that way.
- Name-check every lemma before writing (Mathlib master renames things often;
  hallucinated names are the #1 failure). See the rename list in `KNOWN_TRAPS.md`.

## Environment limits (this WSL box)

- Bash calls hard-cap at 10 minutes (background too) — shard long jobs into
  resumable chunks.
- RAM allows at most 2 concurrent `import Mathlib` processes.
- `ps` may not show processes from other Bash calls; read `/proc/<pid>/status`
  (pid in `.repl/daemon.pid`). `.repl/state.json` can be stale — trust `repl.py status`.

## Architecture (big picture)

- **Kernel boundary** — `core/proof_env.py` (`LeanDojoEnv` interactive states,
  `MockEnv` offline) and `core/lean_cli_env.py` (whole-proof checks via the `lean`
  binary). Proposers in `core/agents.py` (builtin tactics, Claude, portfolio);
  best-first search in `core/search.py`; error-feedback retry loop in
  `core/retry.py`; `core/scalp.py` = name preflight against all mathlib constants +
  batched kernel check. These are the original pipeline; current proving work
  mostly bypasses them in favor of the REPL daemon (`tools/repl.py`, which wraps
  leanprover-community/repl cloned at `repl/`).
- **Benchmarks** — `bench/minif2f.py`, `bench/putnam.py` parse problem statements
  from the gitignored `miniF2F-lean4/` and `PutnamBench/` checkouts. Solved proofs
  are committed as full Lean files with `.txt` extension in
  `bench/solved_putnam/` and `bench/solved_imo/` (one per problem, with a doc
  comment explaining the proof idea).
- **Knowledge that accumulates** — `lemmas.lean` (reusable lemmas, auto-loaded by
  the daemon as a second env), `KNOWN_TRAPS.md` (negative knowledge),
  `tools/analogy.py` STORIES (one per solved proof), `data/` (gitignored mathlib
  dump + 158MB SQLite FTS5 premise index built by `tools/dump_mathlib_db.py` /
  `premise_index.py build`).
- **CDC verification** — `verification/` holds the standalone REPL-checkable
  files + Python computational checks, with the honest summary in
  `verification/STATUS.md`; `cdcproof/` is the lake project tying them into
  cross-importing modules with the capstone `CDCProof.cdc_of_cubicFlow`
  (`Main.lean`) and `cdc_of_covering` (`Flow.lean`). It certifies the paper's
  NOVEL argument only — the 8-flow theorem and Jaeger's cubic reduction are cited,
  not formalized. Always state that boundary; never claim the conjecture is certified.
- **Other areas** — `discovery/` (evolutionary program search on open constructive
  problems; claimed records must be re-verified as a family over growing N —
  finite-N improvements have been mirages), Project Euler solutions (kept OUTSIDE the repo in `~/tmp/euler/`;
  PE asks that solutions past #100 stay private, so never commit PE code or answers),
  `collatz/` (the two-loop discovery demo), `prop_poc/` (original propositional
  PoC), `sherpa.py` (interactive turn-by-turn prover).
- Gitignored large checkouts at repo root: `mathlib4/` (with prebuilt cache),
  `repl/`, `PutnamBench/`, `miniF2F-lean4/`.

## Conventions

- Workflow for a new scalp: write the full `.lean` development → `repl.py check`
  → iterate on kernel errors (step with `tactic` on proofStates from `sorry`) →
  `#print axioms` → save to `bench/solved_*/` → commit as "Scalp N: <problem> (<one-line idea>)".
- Report results honestly, including failures and contamination caveats (the
  README's "What this is NOT" section sets the tone).
- Do not attack Naskręcki's problem — it is a FrontierMath held-out benchmark
  item (declined in `BACKLOG.md`).
