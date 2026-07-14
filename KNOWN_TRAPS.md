# KNOWN_TRAPS

Negative knowledge, earned the hard way. **Read this before every proving
session; append after every failed kernel round.** Each entry: the trap, how
it bites, the escape.

## Soundness traps (silent false positives)

- **Named probe variants poison the env.** Probe variants must be anonymous
  `example`, never named `theorem` — a named variant (even sorry'd or failed)
  enters the environment, and `exact?` then "solves" a sibling by citing it
  (fake 8/8 pass). Escape: `example` only; the REPL daemon
  (`tools/repl.py`) always checks against the pristine base env.
- **`sorry` exits 0.** A `sorry` in an accepted proof is only a WARNING
  (exit code 0). Escape: always reject when output mentions sorry; finish
  with `#print axioms <name>` — the only acceptable output is
  `[propext, Classical.choice, Quot.sound]`.

## Reasoning traps (when GENERATING hypotheses — tools/salt.py)

- **The ex falso trap.** A supposition that CONTRADICTS the context closes the
  goal — any goal — by ex falso, so it scores as maximally "useful" while being
  worthless. First run of salt.py on `3 ∣ n ⊢ 9 ∣ n^2` proposed
  `Nat.Coprime (n^2) n` (forces n = 1, contradicting 3 ∣ n) and rated it a top
  bridge. Escape: before believing ANY useful-looking hypothesis, check that
  context + H does not prove `False`. Usefulness without consistency is not
  evidence, it is the absence of evidence.
- **The restatement trap.** `9 ∣ n^2` unfolds to `∃ k, n^2 = 9*k`. Assuming it
  closes the goal instantly — because it IS the goal. Escape: check whether the
  GOAL implies H; if so it is a restatement, not a reduction. Progress means
  strictly stronger, not differently spelled.
- **A supposition you cannot destructure is inert.** `∃ k, n = 3*k` is useless
  to `omega`/`simp_all` until `obtain ⟨k, rfl⟩` opens it. If the closer cannot
  destructure, the real key gets filed as "true but useless" and you throw away
  the answer. Escape: `obtain`/`rcases` branches belong INSIDE the closer.

## Tactic traps

- **`first | t1 | t2` takes the first tactic that SUCCEEDS, not the first that
  CLOSES the goal.** `simp_all` can make progress, leave goals open, and shadow
  the branch that would have finished — the portfolio then reports failure on a
  provable goal. Escape: guard every branch: `first | (t1; done) | (t2; done)`.
- **`exact?` costs ~100x everything else** (it searches all of mathlib). One
  `exact?` per candidate turned a 9 s triage into 2 min; nested inside four
  `obtain` branches, 3m23s. Escape: keep it at the outermost layer, behind a
  flag, never inside a nested `first`.

- **`group` fails on powers of products** like `(A*B*A)^2` — leaves unsolved
  goals. Escape: the reliable free-group normalizer is
  `simp only [pow_succ, pow_zero, one_mul, mul_one, mul_assoc,
  mul_inv_cancel_left, inv_mul_cancel_left, mul_inv_cancel, inv_mul_cancel]`.
- **`omega` treats casts as atoms.** Mixed `Nat`/`Int` goals with `↑` casts
  can stall because omega won't look inside the cast. Escape:
  `zify`/`push_cast` first to normalize to one ring, then omega.
- **`decide` / deep defeq blows the default limits.** Escape:
  `set_option maxRecDepth 4096` and raise `maxHeartbeats` (e.g.
  `set_option maxHeartbeats 1600000`) before trying.
- **REPL tactic mode takes ONE tactic.** `tac1; tac2` is a parse error in
  `repl.py tactic`. Escape: parenthesize `(tac1; tac2)` or step one at a time.

## Name traps (mathlib master, v4.32.0-rc1)

Hallucinated or renamed lemma names are the #1 cause of failed proposals.
Escape: verify EVERY name via `python tools/premise_index.py query <name>`
(or grep `data/all_names.txt`) BEFORE writing the script. Renames seen live:

- `div_lt_div_iff` → `div_lt_div_iff₀`
- `Nat.dvd_sub'` → `Nat.dvd_sub`
- `ord_proj`/`ord_compl` lemmas → camelCase (`Nat.ordProj_mul_ordCompl_eq_self`)

## Environment traps (this WSL box)

- Bash calls hard-cap at 10 minutes; shard long jobs into resumable chunks.
- RAM caps parallelism at 2 concurrent `import Mathlib` processes.
- First REPL boot on a cold page cache is disk-bound (minutes); warm boots
  are ~6s. Don't kill it early.
