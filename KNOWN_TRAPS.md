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

## Tactic traps

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
