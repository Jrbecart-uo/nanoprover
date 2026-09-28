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
- **Parallel subagents + `lake build` in the same project collide** (two builds write the
  same `.lake/build`). When delegating review of a Lean repo, tell agents NOT to build
  (build once yourself; they may `lake env lean` small files in a scratch dir), and use
  `tools/claimcheck.py`, whose build/comparator steps take a per-claim lock.
- **`pgrep -f PATTERN` inside a wait loop matches the loop's own command line**
  (the pattern is in it), so "wait until X exits" never ends. Escape: wait on a
  sentinel line in X's log, or `pgrep -f '[n]s_script.sh'` (bracket trick).
- Landlock here is ABI v3 (WSL kernel 6.6): current landrun needs `--best-effort`.
  For real isolation layer systemd-run seccomp (`RestrictAddressFamilies=AF_NETLINK`,
  `SystemCallFilter=~@debug …`) + `unshare --user --map-root-user --net --pid --ipc
  --mount --fork --mount-proc` (see `verification/NS_AUDIT.md`).

## Elaboration / tactic traps (added 2026-07-15, from CDC glue + putnam_2001_a5)

- **`decide` over `ZMod n` / products (e.g. `𝔽₂³`) needs raised limits.** A `∀`
  over a finite ZMod-product with `if`/`≠` (like `cdc_local`, `local_02`) fails
  instance synthesis by default. Escape:
  `set_option synthInstance.maxSize 1000 in` + `set_option maxRecDepth 40000 in`.
- **`fin_cases` over `Nat.divisors N` needs `set_option maxRecDepth 100000`.**
  Factoring N during `fin_cases` blows the default depth. (Divisor enumeration:
  `a ∣ N`, `a>0` → `lift a to ℕ`, `a ∈ Nat.divisors N`, `fin_cases <;> omega`.)
- **`ring`/`linear_combination` does NOT reduce the characteristic in `ZMod n`.**
  A goal that is true only because `n = 0` in `ZMod n` (e.g. `9 = 0` in ZMod 9)
  will fail with "ring expressions not equal". Escape: avoid needing it —
  `sub_eq_iff_eq_add` then `decide` on the concrete residue, or manual rewriting.
- **Rewriting a `Prop` inside `if _ then _ else _` fails ("motive is not type
  correct")** — the `Decidable` instance depends on the Prop. Escape: prove the
  if-VALUE equality with `if_congr (h : c ↔ c') rfl rfl`, then `rw` that.
- **Structure fields cannot use grouped binders** `fst snd : E → V` — Lean reads
  `snd` as autoImplicit. Each field on its own line: `fst : E → V` / `snd : E → V`.
- **`gauge` is a Mathlib identifier** (Minkowski gauge, returns ℝ). Don't reuse
  it as a local def name — you get baffling `ℝ`-typed errors. (Used `cdcGauge`.)
- **char-2 module algebra without `•`:** `linear_combination` chokes on scalar
  `•`. Case on `ε : ZMod 2` first (`by decide : ∀ z:ZMod 2, z=0∨z=1`), turning
  `ε • x` into `0` or `x`, then use `CF.neg_self` / `CF.add_self_zero`.
- **`open Nat` (PutnamBench headers) hijacks `pow_succ`/`pow_succ'`** to the `Nat.`
  versions, so a monoid rewrite fails with "function expected". Escape: write
  `_root_.pow_succ'`, and ALWAYS re-check a finished proof under the benchmark file's
  own `open …` line before counting the scalp (2007_a5 passed without it, failed with it).
- Name renames seen: `Finset.card_insert_of_not_mem` → `card_insert_of_notMem`;
  `Finset.filter_sdiff` does not exist (prove by `ext; tauto`).

## Added 2026-09-28 (putnam_2008_b4, 2000_b5)
- **`ring`/`abel` can fail on linear identities whose atoms are `x % q ^ 2` (ℤ)** — e.g.
  `y - x = y % q^2 - x - (y % q^2 - y)` after `convert … using 1` ("made no progress").
  Escape: don't do arithmetic on `%` terms; chain `Int.ModEq` instead
  (`Int.modEq_iff_dvd.mpr`, `.symm`, `.trans`, then `Int.modEq_iff_dvd.mp`).
- **`Xor'` is deprecated (use `Xor`), and `decide (Xor' P Q)` needs a Decidable instance
  that `classical` does not supply inside `decide_eq_decide`.** Escape: case-split
  `by_cases h1 : P <;> by_cases h2 : Q <;> simp_all [Xor']`.
- `push_neg` is deprecated → `push Not` (works the same).
- **`rec` is not a usable `have` name** (`have rec : … := …` → "unexpected token ':='" far
  from the cause, and the theorem is reported as having unsolved goals). Use `hrec`.
- **Parity case splits: `split_ifs <;> omega` over 7 `Odd (r*a + s*b + t*c)` conditions
  (128 branches) hits the heartbeat limit.** Escape: cast to `ZMod 2`
  (`← ZMod.intCast_eq_one_iff_odd`, `push_cast`), state the finite fact for all
  `A B C : ZMod 2`, and close it with `decide` (instant).
- **`linarith` failed on `hm : 1 < m`, `hmn : m = 1 ⊢ False`** (ℝ; context also held rpow
  hypotheses like `u ^ 0 + v ^ 0 = 1` and a `∀` lemma) — cause not isolated. Escape for such
  one-step contradictions: `exact (ne_of_gt hm) hmn` (or `absurd`), don't debug linarith.
- **`decide` refuses goals once a local instance like `haveI : Fact (Nat.Prime 101)` is in
  context** ("Expected type must not contain free variables").  Escape: prove all `decide`
  facts (e.g. `(2 : ZMod 101) ^ 50 ≠ 1`) BEFORE the `haveI`; add the `Fact` only where field
  lemmas (`mul_eq_zero`) need it.  Powers in ZMod p need `by set_option maxRecDepth 20000 in
  decide` — put the option INSIDE the tactic block: a top-level `set_option … in theorem` is
  dropped when `verify_scalps --kernel` splices the proof into PutnamBench's file.
