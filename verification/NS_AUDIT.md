# Independent check: openai/NavierStokesAndEuler (Sep 2026)

Target: https://github.com/openai/NavierStokesAndEuler @ `f9e8bc5` (2026-09-10),
Lean v4.34.0-rc2, ~641k lines / 2659 files. Claims: Clay Navier–Stokes alternatives
**(C)** (breakdown on ℝ³) and **(D)** (breakdown on ℝ³/ℤ³) for every ν > 0, with smooth
forcing; plus unforced Euler blowup on ℝ³. Checked 2026-09-24 on a WSL2 laptop.

**Scope, stated honestly:** this checks that the Lean statements say what is claimed
and that the kernel accepts the proofs. It is not a referee report on the papers, and it
does not certify the Millennium Prize (Clay requires publication + community acceptance).

## 1. Statement fidelity (the trusted surface)
The trust question reduces to `ComparatorChallenges/NavierStokes.lean` (286 lines) and
`ComparatorChallenges/Euler.lean` (186 lines); the solution must match them exactly.

**NS (C)/(D)** — compared clause by clause with Fefferman's official Clay statement.
Since the theorem is a NON-existence claim, the risks are (i) data conditions weaker than
Clay's, or (ii) a solution notion *stronger* than Clay's (making non-existence cheap).
- Data: u₀ smooth, divergence-free, `‖D^m u₀(x)‖ ≤ C(1+|x|)^{-K}` ∀m,K ≡ Clay (4);
  f smooth on ℝ³×[0,∞) with joint (x,t) derivative decay `C(1+|x|+t)^{-K}` ≡ Clay (5);
  periodic variants ≡ (8),(9).
- Solution: equation (1) with `derivWithin … (Ici 0)` in t, `fderiv` convection, Mathlib
  `Δ`, `gradient` — classical for smooth fields; (2),(3); `ContDiffOn ℝ ∞` (C^∞, not
  analytic `ω`) on ℝ³×[0,∞) ≡ (6)/(11); energy: `MemLp … 2` **and** `∫‖v‖² < E` —
  the `MemLp` clause closes the Bochner-integral junk-value trap (a non-integrable field
  has integral 0, which would make the energy bound vacuous) ≡ (7); periodic pressure per
  Clay errata. No clause asks more of a solution than Clay does.
- Provenance: definitions are identical to google-deepmind/formal-conjectures
  `Millenium/NavierStokes.lean` @ `8bf45ed` (pre-dating the claim) modulo `local
  notation`/`@[simp]`; only theorems (A)/(B) were dropped. Upstream HEAD is unchanged
  except it now tags (C)/(D) `research solved` citing this repo.
- Verdict: **faithful to Clay (C) and (D).**

**Euler** (OpenAI-authored challenge, not previously independently audited):
- `euler_breakdown_R3` = the (C) class with ν = 0, f = 0. Non-vacuous (u₀ = 0 has the
  solution 0), so non-existence is a real claim; pressure unconstrained (only strengthens).
- `exists_compact_smooth_euler_singularity`: compactly supported smooth u₀ ≠ 0, maximal
  lifespan T* ∈ (0,1] characterised by "Sobolev-class solution on [0,T] exists ⟺ T < T*",
  C¹ norm limsup = ⊤ and ∫ ‖ω‖_∞ = ⊤ (BKM) at T*, bounded on shorter intervals.
  `vorticity` is the correct cyclic curl; norms are `ℝ≥0∞` sups so blowup cannot hide in a
  junk value.
- Verdict: **statements are meaningful and match the README's claims.**

## 2. Kernel check (our own build)
`lake exe cache get && lake build` → **Build completed successfully (11424 jobs)**,
1h20m wall, 7.3 GB peak RSS, `LEAN_NUM_THREADS=4`. Only `sorry` warnings are the four
intentional challenge placeholders. `#print axioms`:

| theorem | axioms |
|---|---|
| `NavierStokes.Comparator.navier_stokes_breakdown_R3` | propext, Classical.choice, Quot.sound |
| `NavierStokes.Comparator.navier_stokes_breakdown_periodic` | propext, Classical.choice, Quot.sound |
| `Euler.euler_breakdown_R3` | propext, Classical.choice, Quot.sound |
| `Euler.exists_compact_smooth_euler_singularity` | propext, Classical.choice, Quot.sound |

## 3. Comparator + second kernel (nanoda) — fresh clone
Comparator's guarantee assumes the solution was never compiled outside its sandbox, so
this runs in a separate fresh clone (`external/ns_fresh`, same commit, challenge files
byte-identical: sha256 `2f81f812…` NS, `fc943d55…` Euler).

Toolchain built locally: landrun 0.1.18 (Go 1.27.1), lean4export @ v4.34.0-rc2,
nanoda_lib 0.4.19 (`nanoda_bin`, Rust 1.98.1).

**Sandbox.** The WSL2 kernel (6.6.87) exposes Landlock ABI v3; landrun main demands v9
(Linux 7.1), so landrun runs `--best-effort` (filesystem rules only). Two runs were made:

| escape route (probed from inside) | run 1: README guard (`RestrictAddressFamilies=~AF_UNIX`) + landrun | run 2: layered sandbox |
|---|---|---|
| TCP connect to the internet | **allowed** | blocked (seccomp) |
| AF_UNIX socket | blocked | blocked |
| signal a process outside | **allowed** | blocked (PID namespace) |
| write outside granted dirs | blocked (Landlock v3) | blocked (Landlock v3) |
| ptrace | blocked (yama `ptrace_scope=1`) | blocked (seccomp `@debug` + yama) |

Run 2 layers, all on the stock 6.6 kernel: systemd-run `RestrictAddressFamilies=AF_NETLINK`
(no inet/unix sockets), `NoNewPrivileges=yes`,
`SystemCallFilter=~@debug @module @reboot @swap @raw-io @clock @cpu-emulation`; then
`unshare --user --map-root-user --net --ipc --pid --uts --mount --fork --mount-proc`; then
landrun `--best-effort`. For this purpose it is stronger than Landlock v9 alone (network is
removed, not filtered). Script: `external/ns_comparator_strict.sh`.

**RESULT: both challenges pass under both sandboxes** (`external/ns_comparator.log`,
`external/ns_comparator_strict.log`); run 2 rebuilt the solution from scratch (previous
build moved aside), challenge files byte-identical before and after:

| config | statements match challenge | axioms ⊆ permitted | nanoda kernel | Lean kernel | run 1 | run 2 (strict) |
|---|---|---|---|---|---|---|
| `NavierStokes.json` (C),(D) | ✔ | ✔ | **accepts** | **accepts** | 37m38s | 1h19m46s |
| `Euler.json` (both theorems) | ✔ | ✔ | **accepts** | **accepts** | 1h04m36s | 1h39m43s |

Comparator: "Your solution is okay!", exit 0, in all four runs.

## Bottom line
Under the assumptions above (trusted Mathlib cache and toolchain, the layered sandbox of
run 2, and at least one of the two kernels correct), the four theorems are proved in
Lean exactly as stated. The (C)/(D) statements faithfully encode Clay's breakdown
alternatives. Remaining trust questions are **outside** Lean: whether the formal
definitions capture what the community will accept as "the" problem (we find no gap
against Fefferman's text), priority and credit (Buckmaster–Alpöge dispute), and Clay's
own process. This matches the independent CrystalArchitect check and adds what it did not
do: the nanoda second-kernel replay, plus an audit of the OpenAI-authored Euler statement.
