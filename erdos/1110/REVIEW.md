# Erdős #1110 — reviewer's packet

*For an expert asked to check our density results. Everything here can be re-run on one machine
(8 cores, 16 GB). Draft 2026-10-02. Re-run the clean-room check: `cd erdos/1110/indep_rs && cargo build --release`, then see `RESULTS.md`.*

## 1. What is claimed

For coprime p, q ≥ 2, call n *representable* if n = Σ pᵃⁱ qᵇⁱ with no summand dividing another
(Erdős #1110; definition `Erdos1110.Representable` copied verbatim from formal-conjectures).

| pair | claim | status |
|---|---|---|
| (7,2) | representables have positive lower density | posted on erdosproblems.com (2026-09-29), `NOTE.md` |
| (4,3) | representables have positive lower density | public on GitHub, forum claim held for review, `NOTE43.md` |
| (9,2), (5,3) | #{n ≤ x representable} ≫ x^0.8967, x^0.8961 | not posted, `NOTEPOW.md` |
| (4,3), (9,2), (7,2) | upper density ≤ 1/3, 3/4, 1/2 (elementary, almost certainly known) | Lean, unconditional |

Each lower bound has two parts: **(A)** a theorem saying a finite *certificate* implies the bound.
This part is fully formalized in Lean 4/Mathlib. **(B)** A specific certificate, a table of 2²²–2²⁸ numbers,
checked by computer programs and *not* in Lean.

## 2. Part A: the Lean reduction

| file | main theorem | its only hypothesis |
|---|---|---|
| `lean/E1110.lean` | `E1110.erdos1110_72_density` | `∃ K : Cert 11 10, K.g = 8385274094 / 2^31` |
| `lean/E1110G.lean` | `E1110G.erdos1110_72_density` (same table, general formulation) | `∃ K : Cert 2 7 11 22 10, K.W.Nonempty ∧ K.g = 8385274094 / (2^11 · 2^20)` |
| `lean/E1110G.lean` | `E1110G.erdos1110_43_density` | `∃ K : Cert 4 3 2 14 18, K.W.Nonempty ∧ K.g = 42192162 / (16 · 2^20)` |
| `lean/E1110G.lean` | `E1110G.erdos1110_92_pow`, `erdos1110_53_pow` | analogous (`Cert 2 9 1 26 12`, `Cert 3 5 1 17 12`) |

Check: `cd mathlib4 && lake env lean ../erdos/1110/lean/E1110G.lean` (~50 s with a built Mathlib).
It exits 0, and every `#print axioms` line reads `[propext, Classical.choice, Quot.sound]`. There is no `sorry`
and no `native_decide`. The conclusions are stated with `Representable` and `Finset.range`/`filter`/`card`,
so a reviewer only needs to read the **statements** of these theorems and the definition of `Cert`. The
proofs are kernel-checked.

**What to read in Lean:** `Gamma`, `Representable` (lines 35–40, verbatim from formal-conjectures), the
structure `Cert` (`E1110G.lean`, section "Certificates"), and the final theorem statements.

## 3. Part B: the certificate, and why the checkers check `Cert`

A `Cert b r s D H` (digits in base b, other base r, blocks of s digits, states of D digits, heights ≤ H)
consists of a viable set `W`, a policy giving a chain `ch z` and height `hgt z` for each (D+s)-digit window
`z`, a real potential `V` and a drift `g`. The fields correspond to the checker as follows:

| Lean field | what it says | how the certificate provides it |
|---|---|---|
| `chain`, `inj`, `alpha_lt`, `gamma_lt`, `hgt_le` | the policy's chains are chains: α ↑, γ ↑, α < s, γ < hgt ≤ H | chains enumerated as equal-size subsets α ⊆ [0,s), γ ⊆ [0,H), paired in order; hgt = max γ + 1 |
| `res` | `b^s ∣ z − v(ch z)` when the low D digits of z are in W | the chain is chosen from the residue class of x = z mod b^D |
| `closed` | the next state `r^h (z − v)/b^s mod b^D` is in W | the policy takes the arg-min only over chains whose next state is in W; W is a fixed point, so one exists |
| `rclosed` | x ∈ W ⇒ r·x ∈ W (padding steps) | second fixed-point condition |
| `drift` | Σ_u [hgt + V(next)] ≤ b^s (V(x) + g) for x ∈ W | V := round(2²⁰·table)/2²⁰ and g := GNUM/(b^s·2²⁰), where GNUM = max_x of the integer left-minus-right side |

Any table that passes is a valid certificate. The table is just a witness, so how it was found (value
iteration) does not matter, and neither does the storage layout or the float rounding, as long as the checker
evaluates one fixed function V consistently. Soundness rests only on the checker computing chains, inverses
and transitions correctly, which is why we check them several independent ways:

| pair | checkers (full, all states) | partial checks |
|---|---|---|
| (7,2) | `verify.c`, `verify2.c` (written independently; same max at the same state) | Python big-int, 13 states at s = 11; full at s = 5, 6 |
| (4,3) | `verifyd.c` | Python big-int `verify43_probe.py`, 16 states |
| (9,2), (5,3) | `verifyd.c` | Python big-int, 404 states each |
| all four | **clean-room Rust checker** `indep_rs/` (written from `indep_rs/SPEC.md` alone, without seeing the other code or the expected numbers) | reproduces every GNUM exactly (below) |

**Clean-room results (2026-10-02, `indep_rs/RESULTS.md`).** An agent with no access to our C/Python code
or to the expected values implemented `SPEC.md` in Rust. It self-tested transitions against direct big-integer
computation, with random high digits, enumerated chains two independent ways, and compared the whole pipeline
with a naive big-integer version on 100 small cases. It then ran the real tables:

| pair | |W| | bad | GNUM (Rust) | GNUM (C) | g < λ | runtime |
|---|---|---|---|---|---|---|
| (4,3) | 178 956 970 | 0 | 42192162 | 42192162 (`verifyd`) | yes (λ = 58/23) | 128 s |
| (9,2) | 2²⁶ (all) | 0 | 736074 | 736074 (`verifyd`) | yes (λ = 13/37) | 7 s |
| (5,3) | 3¹⁷ (all) | 0 | 2390897 | 2390897 (`verifyd`) | yes (λ = 35/46) | 16 s |
| (7,2) | 2²² (all) | 0 | 8385274094 | 8385274094 (`verify.c`, `verify2.c`) | yes (λ = 286/73) | 161 s |

The argmax states agree too: 80755765 for (4,3), and state (c,b) = (1835,623) for (7,2). The (7,2) table was
checked in the general formulation (b = 2, r = 7, s = 11, D = 22: the conditions of `E1110G.Cert`), as well as the
two-block one of `E1110.Cert` used by `verify.c`/`verify2.c`. `E1110G.erdos1110_72_density` takes exactly this general
certificate as its hypothesis, so all four pairs now rest on the same Lean structure `E1110G.Cert`. The
(4,3) viable set has the same size as `verifyd`'s (2/3 of all states).

Tables and hashes: `V_s11_it8.bin.xz` (7,2); `data_43/V43_final.bin.xz` (4,3; also GitHub release
`v43-certificate`; uncompressed SHA-256 `cc32e163…f1f080`); `data_pow/V92_d26.bin.xz`, `data_pow/V53_d17.bin.xz`. SHA-256 sums sit next to each file.

## 4. Where an error could hide (what we would check first)

1. **Faithfulness of the conclusion**: "positive lower density" is stated as
   `∃ c > 0, ∃ x₀, ∀ x ≥ x₀, c·x ≤ #{n ≤ x : Representable p q n}`.
2. **The `Cert` ↔ checker correspondence** (table above). In particular, the next state in Lean is
   `((r^h * ((z − v).val / b^s) : ℕ) : ZMod (b^D))`, where `v` is the chain value in `ZMod (b^(D+s))` with
   `r⁻¹` taken in that ring. All checkers use exactly this formula.
3. **Arithmetic in the checkers**: r⁻¹ mod b^(D+s), overflow (the checkers use 128-bit intermediates), and the
   rounding of V (harmless, see above).
4. **The threshold inequalities** (`r^λ < b^s`, `g < λ`) are proved in Lean (`three_rpow_lt`, etc.); the
   checkers also test them in exact integers.

## 5. Not done

* The certificates are not checked inside Lean: 2²²–2²⁸ states × 2¹¹–16 look-aheads is far beyond kernel
  evaluation, and the project forbids `native_decide`.
* No human expert has reviewed any of this yet.
* The implied density constants are astronomically small (around 10^(−10⁶)): the results are qualitative.
