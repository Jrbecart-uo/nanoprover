# Positive lower density of representables for (p,q) = (7,2) — proof sketch (DRAFT, conditional)

Status (2026-09-28): **certificate found and independently verified by computer**; argument not yet
reviewed by anyone else — treat as a claim-in-progress, not a result. Method = the finite-certificate
approach of Ding–Li–Liu–Zhang for (5,2) (reconstructed from their abstract), strengthened with a
two-block look-ahead policy and a potential-function (supermartingale) analysis.

Notation. n is *representable* if n = Σ 7^{a_i} 2^{b_i} over an antichain for divisibility, i.e. the
pairs can be ordered with a strictly increasing and b strictly decreasing (equivalently b increasing
and a decreasing). μ := log_7 2. A *chain* is a finite set {(α_j, γ_j)} ⊂ ℕ² strictly increasing in both
coordinates; its value is v(C) = Σ 2^{α_j} 7^{−γ_j} ∈ ℤ₂ and its height h(C) = max γ_j + 1 (h(∅) = 0).

## 1. Blocks
Fix s, H, and for each residue c mod 2^s a finite list 𝒞(c) of chains with all α < s, γ < H and
v(C) ≡ c (mod 2^s) (every residue is covered). A *block placement* of C at bit offset st and 7-offset
G contributes the terms 2^{st+α} 7^{A−G−γ}, (α,γ) ∈ C. Consecutive blocks with G_{t+1} ≥ G_t + h(C_t) form
an antichain overall (block t+1 has larger b and smaller a than every term of block t).

## 2. Encoding
Let A be fixed and y ∈ ℤ/2^{sN}. Put z_0 = y (normalised residual). At block t, with state
X_t = (c_t, b1_t) = (z_t mod 2^s, ⌊z_t/2^s⌋ mod 2^s) and look-ahead u_t = ⌊z_t/2^{2s}⌋ mod 2^s, choose
C_t ∈ 𝒞(c_t) (policy π below), set G_{t+1} = max(G_t + h(C_t), L_{t+1}) with L_t = ⌈tλ⌉, and
z_{t+1} = 7^{G_{t+1}−G_t} (z_t − v(C_t)) / 2^s. Then n := Σ_t Σ_{(α,γ)∈C_t} 2^{st+α} 7^{A−G_t−γ} satisfies
n ≡ 7^A y (mod 2^{sN}) (last two blocks: any chain, no look-ahead). Hence y ↦ n is injective.

## 3. Size
G_t ≥ L_t ≥ tλ, and within a block the terms have distinct α, so
n ≤ Σ_t 2^{s(t+1)} 7^{A−tλ}. With A = L_N + c and λ < sμ (so 2^s 7^{−λ} > 1) this is ≤ K·2^{sN},
K = 2^s 7^{c+1} / (1 − 7^λ 2^{−s}). Representability needs all exponents A−G_t−γ ≥ 0, i.e. G_N ≤ A,
i.e. excess E_N := G_N − L_N ≤ c.

## 4. Probability (y uniform)
Given the past, u_t is uniform on ℤ/2^s (it is a bijective image of y's block t+2). Transitions of
X_t without padding: next = (zn mod 2^s, ⌊zn/2^s⌋) with zn = 7^{h}((z − v(C)) mod 2^{3s})/2^s mod 2^{2s}.
**Certificate inequality:** a table V on (ℤ/2^s)² and ĝ with, for every state x,
  avg_u min_{C∈𝒞(c)} [ h(C) + V(next(x,u,C)) ] ≤ V(x) + ĝ,   and ĝ < λ := s·26/73 < sμ.
π := the minimiser (ties arbitrary). Then Y_t := h_t − ĝ + V(X_{t+1}) − V(X_t) has E[Y_t | F_t] ≤ 0 and
|Y_t| ≤ B := H + ĝ + osc(V) on unpadded steps.
Let τ = last t ≤ N with E_t = 0. Steps after τ are unpadded, so
E_N ≤ Σ_{t=τ}^{N−1} (h_t − λ) + 1 ≤ Σ Y_t + osc(V) + 1 − (N−τ)δ, δ := λ − ĝ > 0.
For each fixed τ₀, the unpadded process from X_{τ₀} (policy π, fresh uniform u's) is a supermartingale
setting; Azuma gives P(Σ_{t=τ₀}^{N−1} Y_t ≥ mδ + c′) ≤ exp(−δc′/B²)·exp(−mδ²/(2B²)), m = N−τ₀,
c′ = c − osc(V) − 1. Union over τ₀: P(E_N > c) ≤ e^{−δc′/B²}/(1 − e^{−δ²/(2B²)}) ≤ 1/2 for c large.

## 5. Conclusion
At least 2^{sN}/2 distinct representables lie in [1, K·2^{sN}], for every N. For x ≥ K·2^s choose N with
K2^{sN} ≤ x < K2^{s(N+1)}: #{n ≤ x representable} ≥ 2^{sN}/2 ≥ x/(2K2^s). Positive lower density.

## Certificate
Found by value iteration (`look4.c`), checked by an independent program (`verify.c`: regenerates the
chains, computes transitions by direct 2-adic arithmetic, exact int64 arithmetic on V scaled by 2^20,
compares ĝ with s·26/73 where 7^26 ≤ 2^73 is checked exactly).

**Result (s = 11, H = 10, per-residue chains with height ≤ min + 3, 70 701 chains):**
`verify 11 10 3 V_s11_it8.bin 26 73` → GNUM = 8385274094, ĝ = GNUM/(2^11·2^20) = 3.904698 per block
(0.354973 per bit) < 11·26/73 = 3.917808. **PASS.** δ = λ − ĝ ≈ 0.0131 per block.
V table: `V_s11_it8.bin.xz` (float32, 2^22 entries; sha256 of the uncompressed file
f7f832116362b96db8ba42884e61803aa5e7cd02071a45f3353072ee4bdd9258), produced by `look4 11 10 14 3`
(iteration 8; value-iteration bracket per bit [0.35423, 0.35523]).

**End-to-end simulation** (`e2e.py`): the certified policy with line padding, run on random targets
(40 × 150 blocks, 6 × 300, 6 × 900), builds n explicitly: every construction is an antichain, satisfies
n ≡ 7^A y (mod 2^{sN}), and the excess E stays bounded (final ≤ 34, typically < 10) — consistent with
negative drift. `simcheck.py` validates the transition formula against direct 2-adic arithmetic
(14 812 cases, 0 mismatches).

Caveats: computer-assisted (C programs, not Lean); the density constant implied by Azuma is
astronomically small (positive, but useless numerically); independent review pending.
