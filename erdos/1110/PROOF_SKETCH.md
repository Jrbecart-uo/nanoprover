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
Filtration F_t := σ(y mod 2^{s(t+2)}). By induction C_0…C_{t−1}, G_0…G_t and X_t = (c_t, b1_t) are
F_t-measurable (C_j depends only on z_j mod 2^{3s}, i.e. on y mod 2^{s(j+3)}). Given F_t, the look-ahead
u_t = ⌊z_t/2^{2s}⌋ mod 2^s = (F_t-known) + 7^{G_t}·(block t+2 of y) mod 2^s is uniform (bijective image of a
fresh block; padding only changes the odd multiplier). The policy reads z_t mod 2^{3s} = (c_t, b1_t, u_t)
and, on an unpadded step, X_{t+1} = (zn mod 2^s, ⌊zn/2^s⌋) with zn = 7^{h}((z − v(C)) mod 2^{3s})/2^s mod 2^{2s}.
**Certificate inequality:** an integer table V̂ (= V·2^20 rounded) and ĝ with, for every state x,
  avg_u min_{C∈𝒞(c)} [ h(C) + V̂(next(x,u,C))/2^20 ] ≤ V̂(x)/2^20 + ĝ,   ĝ < λ := s·26/73 < sμ (7^26 < 2^73).
π := the minimiser w.r.t. V̂ over the (pruned) lists 𝒞(c) (ties arbitrary), used for t ≤ N−3; the last two
blocks use any chain (min height), adding ≤ 2H to the excess.
Let τ = last t ≤ N−2 with E_t = 0. For each fixed τ₀ define the auxiliary process that agrees with the
real one up to time τ₀ and then runs *unpadded* with policy π. On {τ = τ₀} the two coincide on
[τ₀, N−2] (a padded step after τ would force a later zero of E). For the auxiliary process
Y_t := h_t − ĝ + V̂(X_{t+1})/2^20 − V̂(X_t)/2^20 satisfies E[Y_t | F_t] ≤ 0 and |Y_t| ≤ B := H + ĝ + osc(V̂)/2^20.
Since Σ_{t=τ₀}^{N−3} Δ_t = L_{N−2} − L_{τ₀} ≥ (N−2−τ₀)λ − 1,
E_N ≤ Σ_{t=τ₀}^{N−3} Y_t + osc + 1 − mδ + 2H,  m = N−2−τ₀, δ := λ − ĝ > 0.
Azuma: P(Σ Y_t ≥ mδ + c′) ≤ exp(−δc′/B²)·exp(−mδ²/(2B²)), c′ := c − osc − 1 − 2H. Union over the
deterministic τ₀: P(E_N > c) ≤ e^{−δc′/B²}/(1 − e^{−δ²/(2B²)}) ≤ 1/2 for c large (independent of N).

## 5. Conclusion
At least 2^{sN}/2 − 1 distinct representables lie in [1, K·2^{sN}] (y = 0 gives n = 0), for every N. For x ≥ K·2^s choose N with
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

**Independent review (2026-09-28, adversarial referee agent):** no fatal issue; two fixable gaps
(last two blocks; coupling exposition) — both patched above. The referee re-implemented the check
(`review_indep.py`: itertools chains, big-int 2-adic transitions with random high bits) and matched
`verify.c`'s GNUM exactly at s = 5, 6 (incl. random asymmetric tables); exhaustively tested s = 3, N = 4
(`review_fresh_s3.py`): u_t exactly uniform in all 37 440 conditioning classes, transitions match on
854 744 unpadded steps, all 4096 constructed n distinct antichain representations with n ≡ 7^A y.
At s = 11 the rerun reproduces GNUM = 8385274094 (argmax state (c,b1) = (1835, 623)), and the
independent checker (`indep_probe.py`) reproduces the per-state values exactly on the argmax state and
12 random states (`indep_s11.txt` vs `verify_s11_run2.txt`). `check_rational.py`: 7^26 < 2^73.
Referee confidence (pre-patch): ~85–90%.

Caveats: computer-assisted (C programs, not Lean); the density constant implied by Azuma is
astronomically small (positive, but useless numerically); independent review pending.
