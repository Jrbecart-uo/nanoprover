# Erdős #1110 — density clause for (p,q) = (7,2): attack log (2026-09-28)

**Status: OPEN. No proof.** Status re-checked 2026-09-28: the only density claim is Ding–Li–Liu–Zhang
(2026-08-24, (5,2), positive lower density of representables). Pairs still open for density:
(7,2), (9,2), (4,3), (5,3).

## Empirics (`rep.c`, exact up to 2^27)
Fraction representable: (7,2) ≈ 0.22 and flat from 2^20 to 2^27; (4,3) ≈ 0.15 and still drifting down.

## A clean sufficient criterion (our reconstruction of the (5,2) method)
Chain = set {(α_i, γ_i)} strictly increasing in both coordinates. For every residue r mod 2^s pick a chain
with α < s and Σ 2^α 7^(−γ) ≡ r (mod 2^s); height h(r) = max γ + 1.
**If the average height H̄ < s·log_7 2 (≈ 0.3562 s), the representables for (7,2) have positive lower density.**
Proof sketch: stack blocks (2-exponents in [st, st+s), 7-exponent windows G_{t+1} = max(G_t + h(r_t), ⌈(t+1)λ⌉),
H̄ < λ < s log_7 2, A = ⌈Nλ⌉ + c). The map word → n is injective (n·7^(−A) mod 2^{sN} decodes the word
triangularly), n ≤ K·2^{sN} (geometric decay since G_t ≥ tλ), and admissibility (G_N ≤ A) holds for a
fixed positive fraction of words (Lindley recursion + Chernoff union bound over suffixes).
Variable-length refinement (prefix tree, `tree.c`): needs E[h − μ·ℓ] < 0 over the leaves.

**Validation:** for (5,2), s = 12 gives H̄ = 4.930 < 5.168 with max height 8 — exactly the certificate
shape Ding et al. report (P = 2^12, γ ≤ 7, average height < 5).

## (7,2) numbers
| s (flat) | H̄ | bound 0.3562 s | gap |
|---|---|---|---|
| 12 | 4.920 | 4.274 | 0.645 |
| 20 | 7.737 | 7.124 | 0.613 |
| 24 | 9.107 | 8.549 | 0.558 |
| 28 | 10.466 | 9.974 | 0.492 |
Optimal variable-length tree (ratio E[h]/E[ℓ], need < 0.35621): D=16 0.3879, D=20 0.3804, D=24 0.3735,
D=26 0.3705. Fit ≈ 0.343 + 0.72/D ⇒ crossing near D ≈ 50 (infeasible as full bitsets; the tree's deep
tail is fat: ~4% of mass reaches depth 23, nodes grow ~1.8×/level).
Beam search on 300-bit random targets (`beam.py`) achieves ≈ 0.339 γ/bit < 0.3562: the method should
work in principle; the obstacle is certificate size (boundary losses), not the mathematics.

## Other pairs
- 7-adic orientation for (7,2) is impossible: one term per 7-adic position, and 2^(−β) mod 7 ∈ {1,2,4}
  (2 is not a primitive root mod 7), so half the residues are unreachable.
- (4,3): both orientations hit the known obstruction (3-adic: 4^(−g) ≡ 1 mod 3; 4-adic: 3^(−β) ≡ ±1 mod 4),
  so the scheme must be restricted to the unobstructed classes.
- (9,2), (5,3): heuristic exponents 1.045 / 1.034 — margins thinner than (7,2).

## Next ideas (not tried)
Lookahead/Markov certificates that choose among chains of a block by their carry into the next block
(reduces the boundary loss that dominates the finite-size penalty); certificates as explicit leaf lists
checked by an independent verifier.
