# IMO 2026 — blind attempt (2026-10-02)

IMO 2026 (Shanghai, 15–16 July 2026) is after the model's training cutoff. Statements come from
github.com/junaid-hasan/2026_problems (`p1.lean`…`p6.lean`), checked against the official English PDF.
Only those files and the official problem text were read. The repo's `gpt/` solutions and the
math-ai-org/IMO2026 files were not read; the latter were downloaded by mistake, found to contain full proofs,
and deleted unread. Others had already solved all six in Lean (MechMath, GPT-5.6), so this is a capability
measurement, not a first.

| problem | result | file |
|---|---|---|
| P1 (gcd/lcm board) | **solved**: all 5 statements, clean axioms | `imo_2026_p1.txt` |
| P2 (geometry) | skipped: the statement file weakens "K strictly inside triangle ABL" to "K inside angle LBA" (and similarly for L), so it is not faithful | — |
| P3 (stick division game) | not attempted | — |
| P4 (triangle-cutting game) | **solved** 2026-10-22: answer θ = 180/n; invariant "no angle is a multiple of θ", clean axioms | `imo_2026_p4.txt` |
| P5 (functional inequality) | **solved**, clean axioms | `imo_2026_p5.txt` |
| P6 (gcd-greedy sequence) | **solved** 2026-10-22: conjecture (C) proved by a minimal-counterexample argument (a power of the small radical is forced to be a term), clean axioms | `imo_2026_p6.txt` |

## P6 notes (written 2026-10-02, when P6 was still unsolved; (C) was proved 2026-10-22, see `imo_2026_p6.txt`)

Let A be the set of terms and P(x) the set of primes dividing x.
* Every two terms share a prime (by construction, both ways). Conversely, any x ≥ a₁ whose prime set meets
  P(a) for every a ∈ A is a term, since it would otherwise be skipped by the greedy rule. So
  A = {x ≥ a₁ : P(x) meets P(a) for all a ∈ A}, and pure periodicity a_{n+T} = a_n + L follows once membership
  in A depends only on x mod L.
* Finitely many of the gcd constraints do NOT suffice in general. For a₁ = 18, A = the evens ≥ 18, and the
  terms 2p kill odd candidates one prime at a time. The correct object is the family of minimal prime sets
  among the terms; for a₁ = 18 it is {{2}}, realised late by 32.
* **Conjecture (C), verified for every a₁ < 1200 (terms up to 6·a₁):** any two terms share a prime ≤ a₁.
  (C) implies the result with L = ∏_{p ≤ a₁} p, because membership then depends only on which primes ≤ a₁ divide x.
  In fact the smallest shared prime is ≤ a₁/2 for every composite a₁ < 700.
  Not proved. The natural minimal-counterexample induction (take the first term y that shares only a prime
  q > a₁ with an earlier term) did not close: the window (a_n, y) has length < r = rad(a₁) and contains no
  obvious candidate.
* Scripts: the scratchpad copies `p6exp*.py` were not kept. The construction is short: iterate with the
  minimal-family update.
