# Literature / status check B — Erdős #1110, #348, #774, #289 (+ #197, #655, #786)

Checked 2026-09-24. Sources: erdosproblems.com problem pages, forum threads, and `/forum/thread/N/proof-claims`
(this is where the AI-assisted claims live; the plain forum thread does NOT show them), arXiv, GitHub,
TheJustinSunPrize/awards (a bounty catalogue, "JSP-xxxxxx" ids that do NOT equal Erdős numbers; e.g. JSP-000921 = #1110,
JSP-000290 = #348). The local formal-conjectures clone is at commit 40a8592 (2026-09-24).

**Bottom line:** since August 2026 this area has been heavily worked by AI-assisted groups. #289 and #348 are effectively
solved, with Lean proofs that have no `sorry`. The pairwise-coprime clause of #1110, which is all the formal statement
covers, has been proved in Lean with no conditions. #774 is a well-known hard open problem in harmonic analysis. Only the
**density clause of #1110** still looks like room for a small laptop-plus-Lean contribution.

---

## #1110 (Erdős–Lewin, d-complete {p^k q^l})

**Site statement (OPEN, "cannot be resolved with a finite computation"; last edited 01 Apr 2026).**
Let p>q≥2 be coprime. n is representable if it is a sum of numbers of the form p^k q^l, none dividing another.
If {p,q}≠{2,3}, what can be said about the density of non-representable numbers? Are there infinitely many coprime
non-representable numbers?

Known (from the site): Erdős–Lewin [ErLe96]: finitely many non-representables ⇔ {p,q}={2,3}. Yu–Chen [YuCh22, JNT 238 (2022)]:
the representable numbers have density 0 if q>3, or if q=3 and p>6, or if q=2 and p>10. There are infinitely many
(pairwise-)coprime non-representables if q>3, or if q=3 and p≠5, or if q=2 and p∉{3,5,9}. The side question f(n) (every summand > f(n)):
Yang–Zhao [YaZh25, Acta Arith. 217] f ≫ n/log n. van Doorn notes Blecksmith–McCallum–Selfridge (1998) already gives
f(n) ~ (log2·log3/2)·n/log n.

**Forum comments (4):**
- StijnC, 07 Dec 2025: typo, should read "finitely many … iff". Fixed.
- Adenwalla, 07 Dec 2025: pointed to Yang–Zhao (Acta Arith 2025), f ≫ n/log n. Yu–Chen cover every pair except {2,3},{2,5},{2,9},{3,5}. Site updated.
- Adenwalla, 08 Dec 2025: Yu–Chen show density 0 for the *representable* numbers, not the non-representable ones. Fixed.
- Woett (van Doorn), 10 Mar 2026: BMS98 Theorem 2 gives f(n) = (log2 log3/2 + o(1)) n/log n. Site updated.

**Proof claims (2):**
- **Apiros3, 2026-08-05, partial, GPT-5.6 Sol + GPT-5.5, Lean-formalised** (github.com/Apiros3/erdos1110). Covers the 3 pairs
  Yu–Chen miss: (5,2) seed c=3, (9,2) c=5, (5,3) c=2. Construction: N = p^a + c·q^M with p^a < q^M, c·q^M < (p−1)p^a,
  a,M synchronized (log p/log q irrational). A "low-row synchronization" lemma forces the low part of any antichain to be {(a,0)}.
  Dividing by q^M then gives a representation of c, which is impossible. The proof is readable at
  `docs/exceptional_cases_proof.md`.
- **Ding, Li, Liu, Zhang, 2026-08-24, partial, GPT-5.6 Sol** (ResearchGate "On a problem on d-complete sequences"):
  for (p,q)=(5,2) the **representable integers have positive lower density**. Method: a finite certificate of sets C(r),
  0≤r<P=2^12, with Σ 2^α 5^{-γ} ≡ r (mod P) and staircase exponents α≤11, γ≤7, average height H<5. An injective map
  sends admissible words to 𝓡, and the cycle lemma with double counting gives 𝓡(10546·P^N) ≫ P^N.

**Beyond the site:** TheJustinSunPrize/awards issue #637 (x2515102083, 2026-09-17), with the repo
github.com/x2515102083/erdos1110 (`Erdos1110/AllPairs.lean`, endpoint `Erdos1110.erdos1110_pairwise`). It claims an
**all-pairs, unconditional** Lean proof of the pairwise-coprime clause, with no Yu–Chen hypothesis and only the standard
axioms. The submitter says explicitly that the density clause is open, and that the problem should not be marked solved on
this evidence alone. arXiv 2503.11676 ("Note on a theorem of Birch and Erdős", 2025) is related background.

**My checks (this session):**
- Apiros3's generic lemma applies whenever some seed c has 2≤c≤p−2, gcd(c,pq)=1, and c is not a power of q. For coprime
  pairs with p<400, the only failures are **(4,3) and (6,5)**. Both fall to a trivial residue obstruction: an antichain has
  at most one term with j=0, so n mod q ∈ {0} ∪ ⟨p⟩. For (4,3), every n≡2 (mod 3) is non-representable. For (6,5), every
  n≡2,3,4 (mod 5) is. So the formal clause is "easy" once Apiros3's lemma is in hand, consistent with the all-pairs Lean claim.
- The triage hint was right about residue obstructions for (7,2),(4,3),(7,3),(5,4), but those pairs were already covered
  by Yu–Chen. The "risk" pair (5,2) has answer **yes** (seed 3).
- Growth exponent heuristic. The number of antichains below x is about x^e, with e = (1/ln p+1/ln q)·H(t) in nats and
  t = (1/ln p)/(1/ln p+1/ln q). The exponent is e<1 **exactly** in the Yu–Chen density-zero range. The five remaining
  density pairs all have e>1: (5,2) 1.263, (7,2) 1.127, (4,3) 1.120, (9,2) 1.045, (5,3) 1.034. So we expect *positive*
  density of representables there. For (4,3), the density is at most 2/3 because of the mod-3 obstruction.
- Numerics (DP over staircases, n ≤ 2·10^5). Fraction of n that are representable: (5,2) 73.5%, (7,2) 23.9%,
  (4,3) 17.4%, (5,3) 9.9%, (6,5) 1.1%. Script: scratchpad `rep1110.py`.

**Formal statement** (`1110.lean`). It formalizes **only the second question**, as "∀ coprime p>q≥2, (p,q)≠(3,2),
∃ infinite pairwise-coprime set of non-representables". `Gamma p q = {p^k q^l}` and the divisibility antichain match the
site. Reading "coprime" as "pairwise coprime" matches Yu–Chen and Apiros3. **Not a misformalization, but incomplete:**
the density question is absent. The answer to the formal statement should be `True` (if x2515102083's proof holds).

**Verdict:** the infinitude part is done, and done in Lean. The density part is open for (7,2),(9,2),(4,3),(5,3). For (5,2)
there is a claim of positive lower density of representables. Small contribution: port the Ding–Li–Liu–Zhang
finite-certificate method to (7,2) or (4,3), where the margin is largest (e≈1.12). That means a computer search for a
certificate C(r) mod some P with small average height. Then add a Lean statement, perhaps `erdos_1110.variants.density_*`,
to formal-conjectures. The Lean proof of the counting and cycle-lemma step is non-trivial but finite-flavoured.

---

## #348 (deletion thresholds for complete sequences)

**Site statement (OPEN):** for which 0≤m<n is there a complete sequence A = {a1≤a2≤…} that stays complete after removing
any m elements but is not complete after removing any n elements? Fibonacci gives (1,2). Powers of 2 give (0,1).
"The case m=2 and n=3 is not known." van Doorn proved that no example with 2≤m<n exists under *strong* completeness
(every n, not just all large n).

**Forum:**
- Woett, 06 Sep 2025: the strong-completeness version is settled (none for 2≤m<n). The argument fails for weak
  completeness because a_n = F_n + (−1)^n is a counterexample to the method (see #346). He had the Lean statement
  changed to weak completeness on 25 Sep 2025.
- Sprite144, 16 Jul 2026: computational study of the (2,3) case. Found a multiset (Fibonacci values with multiplicities 3,2,2,1,2,1,…)
  that is 2-robust while infinitely many triples break it, and a certificate for "healing". Conjectures that no example
  exists for m≥2.

**Proof claim (1):** **Jesse Geneson, 2026-09-09, full proof** (found by Codex with "GPT-6 Astra Ultra", audited with GPT-6
and Claude Opus 5). **Only m=0,1 work.** If every 2-deletion preserves completeness, then some k-deletion of every size does too.
- Claim comment, Woett, 10 Sep 2026: the claim gives an infinite B⊂A with A∖B₀ complete for every finite B₀⊂B. He
  formalized a weaker but sufficient version for **sets** (github.com/Woett/Lean-files/ErdosProblem348.lean, 1260 lines,
  `main`).
- Paper: **arXiv:2609.25107**, Geneson, "Deletion thresholds and exponential examples for complete sequences"
  (20 Sep 2026). It also refutes a Graham conjecture about ⌊tγ^n⌋.
- **Full Lean for nondecreasing sequences (multisets):** github.com/ljhfafa/jsp-000290-lean, by Codex.
  `Jsp290.admissible_iff (m n) (hmn : m<n) : Admissible m n ↔ m ≤ 1`, standard axioms only.
  JSP PR #4447 was opened **today (2026-09-24)**.

**Formal statement** (`348.lean`). Monotone `a : ℕ → ℕ`. Removal is `Function.updateFinset a s 0`, meaning set to 0.
Completeness is `IsAddCompleteNatSeq'` (every large k is a sum over a Finset of indices), i.e. weak completeness with
multiplicities. Condition 2 is read as ∀. **Matches the intended weak reading.** Zero entries are harmless: they only make
condition 2 harder. Expected answer: `{(m,n) | m < n ∧ m ≤ 1}`.

**Verdict:** solved, including a Lean proof. The only thing left is to port the proof to the formal-conjectures
`erdos_348` statement, and ljhfafa or Woett will likely do that. No contribution room.

---

## #774 (proportionately dissociated ⇒ finite union of dissociated?)

**Site statement (OPEN; last edited 28 Dec 2025).** A⊂ℕ is dissociated if its finite subsets have distinct sums. A is
proportionately dissociated if every finite B⊂A contains a dissociated set of size ≫|B|. Is every proportionately
dissociated set a finite union of dissociated sets? Alon–Erdős [AlEr85] thought this "unlikely". Pisier [Pi83]:
proportionately dissociated ⇔ Sidon set in the harmonic-analysis sense. The Sidon (B₂) analogue has a negative answer
(Nešetřil–Rödl–Sales [NRS24]; see also Reiher–Rödl–Schacht arXiv:2409.04809).

**Forum:**
- Alex Grebennikov, 31 Oct 2025: NRS resolved the combinatorial-Sidon analogue in the negative. Site updated.
- Dogmachine, 07 Feb 2026: link to #846 and #847.

**Proof claims:** none. Nobody is listed as working on it.

**Literature:** "dissociated" here is the same as quasi-independent. By Pisier and Bourgain, #774 is equivalent to the
classical open question **"Is every Sidon subset of ℤ a finite union of quasi-independent sets?"** (Malliavin, Pisier,
Bourgain). arXiv:2606.06669 ("The Sidon Decomposition Problem in Abelian Groups of Bounded Torsion", June 2026) settles
the bounded-torsion case and says **ℤ remains open**. Older partial results: Malliavin–Brameret & Malliavin (prime
exponent), Varopoulos and Bourgain (squarefree exponent). JSP PR #3379 ("JSP-000774 register Lean formalization") is a
catalogue entry and unrelated to Erdős #774.

**Formal statement** (`774.lean`). `IsDissociated` = InjOn of subset sums over finite subsets. Proportional: ∃c>0 ∀
finite B⊆A ∃S⊆B, #S ≥ c#B, S dissociated. Conclusion: A = ⋃₀T with T finite. `A.Infinite` is assumed. **Matches.**

**Verdict:** a well-known hard problem in harmonic analysis. **No realistic laptop contribution.** A counterexample would
need a new NRS-style construction for ±1-linear relations instead of B_h. Possible side project: formalize the easy
converse, "finite union of dissociated sets ⇒ proportionately dissociated" (pigeonhole, c=1/k). It is trivial and would be
a test lemma, not progress.

---

## #289 (1 = Σ reciprocals over separated intervals of length ≥2)

**Site statement (OPEN on the site; last edited 22 Sep 2025).** For all large k, are there intervals I₁..I_k ⊂ ℕ, distinct,
non-overlapping and non-adjacent, each with |I_i|≥2, such that Σ_i Σ_{n∈I_i} 1/n = 1? Example for 2 (Hickerson–Montgomery,
AMM E2689): [2,7],[9,10],[17,18],[34,35],[84,85]. Dual problem: #288.

**Forum:**
- Dogmachine, 09 Aug 2025: dual of #288.
- Dogmachine, 29 Aug 2025: [ErGr80] notes that the intervals cannot all be equal.
- Kovač, 22 Sep 2025: an easy yes-proof when overlaps are allowed (CRT plus a 4-element-multiset splitting lemma). Argues
  the intended version is non-overlapping and non-adjacent. The site was changed.
- Kovač, 18 Dec 2025: the Lean file still had the old variant and a fix was proposed. **The local file now has the fix.**

**Proof claims (2), both full:**
- **Johan Land, 2026-09-04** (Astra, "Fabel 5.1", Gemini-Flash-3.8). Intervals ⊂[1,20k] with |I|∈{2,3}, using
  Conlon–Fox–Pham-style absorption and Liu–Sawhney. **Lean: github.com/beetree/math_erdos_289**, about 9.1k lines plus
  about 120k lines of vendored dependencies, no `sorry`, standard axioms. He found a way to avoid Bourgain–Garaev.
  7 comments: Yuren Tang says he had an independent manuscript in mid-August; StijnC asks for a "book" proof; Land
  proposes a joint paper with Tang and Cambie (the "Cambie–Land–Tang paper", `Erdos289.CLT.MainStatement`); Xiao Hu
  replies.
- **Yuren Tang, 2026-09-07** (GPT-5.6 Sol, GPT-6 Astra, Claude Opus 5): "Reciprocal Sums over Separated Integer Intervals",
  github.com/Yuren-Tang/erdos-289 v1.0.0. Stronger: components of size 2 or 3. Tools: Dias da Silva–Hamidoune and
  Haxell's independent transversals. Includes an exact-arithmetic verifier.
- Related: Korsky, arXiv:2607.04157 (Jul 2026), a stretched-exponential bound for an Erdős–Graham unit-fraction problem.
  Conlon–Fox–He–Mubayi–Pham–Suk–Verstraëte, arXiv:2404.16016. JSP PRs #2541, #2600, #3673, #3736 record the Lean evidence.

**Formal statement** (`289.lean`). `I : Fin k → ℕ×ℕ` with `(I i).1 < (I i).2` (so |I|≥2) and separation
`(I i).2+1 < (I j).1 ∨ …`, which gives non-adjacent and hence distinct intervals. Sum is in ℚ. **Matches the current site.**
One harmless quirk: an interval can start at 0 and 0⁻¹=0 in ℚ, but any such interval has sum ≥1, which forces k=1, so it
does not affect "for all large k".

**Verdict:** solved, pending acceptance on the site. It has a Lean proof with no `sorry`. No contribution room.

---

## #197 (brief): split ℕ into 2 sets, each permutable to avoid monotone 3-APs?
OPEN. It is possible with 3 sets. Forum: wkasel, 26 Aug 2026 (SAT/DRAT, partial): the canonical dyadic partition
∪_{k even}(2^{k−1},2^k] **cannot** be a witness. This is arXiv:2609.02939 (Kasel, 31 Aug 2026), "Structural rigidity in the
Erdős–Graham two-set permutation problem", github.com/Wkasel/erdos197. Geneson, arXiv:2608.12604 (12 Aug 2026):
α_ℕ(3) ≥ 2/3. No proof claims. Formal: A,B complementary, each with a bijection ℕ≃A whose image sequence has no monotone
3-AP. This forces both parts to be infinite, which is harmless. **Matches** (0∈ℕ is harmless because translation preserves APs).
Laptop angle: SAT search on non-dyadic candidate partitions (for example, other block patterns). It is crowded (Kasel,
Geneson) and a "yes" needs an infinite construction.

## #655 (brief): distinct distances under "no circle centred at a point through 3 others"
The literal statement is **false**. Zach Hunter's regular n-gon gives ⌊n/2⌋ distances. Formal-conjectures already marks
`erdos_655` as `research solved` with the formal disproof (AlperTheKing fork). The site still shows OPEN and "ambiguous"
(Tao, 19 Jan 2026). Forum: Somani, Sothanaphan, Bloom, Tao (Jan 2026) on which extra assumption was intended; Bloom prefers
to leave it open-ended. Chojecki (22 Apr 2026) posted a GPT-5.4 survey of variants. The open variant is
`erdos_655.variants.general_position` (no 3 collinear, no 4 concyclic), which is a real distinct-distances problem. JSP
PR #575 formalizes the easy per-point bound (n−1)/2. Laptop angle: small-n search for general-position valid sets with few
distances, as evidence only.

## #786 (brief): density-(1−ε) sets where a₁⋯a_r = b₁⋯b_s forces r=s
OPEN (last edited 11 Apr 2026). If repetitions are allowed, both parts are **no**: [ERS73] gives density ≤1/2, and
Granville–Soundararajan give the sharp |A| ≤ (1−0.1715…)N (Tao). The no-repetition (distinct factors) version is open, and
formal-conjectures uses distinct factors (Finset products). Forum: ebarschkis, Tao, Bloom (Feb 2026) on the ambiguity. Bloom
thinks the repetition version was intended and considers it resolved in 1973. **Proof claim: Declan Gessel, 2026-09-06
(GPT-6 Astra/Codex), Lean-checked** (gist + WoshuaJolk/jig-verifier `Erdos786DistinctDensityRefuted`): with distinct
factors, natural density ≤ **7/8**. That makes part (i) **no**, so `erdos_786.parts.i` is `False`. Part (ii),
(1−o(1))N in [1,N], remains open for distinct factors; Tao conjectures the 0.1715 constant again. Formal quirk:
`A N ⊆ Set.Icc 1 (N+1)`, which should be `Icc 1 N`; harmless asymptotically. Otherwise it matches. Laptop angle for (ii):
low. The ERS/Granville–Soundararajan method uses repetitions, so a no-repetition argument needs a new probabilistic
"contiguity" argument, as Tao sketches.

---

## Verdict table

| # | still open? | attacked recently? (who/when) | known partial results | small laptop+Lean contribution plausible? | recommended next step |
|---|---|---|---|---|---|
| 1110 | Infinitude clause: **effectively solved** (Lean, all pairs). Density clause: **open** | Apiros3 (GPT-5.6, Lean) Aug 2026. Ding–Li–Liu–Zhang (GPT-5.6) Aug 2026. x2515102083 all-pairs Lean, 17 Sep 2026 | Yu–Chen'22 density 0 when e<1. (5,2): positive lower density of representables (claim) | **Yes, for density only**: (7,2) or (4,3) positive lower density via a certificate search | Get the Ding et al. preprint. Reimplement the certificate search mod 2^k for (7,2), then (4,3). Draft a `variants.density` Lean statement |
| 348 | **Solved** (answer: m ≤ 1) | Geneson (GPT-6 Astra/Codex) Sep 2026, arXiv:2609.25107. Woett Lean (sets). ljhfafa Lean (sequences), 24 Sep 2026 | complete | No (already formalized) | Drop. At most, port to the formal-conjectures statement if nobody has in about a week |
| 774 | **Open** (≡ Sidon ⊂ ℤ = finite union of quasi-independent sets?) | No claims. Bounded-torsion analogue solved (arXiv:2606.06669, Jun 2026) | Pisier'83 / Bourgain'85 characterization. NRS24 negative for the B_h analogue | No (a hard harmonic-analysis problem) | Drop |
| 289 | **Solved** (claims pending site acceptance) | J. Land (Lean, 4 Sep 2026). Y. Tang (7 Sep 2026). Cambie–Land–Tang joint paper | complete, even with |I|∈{2,3} | No | Drop |
| 197 | Open | Kasel (SAT, arXiv:2609.02939, Aug 2026). Geneson (arXiv:2608.12604) | dyadic partition ruled out. α_ℕ(3) ≥ 2/3 | Marginal: SAT exploration of other partitions only | Low priority |
| 655 | Literal: **false** (formal-conjectures already solved). General-position variant open | Hunter's n-gon. Chojecki survey Apr 2026. JSP #575 | per-point (n−1)/2 | Only evidence-level (small-n search) | Drop |
| 786 | (i) distinct factors: **no** (claim, ≤7/8, Lean). (ii) open | Gessel (GPT-6 Astra, Lean) 6 Sep 2026. Tao/Bloom Feb 2026 | repetition version fully resolved (ERS73 plus Granville–Soundararajan) | Low | Verify Gessel's Lean if we care. Otherwise drop |
