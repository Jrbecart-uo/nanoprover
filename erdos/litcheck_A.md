# Literature / status check A — Erdős #1063, #273, #203, #700

Checked 2026-09-24. Sources: erdosproblems.com problem pages, forum threads, proof-claims pages, and history pages.
Also: GitHub (formal-conjectures, TheJustinSunPrize/awards, and personal repos), arXiv, and web search.
Local FC clone: `external/formal-conjectures` @ 40a8592 (2026-09-24).

## Verdict table

| # | still open? | attacked recently by AI or humans? (who, when) | known partial results | small laptop + Lean contribution plausible? | recommended next step |
|---|---|---|---|---|---|
| 1063 | Open as "estimate n_k". **The FC target `better_upper` is effectively solved.** | Yes, heavily. Cambie (Oct 2025). rickyc + GPT-5.5/5.6 (Jun–Aug 2026). Patrick White + GPT-5.6 Sol/Claude (25 Jul 2026). jbell31 + Claude (28 Jul 2026). **Lean proof of `better_upper` by GH user 56647563 + Codex (17 Sep 2026, JSP PR #601)**. FC issue #6448 (21 Sep 2026) lists it for "mark solved". | Upper bound log n_k ≤ (k/log k)(logloglog k + loglogloglog k + log 2 + o(1)) (Cipollini/GPT claim). White: exp(C k logloglog k/log k). Lean: n_k ≤ 2^{3k/4} eventually. Lower bound: n_k ≥ ∏_{p^a‖k} p^{a+⌊log_p(k−1)⌋}; claimed log n_k ≥ c(log k)^2. Data: n_k known for k ≤ 75. | **No** for `better_upper`, which is already done. Formalizing rickyc's elementary lower bound in Lean is plausible but low value. | **Drop the triage idea.** It is subsumed several times over. Only a tighter lower bound would be new, and that looks hard. |
| 273 | Open | Yes. ideal_ombrer + AI (12 Jul 2026). Zeraoulia + GPT-5.6 (27 Jul 2026, Zenodo). jaredwilder (SAT ladder, Sep 2026). omega-institute swarm (issue #9507). JSP PRs #281/#299 formalize only the p ≥ 3 variant (Sep 2026, closed). | Any covering needs a modulus p−1 with p > 877 (claimed, BBMST sieve). Σ1/(p−1) ≥ 1 + exp(−3.36e21) (via Filaseta–Kalogirou). LCM L ≥ 393120 (claimed). Parity reduction proved in Lean (0 sorry). UNSAT results for periods 55440, 110880, 166320, 720720. The p ≥ 3 variant (Selfridge, mod 360) is already in FC as solved. | Unlikely. A construction needs huge moduli where several swarms have failed. A non-existence proof would need new ideas. | Skip, unless we have a genuinely new structural idea for large highly composite L. |
| 203 | Open | Yes. Tao (LLM literature search, Oct 2025). Dogmachine, uona, emil467q (search 1e10–1e11, Nov 2025). AnimishSharma (Jun 2026). veljjanoski + Claude (Sep 2026). Neo7672 (JSP-000190, Sep 2026). omega-institute (issue #9414). | Necessary condition Σ1/\|⟨2,3⟩ mod p\| ≥ 1. No covering exists with lcm(\|H_p\|) < 5040 for p ≤ 5·10^7. Best greedy coverage is about 72–76%. 78557 fails (2·3²·78557+1 is prime). There is no nontrivial theory beyond this. | No. A 2D covering is out of reach. A non-existence proof would need something like Sierpiński-type conjectures. | Skip. |
| 700 | **(b) SOLVED** (accepted on the site: Price/GPT-5.6 Sol Pro, 27 Jul 2026, and White+Claude, 24 Jul 2026, via Maynard). (a) and (c) are open, and (a) is arguably ill-posed. | Yes. Cambie (Aug 2025, Jul 2026 with GPT-5.6). Tao (Oct 2025). White/Claude and Price/GPT (Jul 2026). aichiwuhuarou: Lean proof of a four-prime criterion. | f(p(p+a)(p+a+c)) = p(p+a) for p > 10(a+c)², c > a. With Maynard this gives infinitely many n with f(n) ~ n^{2/3}. f(n) ≤ (1+o(1))n/log n. Families from Cambie and Siigur (conditional). | For (b), Lean needs Maynard, which is too big. The conditional three-prime lemma is feasible but was partly done already (four-prime version). (c) is very hard. | Do not attack. At most, note the FC status mismatch, which issue #6448 already tracks. |

## #1063

**Site statement (verbatim):** "Let k≥2 and define n_k≥2k to be the least value of n such that n−i divides C(n,k) for all but one 0≤i<k. Estimate n_k."
- Status: OPEN ("cannot be resolved with finite computation"). Page last edited 01 Feb 2026. OEIS A389360. Sources: ErSe83, Mo85, Guy B31.
- Known values: n_2..n_5 = 4, 6, 9, 12. Monier: n_k ≤ k!. Cambie: n_k ≤ k·lcm(2..k−1) ≤ e^{(1+o(1))k}.

**Forum comments (12):**
1. StijnC, 01 Oct 2025, 14:17: n_k ≤ k·lcm(2..k−1), so n_k ≤ exp((1+o(1))k).
2. StijnC, 01 Oct 2025, 12:40: (n_k) is not monotone.
3. StijnC, 02 Oct 2025: asks whether (1/k)log n_k converges. Over k ≤ 37, max n_k^{1/k} is at k=10 (≈2.178) and min at k=31 (≈1.337). Gives the distribution of the number of bad i for k=23.
4. rickyc (with GPT-5.5 Thinking), 26 Jun 2026: n_k ≥ max(2k, ∏_{p^a‖k} p^{a+⌊log_p(k/2)⌋}). Uses a p-adic argument. Also shows the failing index is the unique one of maximal p-adic valuation.
5. StijnC, 27 Jun 2026: n_p looks smaller for prime p. Asks what "estimate" should mean, and suggests a vote on whether the problem is worth pursuing.
6. rickyc, 27 Jun 2026: plans to improve k/2 to k−1. Calls for consensus on what "estimate" means.
7. rickyc (written by GPT-5.6 Sol), 10 Jul 2026: improves the bound to ∏ p^{a+⌊log_p(k−1)⌋}. Uses a Kummer carry argument and the identity M = a + S + v_p(C(k−1,e)).
8. old-bielefelder, 11 Jul 2026: asks who did the math.
9. rickyc, 11 Jul 2026: the original was mostly his, and the improvement came from 5.6-Sol.
10. rickyc, 11 Jul 2026: AI is good at optimising existing proofs.
11. old-bielefelder, 13 Jul 2026: AI use should be disclosed.
12. jbell31 (with Claude), 28 Jul 2026: extends OEIS A389360 from k=59 to k=75. Uses an exhaustive progression search (n ≡ r mod D(k,r)). Finds no new extremes of n_k^{1/k}. log n_k/k ≈ 0.33 is flat for prime k, while composite k decays. The lower bound is still 10^6–10^9 below n_k. Repo: github.com/Jaybell31/dreamwalk/tree/master/erdos1063.

**Proof claims (2), both by Ricky Cipollini using GPT-5.6 Sol:**
- 27 Jul 2026: log n_k ≤ (k/log k)(logloglog k + loglogloglog k + log 2 + o(1)). This improves his own bound C·k·logloglog k/log k.
- 04 Aug 2026: log n_k ≥ c(log k)².
- Both link to overleaf.com/read/hrpsqsnqktky (possibly the same document). Neither is marked as accepted.

**Other work:**
- Patrick White, github.com/pw/erdos1063-upper-bound (construction by GPT-5.6 Sol via Codex, re-verified by Claude, 25 Jul 2026). Proves n_k ≤ exp(C k logloglog k/log k).
  - Construction: an "excused coordinate" E ≈ k/(log k)³, valuation transport, and simultaneous Dirichlet approximation for large primes.
  - An earlier claim of (3/2+o(1))·lcm was retracted.
- **JSP PR #601** (github.com/TheJustinSunPrize/awards/pull/601), GH user 56647563 with Codex, 17 Sep 2026. A complete Lean proof of `Erdos1063.erdos_1063.better_upper` with upper(k) = 2^{3k/4}.
  - It proves n_k ≤ 2^{3k/4} eventually and that 2^{3k/4} = o(k·lcm) via Mathlib's `Chebyshev.two_pow_le_mul_lcmUpto`.
  - It has 7 modules, and the only axioms are propext, Classical.choice and Quot.sound.
  - JSP closed it on 20/24 Sep because it only counts as "partial progress". The code is at 56647563/awards @ 5130380.
- JSP PRs #56 and #406 formalize Monier's bound, and #154 (pcycho/erdos1063-cambie) formalizes Cambie's bound. All are closed as partial.
- In FC, PR #4135 proved `small_values`, and it is merged.
- **FC issue #6448** ("Open statements with known solutions 2", 21 Sep 2026) explicitly lists `erdos_1063.better_upper` to be marked solved, citing White.

**FC statement check:**
- `n k = sInf {m | 2k ≤ m ∧ ∃ i0<k, ¬(m−i0)∣C(m,k) ∧ ∀ i<k, i≠i0 → (m−i)∣C(m,k)}`. This is exactly "all but one", and it matches the site.
- `better_upper` only asks for some g with n_k = O(g) and g = o(k·lcm(1..k−1)). That is a weak proxy for "estimate", equivalent to n_k = o(k·lcm).
- Taking g := n itself would be a tautological `answer()`. FC's AGENTS.md says such an answer does not count as a solution.
- The variants (exists_exception, monier, cambie, exp_upper_bound) are faithful. Their k ≥ 3 guards are correct.

**Our triage idea** (relax one prime p ∈ (k/2,k) in Cambie's construction by making the window contain two multiples of p):
- Even if it works, it saves only a factor of about p ≍ k. That gives n_k ≤ O(lcm(1..k−1)), which is o(k·lcm) but only by a polynomial factor.
- The literature (White, Cipollini/GPT) already gets exp(o(k)), a saving of exp((1−o(1))k).
- The target has already been proved in Lean with 2^{3k/4}.
- **Verdict: already known, strictly implied, and already formalized. Do not pursue.** The only genuinely open part is closing the gap between exp(c log² k) and exp(k·logloglog k/log k).

## #273

**Site statement:** "Is there a covering system all of whose moduli are of the form p−1 for some primes p≥5?"
- Status: OPEN. Page last edited 01 Oct 2025. Source: ErGr80 p.24.
- Selfridge found an example using divisors of 360 when p=3 is allowed.

**Forum comment (1):** ideal_ombrer (AI-assisted), 12 Jul 2026.
- (1) Every covering needs a modulus p−1 with p > 877. The 149 moduli with p ≤ 877 give η = 0.99991772 < 1 under the BBMST distortion sieve (arXiv:1811.03547), certified with exact rationals.
- (2) Σ1/(p−1) ≥ 1 + exp(−3.36·10^21). This follows from Filaseta–Kalogirou (arXiv:2407.15280), because the 3-smooth moduli (Pierpont primes 2^a3^b+1) only sum to about 0.706 < 11/12.
- Repo: github.com/idealombrer/erdos-273-covering-pm1, with the paper, certificates, a Lean parity reduction (0 sorry), and UNSAT results for periods 55440, 110880, 166320, 720720.
- The author expects the answer "probably yes", but the covering would have to live at large moduli.

**Proof claim (1):** Rafik Zeraoulia with GPT-5.6 Thinking, 27 Jul 2026 (Zenodo 21613011).
- Claims L = lcm ≥ 393120. The reciprocal-sum condition leaves 28 candidates, parity capacity kills 23, and CRT density kills the other 5.
- Not marked as accepted.

**Other work:**
- jaredwilder/erdos273-covering-systems (Sep 2026): parity reduction to two half-moduli coverings, a SAT ladder, and a corrected "4/3 density floor".
- omega-institute/trureturing issue #9507: over 80 search "flights", a 27-class partial cover with period 75600, and failures at Q ≈ 5.6·10^14. No cover found.
- JSP PRs #281/#299 give Lean certificates of the Selfridge p ≥ 3 variant. Both were closed (procedural reasons and scope).
- Background: Hough–Nielsen (every distinct covering has a modulus divisible by 2 or 3) is not an obstruction here, since p−1 is even. I found no published theorem for or against.

**FC statement check:**
- The FC statement is `∃ c : StrictCoveringSystem ℤ, ∀ i, ∃ p prime, 5 ≤ p ∧ c.moduli i = span{p−1}`. "Strict" means the moduli are distinct, which is Erdős's convention. It matches the site.
- Minor issue: `variants.three` uses `StrictCoveringSystem ℕ` instead of ℤ. This is harmless.

## #203

**Site statement:** "Is there an integer m≥1 with (m,6)=1 such that none of 2^k3^ℓm+1 are prime, for any k,ℓ≥0?"
- Status: OPEN. Page last edited 20 Jan 2026. Source: ErGr80 p.27.
- The Sierpiński discussion was split off into #1113.
- On the q_1⋯q_r m+1 variant (q_i ≡ 1 mod 4), Dogmachine noted that m=1 is trivial, so perhaps "m even" was intended.
- Users listed as working on it: uona and AnimishSharma. Formalizing: epassports. Proof claims: none.

**Forum comments (15):**
- Dogmachine, 28 Aug 2025: heuristically m ≥ 10^10. Also cites Izotov 1995: there are non-covering Sierpiński numbers (perfect powers).
- TerenceTao, 19 Oct 2025: LLM literature search found nothing new. Gemini hallucinated coverings.
- Woett, 24 Nov 2025: cites Filaseta–Finch–Kozek (JNT 2008): for each l there is an m with 2^k m^i + 1 composite for all 1 ≤ i ≤ l.
- emil467q, 30 Nov 2025: no hit in 10^10..10^11 (shallow search).
- Bloom, 28 Dec 2025: split off #1113.
- Tao and Dogmachine, 29 Dec 2025: discussed the triviality of the q-variant.
- uona and Bloom, 31 Dec 2025: procedure. uona thinks such m should not exist.
- uona, 7 Jan 2026: asked Dogmachine to explain the 10^10 bound.
- Dogmachine, 25 Jan 2026: explained it (at least double the digits of 78557). Also noted a link to quadratic forms (Iwaniec 1974).
- AnimishSharma, 21 Jun 2026: |H_p| = lcm(ord_p 2, ord_p 3) and the necessary condition Σ1/|H_p| ≥ 1. For p ≤ 5·10^7 there is no covering with lcm < 5040. Best coverage is 71–72%. 78557 fails.
- veljjanoski with Claude, 15 Sep 2026: 2D lattice search reaching 71.7% (N=5040) and 76.0% (N=55440). Lattices rarely nest (77 nested pairs among 442 primes). Concludes that a covering, if one exists, needs much larger primes.

**Other work:**
- Neo7672/erdos-203-covering-search (JSP-000190, 16–17 Sep 2026): 105 primes with h(p) ≤ 400 give density about 1.63, but the budget surplus is only 2–15% and the search plateaus at 17–21% uncovered.
- JSP PR #626 is a Lean proof that the q-variant is trivial with m=1.
- omega-institute issue #9414.

**FC statement check:**
- `∃ m, m.Coprime 6 ∧ ∀ k l, ¬(2^k*3^l*m+1).Prime`. m=0 is excluded because gcd(0,6)=6, so this matches the site's m ≥ 1.
- There is no variant for the general p_i or q_i question (it is a TODO in the file).

## #700

**Site statement:** f(n) = min_{1<k≤n/2} gcd(n, C(n,k)). The page asks three things:
- (a) Characterise the composite n with f(n) = n/P(n).
- (b) Are there infinitely many composite n with f(n) > n^{1/2}?
- (c) Is it true that f(n) ≪_A n/(log n)^A for all A, for composite n?

Status: OPEN overall. Page last edited 28 Aug 2026. Source: ErSz78. OEIS A091963.
- The page now says: "A positive answer to the second question was provided by GPT 5.6 Sol Pro (prompted by Price) … infinitely many n (product of three primes) with f(n) ~ n^{2/3}."
- Known: f(n) ≤ n/P(n), so f(n) ≤ (1+o(1))n/log n. Also f(pq) = p, n = 30 is a further hit (f(30) = 6 = 30/5), and f(n) ≥ p(n).

**Forum comments (6):**
- StijnC, 10 Aug 2025 (18:34): (a) is likely undoable. For 4-prime products in [2,29], 19 are hits, 3 have √n < f < n/P, and 188 have f < √n. For n = q(q+1) the behaviour is inconsistent (q=1151 fails, q=2063 works).
- StijnC, 10 Aug 2025 (19:04): two conditional families for (b):
  - n = q(q+1) with q = 2^k+3 prime and k ≡ 4 mod 20 gives f = q+1.
  - Kadi Siigur's n = 2pq with 2^l < p < q < 2^{l+1} and pq ≡ 1 mod 2^l gives f = 2p.
- StijnC, 11 Aug 2025: (c) is very hard. Lists hits among products of 5, 6 and 7 primes.
- TerenceTao, 17 Oct 2025: Gemini and ChatGPT literature search. ChatGPT's "Guy B33" citation was a hallucination. Mentions Bergman on gcd(C(n,i), C(n,j)).
- StijnC with GPT-5.6, 28 Jul 2026 (07:35): (a) is essentially equivalent to the definition, and proposes abandoning it.
- StijnC, 28 Jul 2026 (09:57): GPT-5.6 Sol cannot exclude hits with ≫ q/log q prime factors. That would give a negative answer to (c).

**Proof claim (1), ACCEPTED by the site:** Liam Price with GPT-5.6 Sol Pro, 27 Jul 2026 (overleaf.com/read/pmnwkfnhhxhn).
- There exist fixed even a < c and infinitely many p with p, p+a, p+a+c all prime (from Maynard). Then n = p(p+a)(p+a+c) has f(n) = p(p+a) ~ n^{2/3}.
- StijnC checked it in detail (28 Jul 2026).
- Independently, Patrick White + Claude (erdosproblemaday.com, 24 Jul 2026) proved the three-prime lemma: for p > 10D² with D = a+c, f(pqr) = pq if c > a, and f(pqr) = p otherwise.

**Other work:**
- aichiwuhuarou/jsp-000570-lean: Lean proof of a four-prime sufficient criterion, f(P(P+a)(P+b)(P+c)) = P(P+a)(P+b). It does not include Maynard.
- FC issue #6448 (21 Sep 2026) lists `erdos_700.parts.ii` for "answer True".

**FC statement check:** parts i, ii and iii match the site.
- (ii) is written as (f n)^2 > n, which is right for the strict inequality.
- (i) was reworked into a set-level answer (FC PR #5830, 11 Sep 2026).
- Proven helpers: prime_pow (f(p^a) = p) and prime_mul (f(pq) = p).
- The local clone still tags (ii) `research open`. This is a status mismatch, already tracked in #6448.
