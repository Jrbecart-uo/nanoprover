# Literature / status check C: suspected mis-tagged `research open` statements

Checked 2026-09-24. Local FC clone: `external/formal-conjectures` @ 40a8592 (2026-09-24).
Sources:
- erdosproblems.com problem pages and forum threads, fetched on 2026-09-24.
- google-deepmind/formal-conjectures issues and PRs, searched by problem number, theorem name and keywords (REST + search API).
- arXiv and publisher pages.

Tracking issues checked for prior reports: #4927 "Open statements with known solutions", #6448 "... 2", #4923 "Possible misformalizations II" and #4896 "Tracking: possible misformalizations". None of them mentions items 1-6 below.

## Verdict table

| # | FC declaration | Verdict | Key evidence |
|---|---|---|---|
| 1 | `Erdos357.erdos_357.variants.hegyvari` | **CONFIRMED-KNOWN** (should be `research solved`) | Hegyvári, *On consecutive sums in sequences*, Acta Math. Hungar. 48 (1986) 193–200. The site states exactly (1/3+o(1))n ≤ g(n) ≤ (2/3+o(1))n. Beker (arXiv:2311.10087, BLMS 2024) independently cites the lower bound. The FC docstring itself says "It is known". |
| 2 | `Erdos44.erdos_44.variants.empty_start` | **CONFIRMED-KNOWN**, answer `True` | Singer 1938 perfect difference sets, plus p_{n+1}/p_n → 1 (Chowla, and Erdős, 1944). erdosproblems.com/30: "Singer [Si38] was the first to show that h(N) ≥ (1−o(1))N^{1/2} for all N". O'Bryant survey EJC DS11 (2004). |
| 3 | `Erdos184.erdos_184.variants.covering` | **CONFIRMED-KNOWN**, answer `True` | L. Pyber, *An Erdős–Gallai conjecture*, Combinatorica 5 (1985) 67–79, doi:10.1007/BF02579444: every n-vertex graph is covered by n−1 circuits and edges. Restated in arXiv:2509.01901 ("Tight bounds for cycle-edge decompositions and covers"). The site page does not mention Pyber. |
| 4 | `Erdos80.erdos_80` | **CONFIRMED-KNOWN**, answer `False` | Fox–Loh, *On a problem of Erdős and Rothschild on edges in triangles*, Combinatorica 32 (2012) 619–628, arXiv:1106.0290: h(n,c) = n^{O(1/log log n)} for every fixed c < 1/4, "answering Erdős's question in the negative". The site says "disproving the first conjecture of Erdős". `variants.log` stays genuinely open. |
| 5 | `Erdos319.erdos_319.variants.isTheta` | **CONFIRMED-KNOWN** (answer `fun N ↦ N`), relative to FC's own `variants.lb` | Upper bound c(N) ≤ N is trivial. Lower bound (1−1/e+o(1))N is `variants.lb` (Adenwalla via Croot 2001), tagged `research solved` in the same file. PR #5843 kept `isTheta` as open, saying it "pins the growth rate up to constants", but did not notice that `lb` already settles it. |
| 6 | `Erdos261.erdos_261.variants.two_representations` | **CONFIRMED-DEGENERATE** (literal answer `True`). Noted on the forum only; **not reported on FC** | Forum thread 261: Zeraoulia Rafik (2026-04-27) gives 7/4 = Σ_{ℕ∖{5,6}} = Σ_{ℕ∖{4}}. Kovač (2026-05-05) replies that "two" is believed to be a misprint for 2^ℵ₀. FC issue #458 and PR #1902 (merged 2026-09-02, after the forum comment) have no discussion of it. There is no other FC issue or PR. |
| 7a | `Erdos1055.erdos_1055.variants.erdos_limit` / `selfridge_limit` | **NOT-CONFIRMED** (not a defect) | These are two incompatible competing conjectures (Erdős: p_r^{1/r} → ∞; Selfridge: bounded; Guy A18). Each is correctly a separate open `sorry`, which is standard FC practice. They are not complementary, since both can fail. The earlier genuine bug in `IsOfClass` (#4976) was fixed by #4988. |
| 7b | `Erdos885.erdos_885` | **NOT-CONFIRMED** as degenerate; it is a minor weakening | 0 ∈ D(m²) gives one free common element only when every N_i is a square. The literal problem then asks for k squares with k−1 common nonzero differences. That is still a nontrivial "(k)×(k−1) sums of squares" problem, and the ∀k question stays open. PR #5055 (open) uses the 0 trick in its k=3 witness {44², 70², 180²} with differences {0,105,480}. |
| 7c | `Erdos1056.erdos_1056` | **Partly CONFIRMED-DEGENERATE**: only the k=2 instance is trivial; the main ∀k statement is not | I_1={1}=Ico 1 2 and I_2=[2,p−2] give 1 and (p−2)! ≡ 1 by Wilson, so k=2 is trivial for every prime p ≥ 5. For general k, {1} gives only one free interval. The literal problem at k is at most the intended problem at k−1, and the ∀k question stays open. Forum 1056 (Kitamura, 2026-06-21) already gives explicit witnesses for all 2 ≤ k ≤ 14 (p = 10428007). |

## Details

### 1. #357 `variants.hegyvari`
- **Lean:** `g n = sSup {k | ∃ a : Fin k → ℕ, range a ⊆ Icc 1 n ∧ HasDistinctSums a}`. `HasDistinctSums` requires injectivity of interval sums over all order-connected finsets (∅ and singletons included, so the values are distinct). The statement is `∃ o o' = o(1), ∀ᶠ n, g n ∈ [(1/3+o n)n, (2/3+o' n)n]`. It is tagged `research open`.
- **Site (357, last edited 12 Jan 2026):** "If g(n) is the maximal k such that there are 1≤a_1,…,a_k≤n with all consecutive sums distinct (i.e. we drop the monotonicity assumption…) then Hegyvári [He86] has proved that (1/3+o(1))n ≤ g(n) ≤ (2/3+o(1))n."
- **Corroboration:**
  - Beker, arXiv:2311.10087, §1: "an affirmative answer was given by Hegyvári, who showed more strongly in [5] that one can find a sequence of length (1/3+o(1))n in [n] with all consecutive sums distinct".
  - Forum 357, Adenwalla (9 Dec 2025): "The upper bound f(n) ≤ g(n) ≤ 2n/3 follows from Hegyvári's paper".
- **Definition match:** exact. The site's g drops monotonicity. Distinct values are forced by singleton sums in both versions. `sSup` is fine because k ≤ n.
- **FC status:** no issue or PR mentions it. PR #4967 (open) deals with other 357 growth targets, and #4896 only flags the weak-monotone variant. This is the FC docstring contradicting its own tag.
- **Fix:** `@[category research solved]`.

### 2. #44 `variants.empty_start`
- **Lean:** `answer(sorry) ↔ ∀ ε > 0, ∀ᶠ M in atTop, ∃ A ⊆ Icc 1 M, IsSidon A ∧ (1−ε)√M ≤ |A|`. `IsSidon` is the standard definition (FormalConjecturesForMathlib/Combinatorics/Basic.lean:67).
- **Math:**
  - For each prime q, Singer gives a Sidon set of size q+1 modulo m = q²+q+1. Its representatives in [1,m] form a Sidon set in ℤ.
  - Given M, take the largest prime q with q²+q+1 ≤ M. Since p_{n+1}/p_n → 1, q = (1−o(1))√M.
  - So |A| = q+1 ≥ (1−ε)√M eventually, and the answer is `True`.
  - This is the classical fact h(N) ~ √N (lower half).
- **Citations:**
  - J. Singer, Trans. AMS 43 (1938) 377–385.
  - S. Chowla, Proc. Nat. Acad. Sci. India 14 (1944).
  - P. Erdős, J. London Math. Soc. 19 (1944), addendum to Erdős–Turán 1941.
  - Bose–Chowla (1962/63).
  - K. O'Bryant, "A complete annotated bibliography of work related to Sidon sequences", EJC Dynamic Survey DS11 (2004).
  - erdosproblems.com/30: "Singer [Si38] was the first to show that h(N)≥(1−o(1))N^{1/2} for all N."
- **FC status:**
  - PRs #1153 and #1265 (2025) fixed the quantifiers but left the tag `open`.
  - PR #2921 (closed, 2026-03) was a bogus "formally solved" loophole PR and did not raise the literature point.
  - No open issue.
  - Related open PR #3935 (Erdős 30) adds a *conditional* Singer witness; it is not a fix.
- **Fix:** `research solved` (arguably `textbook`) with `answer(True)`.

### 3. #184 `variants.covering`
- **Lean:**
  - Statement: `answer(sorry) ↔ ∀ V [Fintype] [Nonempty] G, ∃ D : Finset G.Subgraph, (∀ H ∈ D, IsCycleOrEdge H.coe) ∧ ⋃ H ∈ D, H.edgeSet = G.edgeSet ∧ |D| ≤ |V| − 1`.
  - `IsCycleOrEdge` means connected and 2-regular (a simple cycle), or exactly one edge.
- **Literature:**
  - Pyber 1985, abstract: the Erdős–Gallai conjecture "every graph on n vertices can be covered by n−1 circuits and edges" is proved.
  - arXiv:2509.01901: "The covering version of this conjecture was proven by Pyber in 1985, where it was shown that all graphs can be covered by n−1 cycles and edges". The paper then sharpens it: only forests need n−1.
- **Definition match:** exact. "Circuit" means simple cycle = connected 2-regular subgraph. Empty-edge graphs are handled by D = ∅, and n = 1 gives 0 ≤ 0.
- **FC status:** issue #410 and PR #2287 have no discussion of this. The docstring copies the site ("Erdős suggests…"), and the site itself omits Pyber. It could also be reported to the site.
- **Fix:** `research solved`, `answer(True)`, and cite [Py85].

### 4. #80 `erdos_80`
- **Lean:** `answer(sorry) ↔ ∀ c, 0 < c → c < 1/2 → ∃ ε > 0, ∀ᶠ n, n^ε < f c n`. Here `f c n` is the least book number over n-vertex graphs with ≥ cn² edges and every edge in a triangle.
- **Literature:** Fox–Loh (Combinatorica 32 (2012) 619–628; arXiv:1106.0290), abstract: "H(N,C) = N^{O(1/log log N)} for fixed C < 1/4, answering Erdős's 1987 question in the negative".
- **Why the answer is False:** take c = 1/8. For every ε > 0, eventually f c n ≤ n^{O(1/log log n)} < n^ε. So the ∀c statement fails.
  - The c < 1/2 restriction added in #4877 does not rescue it.
  - For c > 1/4, f ≥ n/6 (Edwards; Khadzhiivanov–Nikiforov), but the statement is universal in c.
- **Site:** "Fox and Loh [FoLo12] proved f_c(n) ≤ n^{O(1/log log n)} for all c<1/4, disproving the first conjecture of Erdős". The site's overall "OPEN" status refers to "estimate f_c(n)" and the log n question.
- **FC status:** #309, #4830, #4867 and #4877 have no mention of Fox–Loh. The FC docstring omits it. `variants.log` (f ≫ log n) is genuinely open: the best lower bounds come from regularity and are tower-type.
- **Fix:** `research solved` with `answer(False)`.

### 5. #319 `variants.isTheta`
- **Lean:** for any `c` with `IsGreatest S_N (c N)` for all N, `c =Θ[atTop] answer(sorry)`.
- **Proof with `answer(fun N ↦ (N:ℝ))`:**
  - c N ∈ S_N means c N = |A| for some A ⊆ [1,N], so c N ≤ N.
  - `IsGreatest.csSup_eq` gives c N = sSup S_N.
  - `variants.lb` then gives c N ≥ (1−1/e+o(1))N ≥ N/2 eventually.
- **Lower bound source (site text):**
  - Adenwalla: Croot [Cr01] gives B ⊂ [(1/e−o(1))N, N] with Σ1/b = 1, which forces |B| ≥ (1−1/e+o(1))N.
  - Take A = B ∪ {1} with δ(1) = +1 and δ = −1 on B.
  - Minimality holds: a proper subset without 1 has a negative sum, and one with 1 has a positive sum.
- **Caveats:**
  - `lb` itself is a `sorry` in FC, tagged solved. The claim is "known modulo the literature result FC already accepts".
  - What remains open is the exact constant or the asymptotic c(N) ~ αN, which `erdos_319` with `answer(sorry)` still captures loosely.
- **FC status:** #4892 and PR #5843 (merged 2026-09-13) removed the tautological `isBigO`/`isLittleO` and explicitly kept `isTheta` as open. Nobody noted that `lb` settles it.
- **Fix:** mark solved with `answer(fun N ↦ N)`, or delete it as redundant.

### 6. #261 `variants.two_representations`
- **Lean:**
  - Statement: `answer(sorry) ↔ ∃ x : ℚ, 2 ≤ #{a : ℕ → ℕ | Erdos261InfiniteRepresentation x a}`.
  - A representation means a strictly monotone a ≥ 1 with Σ a_k/2^{a_k} = x (summable).
- **Witness:** x = 3/8.
  - a = (4, 7, 8, 9, …) and a' = (5, 6, 7, 8, …) both give 3/8.
  - This uses 4/2⁴ = 5/2⁵ + 6/2⁶ = 1/4 and Σ_{k≥7} k/2^k = 8/2⁶ = 1/8.
  - A kernel-checked proof is in `erdos/erdos_261_two_reps.lean`.
- **Forum 261:**
  - Zeraoulia Rafik (23:10, 27 Apr 2026) gave the same trick with x = 7/4 and noted it is "literal interpretation".
  - Vjeko_Kovac (5 May 2026): "It is generally believed that 2 or 'two' was a misprint or misread typo and that it should have been 2^ℵ₀."
- **FC:**
  - Issue #458 has no comments.
  - PR #1902 (merged 2026-09-02) has only an unrelated review ping.
  - Searches for "two_representations", "erdos_261", "Erdős 261", "7/4" and "3/8" find no issue or PR about this.
- **Verdict:** not reported on FC. The trick extends to any finite number of disjoint swap gadgets, giving 2^n representations for every finite n. It does not give 2^ℵ₀ (`parts.iii` is still open).
- **Suggested FC action:** mark `research solved`, `answer(True)`, with a docstring note that the literal "two" is trivial and Kovač's misprint remark. Alternatively, strengthen the variant to ℵ₀ (infinitely many representations). That version is not obviously trivial, because infinitely many gadgets are needed and rationality of Σ n_i/2^{n_i} becomes the issue.

### 7a. #1055 `erdos_limit` vs `selfridge_limit`
- **Lean:**
  - `erdos_limit`: `Tendsto (fun r ↦ (p r)^(1/r)) atTop atTop`.
  - `selfridge_limit`: `∃ M, ∀ r, (p r)^(1/r) ≤ M`.
  - Both are `research open` sorry theorems.
- **Analysis:**
  - The two are mutually exclusive. At most one is true, and both could be false (limsup = ∞, liminf < ∞).
  - FC routinely formalises competing conjectures as separate open statements, and a `sorry` theorem is a conjecture, not a claim. This is not a defect.
  - Guy A18 records the Erdős and Selfridge opinions. The site page lists only "how does p_r^{1/r} behave?".
  - Elementary bound: p_r + 1 ≥ 2 p_{r−1}, so p_r ≫ 2^r. Nothing near either conjecture is known.
- **FC history:** the real bug was `IsOfClass` accepting lower classes (p 2 = 2). It was reported in #4976 and fixed in #4988 (2026-08-16). The current definition matches A005113 (2, 13, 37, 73, 1021).

### 7b. #885 zero difference for squares
- **Lean:**
  - `factorDifferenceSet n = {d | ∃ a b, n = a*b ∧ d = |a−b|}`, which contains 0 iff n is a square.
  - The site's D(n) = {|a−b| : n=ab} literally contains 0 as well.
- **Effect:** when all N_i are squares, 0 is a free common element. The requirement drops to k−1 common *nonzero* differences for k squares.
- **Why it is not degenerate:**
  - By the forum reformulation (Aleksanndr_NFA, 23 Sep 2026), d ∈ D(N) iff 4N + d² is a square.
  - So the reduced problem needs k values x_i = 2m_i and k−1 values d_j with every x_i² + d_j² a square.
  - That is a (k)×(k−1) rational "sums of squares" configuration, of the same nature as the original. Nothing trivialises it.
- **Where it matters:**
  - Open PR #5055 proves `k_eq_3` with the witness {44², 70², 180²} and differences {0, 105, 480}. This is formally valid, but the literature's k=3 examples use nonzero differences, e.g. D(112) ∩ D(952) ∩ D(3240) ⊇ {6, 54, 111}.
  - The k=4 proof in the file (Bremner's witness, merged in #6509) uses only nonzero differences.
- **Recommendation:** a small docstring note, or `0 < d`. Not a mis-tag.

### 7c. #1056 interval {1}
- **Lean:**
  - `∀ k ≥ 2, ∃ p prime, ∃ boundaries : Fin (k+1) → ℕ strictly monotone, ∀ i, ∏_{Ico b_i b_{i+1}} n ≡ 1 [MOD p]`.
  - A block containing 0 or a multiple of p has product 0, so all blocks lie in one residue run (mp, (m+1)p). This is the same as the intended setting.
- **k=2 is trivial:**
  - Boundaries (1, 2, p−1) give {1} with product 1, and [2, p−2] with product (p−2)! ≡ (p−1)!/(p−1) ≡ (−1)/(−1) = 1 (Wilson).
  - This works for every prime p ≥ 5, e.g. p=5: {1},{2,3}.
  - Erdős's own k=2 example (3·4 ≡ 5·6·7 mod 11) deliberately avoids 1 and 2, which suggests the intended problem excludes such trivial blocks.
- **General k:** the only free block is {1}, and the Wilson block is available once. So the literal problem at k is implied by the intended one at k−1, and the ∀k statement is still open.
- **Forum:** Kitamura (21 Jun 2026) gives a 14-interval witness mod 10428007. Lorenzo Luccioli/Aristotle (Jan 2026) give a Lean reduction to Noll–Simmons.
- **Side note:** in `variants.noll_simmons`, 0! = 1! = (p−2)! ≡ 1 give 3 congruent factorials for free. This is harmless because the statement is `∀ᶠ k`.
- **Recommendation:** optionally require `2 ≤ boundaries 0`, or document it. Not a mis-tag of the main statement.

## Links
- https://www.erdosproblems.com/357 , /forum/thread/357
- https://www.erdosproblems.com/30 (Singer lower bound), /44, /forum/thread/44
- https://www.erdosproblems.com/184 ; https://link.springer.com/article/10.1007/BF02579444 ; https://arxiv.org/abs/2509.01901
- https://www.erdosproblems.com/80 ; https://arxiv.org/abs/1106.0290 ; https://link.springer.com/article/10.1007/s00493-012-2844-3
- https://www.erdosproblems.com/319 ; FC #4892, #5843
- https://www.erdosproblems.com/forum/thread/261 ; FC #458, #1902
- https://www.erdosproblems.com/1055 ; FC #4976, #4988
- https://www.erdosproblems.com/forum/thread/885 ; FC #5050, #5055, #6509
- https://www.erdosproblems.com/forum/thread/1056 ; FC #1099, #1133
- https://arxiv.org/abs/2311.10087 (Beker, cites Hegyvári's lower bound)
