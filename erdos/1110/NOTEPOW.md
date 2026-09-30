# Power lower bounds for $\lbrace 9,2\rbrace$- and $\lbrace 5,3\rbrace$-representable integers

*Jean-Roch Bécart, using Claude Opus 5.5 (Anthropic) via Claude Code. Draft, 2026-09-30.*

*Status: computer-assisted proof. The reduction "certificate ⇒ power lower bound" is formalized in Lean 4 /
Mathlib (`lean/E1110G.lean`, `pow_lower_bound`, `erdos1110_92_pow`, `erdos1110_53_pow`; no `sorry`, axioms
`[propext, Classical.choice, Quot.sound]`). The two finite certificates are checked by an exact C program and
cross-checked state by state by an independent Python big-integer program. They are not checked in Lean.
Not yet reviewed by a human expert.*

## 1. Statement

For coprime $p>q\ge2$, call $n$ representable if $n=\sum_i p^{a_i}q^{b_i}$ with no summand dividing another
(Erdős problem #1110), and let $R_{p,q}(x)=\#\lbrace n\le x:\ n\text{ representable}\rbrace$. The pairs not covered
by Yu–Chen's density-zero theorem are $(5,2),(7,2),(9,2),(4,3),(5,3)$. Positive lower density has been claimed
for $(5,2)$ (Ding–Li–Liu–Zhang), $(7,2)$ and $(4,3)$ (our notes `NOTE.md`, `NOTE43.md`). For $(9,2)$ and $(5,3)$
the certificate method does not reach the density threshold at computable sizes.

**Theorem.** For all sufficiently large $x$:
$$R_{9,2}(x)\ \gg\ x^{851/949}\quad(851/949=0.8967\ldots),\qquad R_{5,3}(x)\ \gg\ x^{69/77}\quad(69/77=0.8961\ldots).$$

We have not found power lower bounds for these pairs on the problem page or in the papers it cites. The
empirical densities (about 6% for $(9,2)$ and 4% for $(5,3)$ at $2^{64}$, flat) suggest that $R(x)\asymp x$.

## 2. The criterion (Theorem A″)

We use the certificate of `NOTE43.md` §2: digits in base $b$, the other base $r$, blocks of $s$ digits,
$D$-digit states, a viable set $W$, a policy, a potential $V$ and a drift bound $g$, with the same four
conditions (residue, closure, padding closure, drift).

**Theorem A″.** Suppose a certificate exists with $W\ne\varnothing$ and $g<\lambda$, where $\lambda\ge0$ and now
$b^s<r^\lambda$. Then for every $\alpha\ge0$ with $r^{\lambda\alpha}\le b^s$ we have $R_{r,b}(x)\gg x^{\alpha}$.

*Proof.* Run the encoding of Theorem A′ unchanged. The Markov step uses only $g<\lambda$. It shows that at least
half of the viable residues $y$ mod $b^{sN+D+s}$ have $G_N\le N\lambda+c_0$. For those $y$ the encoded integers
are representable, and distinct residues mod $b^{sN}$ give distinct integers. So at least $b^{sN}/(2b^D)$
representable integers arise. Only the size bound changes. With $\ell=r^\lambda>b^s$ and $G_t\ge t\lambda$,
$$n(y)\ \le\ b^s r^{A}\sum_{t<N}(b^s)^t\ell^{-t}\ \le\ b^s r^{c}\sum_{t<N}(b^s)^t\ell^{N-t}\ \le\ C\,\ell^N,$$
with $C=b^s r^{1+\lceil c_0\rceil}\ell/(\ell-b^s)$. The geometric series is now dominated by its $t=0$ term.
For $C\ell^N\le x<C\ell^{N+1}$ this gives $R(x)\ge b^{sN}/(2b^D)\ge (\ell^N)^\alpha/(2b^D)\ge x^\alpha/(2b^D(C\ell)^\alpha)$.
$\square$ (Lean: `E1110G.pow_lower_bound`.)

The exponent is $\alpha = s\log b/(\lambda\log r)$, arbitrarily close to $1/\text{ratio}$, where
ratio $=g/(s\log_r b)$ is the quantity the certificate search reports. The flat certificate ($V=0$, minimal
chains, no look-ahead) gives only $x^{0.68}$ for $(5,3)$ in base 3. The look-ahead potential is what brings the
exponent near $0.9$.

## 3. The certificates

Both certificates use one digit per block ($s=1$), heights at most $H=12$, and for each residue class the
chains with $h\le\min+7$. The viable set is all states (no dead residues when $s=1$). The potential comes
from value iteration with a $(D+1)$-digit window (`gvid B Q 1 D 12 iters 7`, 260–300 iterations).

| pair | digits $b$ | $r$ | $D$ | states | GNUM | $g=\mathrm{GNUM}/(b\cdot2^{20})$ | $\lambda$ | $\alpha$ ($\lambda\alpha$) |
|---|---|---|---|---|---|---|---|---|
| (9,2) | 2 | 9 | 26 | $2^{26}$ | 736074 | 0.3509874 | $13/37$ ($2^{37}<9^{13}$) | $851/949$ ($23/73$; $9^{23}\le2^{73}$) |
| (5,3) | 3 | 5 | 17 | $3^{17}$ | 2390897 | 0.7600457 | $35/46$ ($3^{46}<5^{35}$) | $69/77$ ($15/22$; $5^{15}\le3^{22}$) |

As ratios to the threshold, these are 1.1126 for (9,2) and 1.1134 for (5,3).

* **Exact check** (`verifyd.c`, integer arithmetic, $V$ scaled by $2^{20}$ and rounded). It rebuilds $W$
  (all states, bad = 0) and evaluates the drift inequality on every state. The maximum is GNUM, attained at
  state 34715034 for (9,2) and 46408945 for (5,3).
* **Independent check** (`verify43_probe.py`, Python big integers; chains via itertools, inverses via
  `pow(Q,-g,·)`, transitions computed on windows with random high digits). It covers 400 random states plus
  the argmax and extreme states. The per-state drift values agree exactly with `verifyd` on all 404 states
  for each pair, and the argmax value is reproduced.
* **Tables**: `data_pow/V92_d26.bin.xz` and `data_pow/V53_d17.bin.xz` (float32, gvid transposed layout;
  gitignored, 145 MB and 278 MB). SHA-256 of the uncompressed files are in `data_pow/SHA256SUMS`. Any table
  that passes the checker is a valid certificate, so re-running the search and then the checker also suffices.

Window scans (ratio at convergence, which lower-bounds what larger windows can do): (9,2) D=15 1.1795,
D=20 1.1425, D=22 1.1317, D=24 1.1217, D=26 1.1126. (5,3), base 3: D=13 1.1415, D=17 1.1134. Base 5 is much
worse (1.365). The exponent creeps toward 1 like the online rate (see FINDINGS), so this method cannot give
$x^{1-o(1)}$ in practice, let alone positive density.
