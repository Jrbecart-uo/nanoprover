# Clean-room checker: results

I wrote the checker in Rust (`src/main.rs`, Cargo project in this directory) from `SPEC.md` alone,
plus the coordinator's later addition of instance (7,2). I did not read any other implementation,
log or expected-result file. Machine: 8 cores, WSL2. Build:
`RUSTFLAGS="-C target-cpu=native" cargo build --release`.
Usage: `indep_rs selftest`, `indep_rs run NAME B Q s D H SLACK a b TABLE T|N SHA`, `indep_rs sha FILE`.

## Results

| instance | (4,3) | (9,2) | (5,3) | (7,2) layout N (natural) | (7,2) layout T (transposed) |
|---|---|---|---|---|---|
| B,Q,s,D,H,SLACK | 4,3,2,14,18,12 | 2,9,1,26,12,7 | 3,5,1,17,12,7 | 2,7,11,22,10,3 | 2,7,11,22,10,3 |
| M (states) | 268435456 | 67108864 | 129140163 | 4194304 | 4194304 |
| chains / kept (distinct (v,h)) | 190 / 137 (137) | 13 / 9 (9) | 13 / 9 (9) | 352716 / 70701 (69131) | same |
| covered classes | 11/16 | 2/2 | 3/3 | 2048/2048 | 2048/2048 |
| \|W\| | **178956970** (5592406 removed from 184549376 covered) | **67108864** (all) | **129140163** (all) | 4194304 (all) | **4194304** (all) |
| bad | **0** | **0** | **0** | 0 | **0** |
| GNUM | **42192162** | **736074** | **2390897** | 22313851226 | **8385274094** |
| argmax x (smallest) | 80755765 | 600987 | 15421606 | 2101083 | 1277739 |
| g = GNUM/(P·2^20) | 21096081/8388608 = 2.514848828315734… | 368037/1048576 = 0.350987434387207… | 2390897/3145728 = 0.760045687357584… | 11156925613/1073741824 = 10.3906966866925… | 4192637047/1073741824 = 3.904697529040277… |
| λ | 58/23 = 2.521739130434782… | 13/37 = 0.351351351351351… | 35/46 = 0.760869565217391… | 286/73 = 3.917808219178082… | 286/73 |
| g < λ (GNUM·b < a·P·2^20) | **true** | **true** | **true** | false | **true** |
| Q^a < B^(s·b) | true | false | false | true | true |
| B^(s·b) < Q^a | false | true | true | false | false |
| W iteration passes (full?, removed) | (F,5585748),(dirty,6658),(dirty,0),(F,0) | (F,0) | (F,0) | (F,0) | (F,0) |
| runtime (wall, incl. load+SHA) | 127.8 s (W 13.8 s, potential 97.4 s) | 7.1 s | 16.3 s | 175.7 s | 161.2 s |
| SHA-256 verified | `.xz`: 15eb0c88…6a71 = `data_43/V43_final.bin.xz.sha256` ✔; uncompressed (computed, no reference given): cc32e163ac5bac97fe5111242e40d7f5ae2bf4f636961b07a6c5cd9ba3f1f080 | df36042caada6ed6d20c255dae4b8f04de063784fb547318ce9b92d4b7f1db68 ✔ | 0906e8b2dd421a0a8e0a94fabde3060fecf91960a1dde13dda5b910a4ffead82 ✔ | f7f832116362b96db8ba42884e61803aa5e7cd02071a45f3353072ee4bdd9258 (prefix f7f83211 / suffix dd9258 ✔) | same |

Argmax digits, most significant first:
(4,3) base 4 `1 0 3 1 0 0 0 3 3 0 0 3 1 1`;
(9,2) base 2 `00000010010010101110011011`;
(5,3) base 3 `0 1 0 0 2 0 0 0 1 1 1 1 1 0 1 2 1`;
(7,2)T base 2 `0100110111111100101011`.

**Verdict.** All four certificates pass (W nonempty, bad = 0, g < λ). For (4,3), (9,2) and (5,3)
this uses the transposed layout from the spec. For (7,2) the table only passes when read with the
transposed layout. The natural layout gives g ≈ 10.39, which is impossible for a valid table, so
the table is clearly transposed. Every computation in these runs was exact integer arithmetic.
Peak RSS was about 0.8 GB for (9,2); the (4,3) run held a 1 GB table, 2 GB of Vi and a 34 MB W
bitset.

## Self-tests (all passed, 4.2 s total; `indep_rs selftest`)

1. **Transition vs a direct big-integer computation.** The tiny cases were B=4,Q=3,s=1,D=3,H=4;
   B=2,Q=9,s=1,D=5,H=4; (4,3,s=2,D=4,H=5); (2,7,3,6,3); (3,5,1,4,4); (5,2,2,3,3). The test also ran
   on all four real parameter sets. Each case drew 3000 random (x, u, chain) triples with the chain
   of class x mod P. For each triple I took Y = z + M'·R, where z = x + M·u and R is random: 0 or a
   number of about 128 bits, three draws per triple. The direct value is
   N = Q^h·Y − Σ_i B^{α_i}·Q^{h−γ_i}, an integer because h > γ_i. The test checks that P | N and
   that (N/P) mod M equals `next` from the spec's u128 formula. The high digits never mattered. The
   same triples also checked two other formulas against the literal one: the fast internal-index
   formula, and the predecessor formula used for dirty marking. Each real run also spot-checked
   200000 random fast transitions against the literal formula.
2. **Chain enumeration against an independent DFS.** The main enumeration uses bitmasks. The second
   one is a DFS over strictly increasing (α,γ) pairs, with the class computed by big integers and a
   brute-force inverse of Q mod P. They agree on the total, which is Σ_k C(s,k)C(H,k) in every case,
   and on the per-class counts and hmin. This held for the 6 tiny and 4 real parameter sets; the
   (7,2) parameters give 352716 chains. Every chain value also satisfies
   Q^h·v ≡ Σ B^{α_i} Q^{h−γ_i} (mod M').
3. **Whole fast pipeline against a naive implementation.** The naive version computes kept chains
   from the DFS. It gets transitions from big integers with random high digits, iterates W
   Jacobi-style with plain Vec<bool> and natural indexing, and reads V from the file bytes through
   the spec's layout formula. The comparison ran for 100 combinations of (parameters, V-mode,
   layout T and N) and covered:
   - Full W membership, with both W strategies (dirty propagation and full passes only).
   - Every d(x), GNUM, the bad count and the argmax.
   - V-modes: V ≡ 0, random V, V with NaN/Inf/2.5e5 entries, and V at exact half-ulps of 2^-20 to
     test rounding half away from zero.

   With V ≡ 0, every d(x) is a multiple of 2^20 and GNUM/2^20 = max_x Σ_u min h, as the spec
   expects. The instances included the real (B,Q,s,H,SLACK) with small D:
   (4,3,2,D=5,18,12) has |W| = 682 of 704 covered states, so removal really happens.
   (2,9,1,10,12,7), (3,5,1,7,12,7) and (2,7,5,9,6,3) were also tested. A grid search added
   parameter sets where 0 < |W| < #covered.

## Implementation notes

- I store W, Vi and the bad flags at the internal index (x mod B^(D−s))·P + ⌊x/B^(D−s)⌋, which is a
  bijection. For a fixed (x, chain), the P successors over u differ only in their top s digits and
  satisfy top(u) = (top(0) + u·Q^h) mod P. `next(u=0)` is computed literally, including the
  "r divisible by P" assertion, and the other u follow from that identity. Self-tests 1 and 3 check
  this against the literal and big-integer formulas.
- **Greatest fixed point.** W is updated in place. A state is removed only if it fails conditions
  (i) or (ii) against the current W, which always contains the greatest fixed point, so no state of
  the greatest fixed point is ever removed. Once a dirty pass removes nothing, a full pass over all
  of W runs, and the iteration stops only when such a full pass removes nothing. The result is
  therefore exactly the greatest fixed point. Dirty passes recheck only predecessors of removed
  states: Q^{-1}y, plus exactly one predecessor per kept chain. This shortcut is used only when there
  are at most 4096 distinct kept chains; otherwise only full passes run, as for (7,2).

## Spec ambiguities and how I resolved them

1. **Non-finite V.** For a NaN or Inf entry I set Vi = 0 and count the state as bad if it is in W;
   d is still computed. A finite |V| ≥ 1e5 is rounded normally and also counted as bad. This made no
   difference: every run has bad = 0.
2. **Duplicate chains.** Different (α,γ) chains can give the same (v,h). I dedupe them per class
   because this cannot change any min or existence test; both counts are shown in the table. Only
   (7,2) has duplicates (70701 kept, 69131 distinct).
3. **"argmax (any one)".** I report the smallest x that attains the maximum.
4. **Scope of "bad".** I count only x ∈ W, as the spec says. The successors used in d(x) are in W,
   so they are covered by the same check.
5. **Decimal display of g.** I truncate to 15 digits. The exact rational is the authoritative value.
6. **(4,3) SHA.** The spec gives only the SHA-256 of the `.xz`. I verified that and also report the
   computed SHA-256 of the uncompressed table.
7. **(7,2) layout.** The spec does not document it. As instructed, I tried natural first: it fails
   (g ≈ 10.39 > λ). Transposed passes. Both are reported above.
8. **The Q^a vs B^(s·b) booleans.** I report them exactly as specified, without interpreting them.
