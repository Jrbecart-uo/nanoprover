// gvis1: one-digit blocks (s = 1) with a k-digit sliding look-ahead window (general base, dead states).
// Pair (B-adic digits, other base Q). State x in Z/B^k = next k digits of the normalised residual z
// (x mod B = current digit c). Fresh digit u in Z/B (uniform). Per step the chain is either empty
// (h = 0, only if c = 0) or a single term B^0 Q^{-g}, 0 <= g < H, with Q^{-g} = c (mod B); h = g + 1.
// Transition: w = ((x - v) mod B^{k+1}) / B, base = Q^h w mod B^k,
//             next(u) = (base mod B^{k-1}) + B^{k-1} ((base / B^{k-1} + Q^h u) mod B).
// Viable set + average-cost value iteration; threshold per digit: log_Q(B).
// usage: gvis1 B Q k H iters [Vout]
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <omp.h>
typedef uint64_t u64; typedef unsigned __int128 u128;
static u64 mulm(u64 a, u64 b, u64 m) { return (u64)((u128)a * b % m); }
static u64 invmod(u64 a, u64 m) {
  __int128 t = 0, nt = 1, r = m, nr = a % m;
  while (nr) { __int128 q = r / nr, x; x = t - q * nt; t = nt; nt = x; x = r - q * nr; r = nr; nr = x; }
  if (r != 1) { fprintf(stderr, "not invertible\n"); exit(1); }
  if (t < 0) t += m; return (u64)t;
}
int main(int argc, char **argv) {
  u64 B = atoll(argv[1]), Q = atoll(argv[2]); int k = atoi(argv[3]), H = atoi(argv[4]), iters = atoi(argv[5]);
  u64 Mk = 1; for (int i = 0; i < k; i++) Mk *= B; u64 Mk1 = Mk * B, Mkm1 = Mk / B;
  // chains: index 0 = empty (h=0, v=0); index 1+g = term Q^{-g}
  int nc = H + 1; u64 *cv = malloc(8 * nc); int *chh = malloc(4 * nc);
  u64 qi = invmod(Q, Mk1); cv[0] = 0; chh[0] = 0; u64 t = 1;
  for (int g = 0; g < H; g++) { cv[1 + g] = t; chh[1 + g] = g + 1; t = mulm(t, qi, Mk1); }
  // per residue c: list of usable chains
  int *lst = malloc(4 * nc * B), *ln = calloc(B, 4);
  for (int j = 0; j < nc; j++) { u64 c = cv[j] % B; lst[c * nc + ln[c]++] = j; }
  unsigned char *cov = calloc(B, 1); for (u64 c = 0; c < B; c++) cov[c] = ln[c] > 0;
  u64 *pq = malloc(8 * (H + 2)); pq[0] = 1; for (int i = 1; i <= H + 1; i++) pq[i] = mulm(pq[i - 1], Q, Mk1);
  double need = log((double)B) / log((double)Q);
  printf("B=%llu Q=%llu k=%d states=%llu H=%d need<%.5f per digit; covered digits:", (unsigned long long)B,
         (unsigned long long)Q, k, (unsigned long long)Mk, H, need);
  for (u64 c = 0; c < B; c++) printf(" %llu:%d", (unsigned long long)c, ln[c]); printf("\n"); fflush(stdout);
  unsigned char *alive = malloc(Mk); for (u64 x = 0; x < Mk; x++) alive[x] = cov[x % B];
  for (int pass = 0;; pass++) {
    long removed = 0;
    #pragma omp parallel for schedule(dynamic, 4096) reduction(+:removed)
    for (u64 x = 0; x < Mk; x++) {
      if (!alive[x]) continue;
      u64 c = x % B; int okall = 1;
      for (u64 u = 0; u < B && okall; u++) {
        int ok = 0;
        for (int i = 0; i < ln[c] && !ok; i++) { int j = lst[c * nc + i]; int h = chh[j];
          u64 w = ((x + Mk1 - cv[j]) % Mk1) / B; u64 base = mulm(pq[h] % Mk, w, Mk);
          u64 nx = base % Mkm1 + Mkm1 * ((base / Mkm1 + mulm(pq[h] % B, u, B)) % B);
          if (alive[nx]) ok = 1; }
        if (!ok) okall = 0;
      }
      if (!okall) { alive[x] = 0; removed++; }
    }
    u64 na = 0; for (u64 x = 0; x < Mk; x++) na += alive[x];
    printf("viable pass %d: removed %ld, alive %llu of %llu\n", pass, removed, (unsigned long long)na, (unsigned long long)Mk); fflush(stdout);
    if (!na) { printf("NO VIABLE STATES\n"); return 0; }
    if (!removed) break;
  }
  const float BIG = 1e6f;
  float *V = calloc(Mk, 4), *NV = malloc(Mk * 4);
  for (u64 x = 0; x < Mk; x++) if (!alive[x]) V[x] = BIG;
  for (int it = 0; it < iters; it++) {
    #pragma omp parallel for schedule(dynamic, 4096)
    for (u64 x = 0; x < Mk; x++) {
      if (!alive[x]) { NV[x] = BIG; continue; }
      u64 c = x % B; double tot = 0;
      for (u64 u = 0; u < B; u++) {
        float best = 1e30f;
        for (int i = 0; i < ln[c]; i++) { int j = lst[c * nc + i]; int h = chh[j];
          u64 w = ((x + Mk1 - cv[j]) % Mk1) / B; u64 base = mulm(pq[h] % Mk, w, Mk);
          u64 nx = base % Mkm1 + Mkm1 * ((base / Mkm1 + mulm(pq[h] % B, u, B)) % B);
          float v = (float)h + V[nx]; if (v < best) best = v; }
        tot += best;
      }
      NV[x] = (float)(tot / B);
    }
    double mn = 1e18, mx = -1e18; u64 b0 = 0; while (!alive[b0]) b0++;
    for (u64 x = 0; x < Mk; x++) { if (!alive[x]) continue; double d = NV[x] - V[x]; if (d < mn) mn = d; if (d > mx) mx = d; }
    float base0 = NV[b0]; for (u64 x = 0; x < Mk; x++) V[x] = alive[x] ? NV[x] - base0 : BIG;
    if (argc > 6) { FILE *f = fopen(argv[6], "wb"); fwrite(V, 4, Mk, f); fclose(f); }
    printf("it=%d g in [%.5f, %.5f]  ratio-to-need [%.4f, %.4f]\n", it, mn, mx, mn / need, mx / need); fflush(stdout);
  }
  return 0;
}
