// gvik: k-block look-ahead value iteration with dead states and viability (general base).
// Pair (B-adic blocks of s digits, other base Q). M = B^s. State x in Z/M^k = the next k blocks of the
// normalised residual (x mod M = current block c). Fresh u in Z/M = block k+1 (uniform). Chains:
// {(alpha,gamma)} strictly increasing, alpha < s, gamma < H, value v = sum B^alpha Q^{-gamma} mod M^{k+1},
// h = max gamma + 1; a chain is usable at x iff v = c (mod M). Transition (exact):
//   w = ((x - v) mod M^{k+1}) / M,   base = Q^h w mod M^k,   next(u) = low + M^{k-1} ((t0 + Q^h u) mod M)
// with low = base mod M^{k-1}, t0 = base / M^{k-1}. Residues c not covered by any chain are dead.
// Viable set W: largest set of covered states such that for every x in W and every u some chain leads into W.
// Average-cost value iteration on W; prints the bracket [min, max] of (T V - V) and its ratio to
// s*log_Q(B) (the threshold: need max < 1 for a certificate).
// usage: gvik B Q s k H iters SLACK [Vout]
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
typedef struct { u64 v; int h; } Ch;
static Ch *ch; static u64 nch = 0, cap = 0;
static int s, k, H; static u64 B, Q, M, Mk, Mk1, Mkm1;
static u64 Bp[64], uq[64];
static void gen(int a0, int g0, u64 v, int h) {
  if (nch == cap) { cap = cap ? cap * 2 : 1 << 20; ch = realloc(ch, cap * sizeof(Ch)); }
  ch[nch].v = v; ch[nch].h = h; nch++;
  for (int a = a0; a < s; a++) for (int g = g0; g < H; g++) gen(a + 1, g + 1, (v + mulm(uq[g], Bp[a], Mk1)) % Mk1, g + 1);
}
static int cmpc(const void *a, const void *b) {
  u64 x = ((Ch *)a)->v % M, y = ((Ch *)b)->v % M; return x < y ? -1 : x > y;
}
int main(int argc, char **argv) {
  B = atoll(argv[1]); Q = atoll(argv[2]); s = atoi(argv[3]); k = atoi(argv[4]); H = atoi(argv[5]);
  int iters = atoi(argv[6]), SLACK = atoi(argv[7]);
  M = 1; for (int i = 0; i < s; i++) M *= B;
  Mk = 1; for (int i = 0; i < k; i++) Mk *= M;
  Mk1 = Mk * M; Mkm1 = Mk / M;
  if (Mk1 / M != Mk) { fprintf(stderr, "overflow\n"); return 1; }
  Bp[0] = 1; for (int i = 1; i < s; i++) Bp[i] = Bp[i - 1] * B;
  u64 qinv = invmod(Q, Mk1); uq[0] = 1; for (int g = 1; g <= H; g++) uq[g] = mulm(uq[g - 1], qinv, Mk1);
  gen(0, 0, 0, 0);
  qsort(ch, nch, sizeof(Ch), cmpc);
  u64 *cnt = calloc(M + 1, 8); for (u64 i = 0; i < nch; i++) cnt[ch[i].v % M + 1]++;
  for (u64 c = 0; c < M; c++) cnt[c + 1] += cnt[c];
  unsigned char *cov = calloc(M, 1); u64 unc = 0; double flat = 0;
  { u64 w = 0; u64 *nc = calloc(M + 1, 8);
    for (u64 c = 0; c < M; c++) {
      int mh = 1 << 20; for (u64 j = cnt[c]; j < cnt[c + 1]; j++) if (ch[j].h < mh) mh = ch[j].h;
      cov[c] = cnt[c + 1] > cnt[c]; if (!cov[c]) unc++; else flat += mh;
      nc[c] = w; for (u64 j = cnt[c]; j < cnt[c + 1]; j++) if (ch[j].h <= mh + SLACK) ch[w++] = ch[j];
    }
    nc[M] = w; memcpy(cnt, nc, 8 * (M + 1)); }
  flat /= (double)(M - unc);
  u64 *pq = malloc(8 * (H + 2)); pq[0] = 1; for (int i = 1; i <= H + 1; i++) pq[i] = mulm(pq[i - 1], Q, Mk1);
  u64 qim = invmod(Q, M); u64 *iq = malloc(8 * (H + 2)); iq[0] = 1; for (int i = 1; i <= H + 1; i++) iq[i] = mulm(iq[i - 1], qim, M);
  double need = s * log((double)B) / log((double)Q);
  printf("B=%llu Q=%llu s=%d k=%d M=%llu states=%llu H=%d slack=%d chains=%llu uncovered=%llu/%llu flat=%.4f need<%.5f\n",
         (unsigned long long)B, (unsigned long long)Q, s, k, (unsigned long long)M, (unsigned long long)Mk, H, SLACK,
         (unsigned long long)cnt[M], (unsigned long long)unc, (unsigned long long)M, flat, need); fflush(stdout);
  // precompute per (state-independent) chain data? transitions depend on x; computed on the fly.
  unsigned char *alive = malloc(Mk); for (u64 x = 0; x < Mk; x++) alive[x] = cov[x % M];
  for (int pass = 0;; pass++) {
    long removed = 0;
    #pragma omp parallel reduction(+:removed)
    { unsigned char *ok = malloc(M);
      #pragma omp for schedule(dynamic, 64)
      for (u64 x = 0; x < Mk; x++) {
        if (!alive[x]) continue;
        u64 c = x % M; memset(ok, 0, M); u64 nok = 0;
        for (u64 j = cnt[c]; j < cnt[c + 1] && nok < M; j++) {
          int h = ch[j].h; u64 w = ((x + Mk1 - ch[j].v) % Mk1) / M; u64 base = mulm(pq[h] % Mk, w, Mk);
          u64 low = base % Mkm1, t0 = base / Mkm1;
          if (!cov[(k == 1 ? t0 : low) % M]) continue;
          u64 m = pq[h] % M;
          for (u64 u = 0; u < M; u++) { if (ok[u]) continue; u64 nx = low + Mkm1 * ((t0 + mulm(m, u, M)) % M); if (alive[nx]) { ok[u] = 1; nok++; } }
        }
        if (nok < M) { alive[x] = 0; removed++; }
      }
      free(ok); }
    u64 na = 0; for (u64 x = 0; x < Mk; x++) na += alive[x];
    printf("viable pass %d: removed %ld, alive %llu of %llu\n", pass, removed, (unsigned long long)na, (unsigned long long)Mk); fflush(stdout);
    if (!removed) break;
    if (!na) { printf("NO VIABLE STATES\n"); return 0; }
  }
  const float BIG = 1e6f;
  float *V = calloc(Mk, 4), *NV = malloc(Mk * 4);
  for (u64 x = 0; x < Mk; x++) if (!alive[x]) V[x] = BIG;
  float *W = malloc((size_t)(H + 1) * Mk * 4); // W[h][low][y] = V[low + Mkm1 * (Q^h y mod M)]
  if (!W) { fprintf(stderr, "W alloc failed\n"); return 1; }
  for (int it = 0; it < iters; it++) {
    #pragma omp parallel for schedule(static)
    for (u64 low = 0; low < Mkm1; low++) for (int h = 0; h <= H; h++) {
      u64 m = pq[h] % M; float *dst = W + ((size_t)h * Mkm1 + low) * M;
      for (u64 y = 0; y < M; y++) dst[y] = V[low + Mkm1 * mulm(y, m, M)];
    }
    #pragma omp parallel
    { float *best = malloc(M * 4);
      #pragma omp for schedule(dynamic, 64)
      for (u64 x = 0; x < Mk; x++) {
        if (!alive[x]) { NV[x] = BIG; continue; }
        u64 c = x % M;
        for (u64 u = 0; u < M; u++) best[u] = 1e30f;
        for (u64 j = cnt[c]; j < cnt[c + 1]; j++) {
          int h = ch[j].h; u64 w = ((x + Mk1 - ch[j].v) % Mk1) / M; u64 base = mulm(pq[h] % Mk, w, Mk);
          u64 low = base % Mkm1, t0 = base / Mkm1;
          u64 off = mulm(t0, iq[h], M);
          const float *row = W + ((size_t)h * Mkm1 + low) * M; float hh = (float)h;
          u64 split = M - off;
          for (u64 u = 0; u < split; u++) { float v = hh + row[u + off]; if (v < best[u]) best[u] = v; }
          for (u64 u = split; u < M; u++) { float v = hh + row[u + off - M]; if (v < best[u]) best[u] = v; }
        }
        double tot = 0; for (u64 u = 0; u < M; u++) tot += best[u]; NV[x] = (float)(tot / M);
      }
      free(best); }
    double mn = 1e18, mx = -1e18; u64 b0 = 0; while (!alive[b0]) b0++;
    for (u64 x = 0; x < Mk; x++) { if (!alive[x]) continue; double d = NV[x] - V[x]; if (d < mn) mn = d; if (d > mx) mx = d; }
    float base0 = NV[b0]; for (u64 x = 0; x < Mk; x++) V[x] = alive[x] ? NV[x] - base0 : BIG;
    if (argc > 8) { FILE *f = fopen(argv[8], "wb"); fwrite(V, 4, Mk, f); fclose(f); }
    printf("it=%d g in [%.5f, %.5f]  ratio-to-need [%.4f, %.4f]\n", it, mn, mx, mn / need, mx / need); fflush(stdout);
  }
  return 0;
}
