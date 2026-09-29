// EXACT minimal cost of a staircase matching a B-adic target y mod B^L (B = 2 or 3, R = other base),
// by IDA* with an admissible look-ahead bound:  h_k(z) = exact min cost to match the next k digits of the
// normalized residual z (table for all k <= W, computed by DP).  Complements nbrw.c: finite-L exact minima
// approach the quenched rate from BELOW (log-correction), beams from ABOVE.
// Normalized residual z = R^G * (y - partial)/B^b.  Digit 0 -> z/B.  Nonzero digit -> a term with increment
// d >= 1 (first term: gamma = d-1), needs R^{-d}... i.e. R^d z = 1 mod B, then z' = (R^d z - 1)/B.
// usage: exactmin B R L W trials seed          (L <= 124 bits for B=2, L <= 78 trits for B=3)
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
typedef unsigned __int128 u128; typedef unsigned long long u64;
static int B, R, L, W, K = 40;
static u128 MODL;                 // B^L (B=3) ; for B=2 we use natural 2^128 wrap
static unsigned char *H[64];      // H[k][z] for z in [0, B^k)
static u64 PK[64];                // B^k
static u128 RP[64];               // R^d mod 2^128 (B=2) or mod MODL (B=3)
static long nodes; static int found;

static inline u128 mulmod(u128 a, u128 b) {   // for B=3: a*b mod MODL with MODL < 2^127; use double-and-add
  if (B == 2) return a * b;
  u128 r = 0; a %= MODL; b %= MODL;
  while (b) { if (b & 1) { r += a; if (r >= MODL) r -= MODL; } a <<= 1; if (a >= MODL) a -= MODL; b >>= 1; }
  return r;
}
static inline int digit(u128 z) { return (int)(z % B); }

static void build_tables(void) {
  PK[0] = 1; for (int k = 1; k <= W; k++) PK[k] = PK[k - 1] * B;
  H[0] = calloc(1, 1);
  for (int k = 1; k <= W; k++) {
    H[k] = malloc(PK[k]);
    for (u64 z = 0; z < PK[k]; z++) {
      int dg = (int)(z % B);
      if (dg == 0) { H[k][z] = H[k - 1][(z / B) % PK[k - 1]]; continue; }
      int best = 255; u64 rd = 1;                       // rd = R^d mod B^k
      for (int d = 1; d <= K && d < best; d++) {
        rd = (rd * R) % PK[k];
        u64 t = (u64)(((u128)rd * z) % PK[k]);
        if (t % B != 1) continue;
        u64 nz = ((t + PK[k] - 1) % PK[k]) / B;         // (R^d z - 1)/B mod B^(k-1)
        int c = d + H[k - 1][nz % PK[k - 1]];
        if (c < best) best = c;
      }
      H[k][z] = (unsigned char)best;
    }
  }
}
// lower bound on remaining cost with `rem` digits left
static inline int lb(u128 z, int rem) { int k = rem < W ? rem : W; return H[k][(u64)(z % PK[k])]; }

static void dfs(u128 z, int rem, int g, int bound) {
  nodes++;
  if (found) return;
  while (rem > 0 && digit(z) == 0) { z /= B; rem--; }
  if (rem == 0) { found = 1; return; }
  if (g + lb(z, rem) > bound) return;
  u128 t = (B == 2) ? z : z % MODL;
  for (int d = 1; d <= K && g + d <= bound; d++) {
    t = (B == 2) ? t * (u128)R : (t * (u128)R) % MODL;
    if (digit(t) != 1) continue;
    u128 nz = (B == 2) ? ((t - 1) >> 1) : ((t + MODL - 1) % MODL) / 3;
    if (g + d + lb(nz, rem - 1) > bound) continue;
    dfs(nz, rem - 1, g + d, bound);
    if (found) return;
  }
}

static u64 st[2];
static u64 rnd(void) { u64 x = st[0], y = st[1]; st[0] = y; x ^= x << 23; st[1] = x ^ y ^ (x >> 17) ^ (y >> 26); return st[1] + y; }

int main(int argc, char **argv) {
  if (argc < 7) { fprintf(stderr, "usage: exactmin B R L W trials seed [y_hex]\n"); return 1; }
  B = atoi(argv[1]); R = atoi(argv[2]); L = atoi(argv[3]); W = atoi(argv[4]); int trials = atoi(argv[5]);
  u64 seed = strtoull(argv[6], 0, 10); st[0] = seed * 0x9E3779B97F4A7C15ULL + 7; st[1] = seed ^ 0xD1B54A32D192ED03ULL;
  for (int i = 0; i < 20; i++) rnd();
  if (B == 3) { MODL = 1; for (int i = 0; i < L; i++) MODL *= 3; }
  build_tables();
  RP[0] = 1; for (int d = 1; d < 64; d++) RP[d] = mulmod(RP[d - 1], R);
  u128 Rinv;   // R^{-1} mod 2^128 or mod MODL
  if (B == 2) { u128 x = R; for (int i = 0; i < 8; i++) x *= 2 - (u128)R * x; Rinv = x; }
  else { // extended Euclid mod MODL
    __int128 a = (__int128)MODL, b = R, x0 = 0, x1 = 1;
    while (b) { __int128 q = a / b, t = a - q * b; a = b; b = t; t = x0 - q * x1; x0 = x1; x1 = t; }
    Rinv = (u128)((x0 % (__int128)MODL + (__int128)MODL) % (__int128)MODL);
  }
  double mu = log(B) / log(R); double sum = 0; long tot = 0;
  for (int tr = 0; tr < trials; tr++) {
    u128 y;
    if (argc > 7) { y = 0; for (char *p = argv[7]; *p; p++) { int v = (*p <= '9') ? *p - '0' : (*p | 32) - 'a' + 10; y = y * 16 + v; } }
    else if (B == 2) { y = ((u128)rnd() << 64) | rnd(); if (L < 128) y &= (((u128)1) << L) - 1; }
    else { y = 0; for (int i = 0; i < L; i++) y = y * 3 + rnd() % 3; }
    u128 z = mulmod(Rinv, y);     // G = -1 normalization: first term gamma = d-1
    int bound = lb(z, L) - 1;          // final gamma >= -1 + H_L(z)
    found = 0; nodes = 0;
    for (;; bound++) { dfs(z, L, -1, bound); if (found) break; }
    // result: minimal final gamma = bound
    sum += bound; tot += nodes;
    printf("y=%016llx%016llx min_gamma=%d nodes=%ld\n", (u64)(y >> 64), (u64)y, bound, nodes);
    fflush(stdout);
  }
  printf("B=%d R=%d L=%d W=%d trials=%d  mean min_gamma/L=%.5f  mu=%.5f  ratio=%.4f  avg_nodes=%.0f\n",
         B, R, L, W, trials, sum / trials / L, mu, sum / trials / L / mu, (double)tot / trials);
  return 0;
}
