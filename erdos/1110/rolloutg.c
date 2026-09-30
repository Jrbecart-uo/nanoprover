// Online W-digit look-ahead ("rollout") policy in ANY digit base B (other base R), with dead residues.
// Exact tables H_k(z), z in Z/B^k: min total increment to process k digits of the normalized residual z
// (255 = impossible: a nonzero digit that is not a unit mod B can never be matched).  Policy at a nonzero
// digit: choose d >= 1 with R^d z = 1 (mod B) minimizing d + H_{W-1}((R^d z - 1)/B).  Simulates a long random
// target (fresh digits enter at the top, exactly as in the certificate model) and reports cost per digit /
// mu = log_R B.  Also prints, per k, the viable fraction and mean of H_k over viable z (exact).
// usage: rolloutg B R W L seed          (B^(W+8) < 2^64)
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <omp.h>
typedef unsigned long long u64; typedef unsigned __int128 u128;
#define INF 255
int main(int argc, char **argv) {
  u64 B = atoll(argv[1]), R = atoll(argv[2]); int W = atoi(argv[3]); long L = atol(argv[4]); u64 seed = strtoull(argv[5], 0, 10);
  int DMAX = 64;
  unsigned char *prev = calloc(1, 1), *cur = NULL; u64 Pk = 1;
  double mu = log((double)B) / log((double)R);
  for (int k = 1; k <= W - 1; k++) {
    u64 P = Pk * B; cur = malloc(P);
    double sum = 0; long viable = 0;
    #pragma omp parallel for schedule(static, 65536) reduction(+:sum,viable)
    for (u64 z = 0; z < P; z++) {
      u64 dg = z % B; int h;
      if (dg == 0) h = prev[z / B];
      else {
        int best = INF; u64 rd = 1;
        for (int d = 1; d <= DMAX && d < best; d++) {
          rd = (rd * R) % P;
          u64 t = (u64)(((u128)rd * z) % P);
          if (t % B != 1) continue;
          int c = prev[(t - 1) / B]; if (c == INF) continue;
          c += d; if (c < best) best = c;
        }
        h = best;
      }
      cur[z] = (unsigned char)(h > INF ? INF : h);
      if (h < INF) { sum += h; viable++; }
    }
    if (k >= W - 4) printf("  k=%2d viable=%.5f  E[H_k|viable]=%.4f  per-digit=%.4f  /mu=%.4f\n", k, (double)viable / P, sum / viable, sum / viable / k, sum / viable / k / mu);
    fflush(stdout);
    free(prev); prev = cur; Pk = P;
  }
  unsigned char *H = prev; u64 PW = Pk;                 // H_{W-1}
  int Wz = W + 8; u64 M = 1; for (int i = 0; i < Wz; i++) M *= B; u64 topw = M / B;
  u64 RP[65]; RP[0] = 1; for (int d = 1; d <= DMAX; d++) RP[d] = (u64)(((u128)RP[d - 1] * R) % M);
  u64 s0 = seed * 0x9E3779B97F4A7C15ULL + 99, s1 = seed ^ 0xD1B54A32D192ED03ULL;
  #define RND() ({ u64 x_ = s0, y_ = s1; s0 = y_; x_ ^= x_ << 23; s1 = x_ ^ y_ ^ (x_ >> 17) ^ (y_ >> 26); s1 + y_; })
  u64 z = 0; for (int i = 0; i < Wz; i++) z = z * B + RND() % B;
  long cost = 0, deaths = 0, terms = 0, steps = 0;
  for (long b = 0; b < L; b++) {
    u64 dg = z % B;
    if (dg == 0) z /= B;
    else {
      int best = 1 << 30, bd = -1;
      for (int d = 1; d <= DMAX && d < best; d++) {
        u64 t = (u64)(((u128)RP[d] * z) % M);
        if (t % B != 1) continue;
        u64 nz = (t - 1) / B; int c = H[nz % PW]; if (c == INF) continue;
        c += d; if (c < best) { best = c; bd = d; }
      }
      if (bd < 0) {                                  // dead end: restart on a fresh random residual
        deaths++; z = 0; for (int i = 0; i < Wz; i++) z = z * B + RND() % B; continue;
      }
      u64 t = (u64)(((u128)RP[bd] * z) % M); z = (t - 1) / B; cost += bd; terms++;
    }
    z += topw * (RND() % B); steps++;
  }
  printf("B=%llu R=%llu W=%d L=%ld: rate=%.5f per digit  mu=%.5f  ratio=%.4f  terms/digit=%.4f  deaths=%ld\n",
         B, R, W, L, (double)cost / steps, mu, (double)cost / steps / mu, (double)terms / steps, deaths);
  return 0;
}
