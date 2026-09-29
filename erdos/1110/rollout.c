// Online W-digit look-ahead ("rollout") policy for the B-adic encoding, B = 2 only.
// At each odd residual z, choose d minimizing  d + H_{W-1}( (R^d z - 1)/2 mod 2^{W-1} )  where H_k is the exact
// min-cost table (as in hmean.c).  Simulates the policy on a long random target and reports cost per digit.
// This measures how quickly finite-look-ahead (online) encodings approach the offline optimum.
// usage: rollout R W L seed
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <omp.h>
typedef unsigned long long u64; typedef unsigned __int128 u128;
int main(int argc, char **argv) {
  int R = atoi(argv[1]), W = atoi(argv[2]); long L = atol(argv[3]); u64 seed = strtoull(argv[4], 0, 10);
  int Wm = W - 1; unsigned char *prev = calloc(1, 1), *cur = NULL; u64 Pk = 1;
  for (int k = 1; k <= Wm; k++) {             // build H_k up to k = W-1, keep only the last
    u64 P = Pk * 2; cur = malloc(P);
    #pragma omp parallel for schedule(static, 65536)
    for (u64 z = 0; z < P; z++) {
      if (!(z & 1)) { cur[z] = prev[z >> 1]; continue; }
      int best = 255; u64 rd = 1;
      for (int d = 1; d < best && d <= 60; d++) { rd = (rd * R) & (P - 1); u64 t = (rd * z) & (P - 1); int c = d + prev[(t - 1) >> 1]; if (c < best) best = c; }
      cur[z] = (unsigned char)best;
    }
    free(prev); prev = cur; Pk = P;
  }
  unsigned char *H = prev; u64 mask = Pk - 1;
  // target: stream of random bits; keep the normalized residual z as a sliding big window of 128 bits:
  // z has infinite precision in principle; we keep 128 bits and refill the top bit from the random stream.
  // (Refill is exact: z = R^G (y - partial)/2^b; its bit 127 after a shift is determined by y's fresh bit XOR
  //  the partial-sum contribution, which we track by keeping z exactly mod 2^(128) and injecting the fresh
  //  y-bit multiplied by R^G at position 127.)
  u64 s0 = seed * 0x9E3779B97F4A7C15ULL + 99, s1 = seed ^ 0xD1B54A32D192ED03ULL;
  #define RND() ({ u64 x_ = s0, y_ = s1; s0 = y_; x_ ^= x_ << 23; s1 = x_ ^ y_ ^ (x_ >> 17) ^ (y_ >> 26); s1 + y_; })
  u128 z = ((u128)RND() << 64) | RND();       // initial normalized residual (G = 0 reference; uniform)
  long cost = 0; long terms = 0;
  // RG = R^G mod 2 (always odd) -> injecting fresh bit f at position 127 changes bit 127 by f (since R^G odd):
  // (y + f*2^(b+127)) * R^G / 2^b  mod 2^128 = z + f*R^G*2^127 = z + f*2^127 (mod 2^128).  So fresh bits are
  // simply XORed into bit 127, independent of G.  After each shift we set bit 127 := fresh ^ (carry-free top bit).
  for (long b = 0; b < L; b++) {
    if (z & 1) {
      int best = 1 << 30, bd = 1; u128 t = z;
      for (int d = 1; d <= 60 && d < best; d++) {
        t *= (u128)R; u128 nz = (t - 1) >> 1;
        int c = d + H[(u64)nz & mask];
        if (c < best) { best = c; bd = d; }
      }
      u128 t2 = z; for (int d = 0; d < bd; d++) t2 *= (u128)R;
      z = (t2 - 1) >> 1; cost += bd; terms++;
    } else z >>= 1;
    // top bit (127) after shift is unknown -> fresh: XOR a random bit into it
    if (RND() & 1) z ^= ((u128)1) << 127;
  }
  double mu = log(2) / log(R);
  printf("R=%d W=%d L=%ld seed=%llu  rate=%.5f  mu=%.5f  ratio=%.4f  terms/bit=%.4f\n", R, W, L, seed, (double)cost / L, mu, cost / (double)L / mu, terms / (double)L);
  return 0;
}
