// EXACT offline reachable set for the (R,2) encoding, relative to a reference line of rate rho < mu.
// Reference: z_ref (the uniformly random target), level G_ref(t) = floor(rho*t); its bit r_t = z_ref mod 2
// is iid uniform.  Every candidate staircase p has normalized residual  z_p = R^{e_p} z_ref + k_p  with
// e_p = G_p - G_ref(t) >= 0 (excess; candidates below the line are padded) and k_p an INTEGER (normalized
// difference of partial sums; bounded by geometric decay because rho < mu).  Transitions (lambda = G_ref step):
//   (r + k) even (no term):  e' = e - lambda; if e' < 0 {pad: e' = 0, k' = (r + R k)/2} else k' = (R^e' r + k)/2
//   (r + k) odd  (term, increment d >= 1):  e' = e + d - lambda,  k' = (R^e' r + R^d k - 1)/2
// Equal (e,k) <=> identical candidates, so the set is exact (no carries lost).  A bounded front (min e) means
// typical targets are encodable at rate rho; the set is a finite-type branching process in a random environment.
// usage: exactset R rho_num rho_den D L seed [KMAX]
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
typedef long long i64; typedef unsigned long long u64;
static u64 s0, s1;
static u64 rnd(void) { u64 x = s0, y = s1; s0 = y; x ^= x << 23; s1 = x ^ y ^ (x >> 17) ^ (y >> 26); return s1 + y; }
int main(int argc, char **argv) {
  i64 R = atoll(argv[1]); i64 rn = atoll(argv[2]), rd = atoll(argv[3]); int D = atoi(argv[4]); long L = atol(argv[5]);
  u64 seed = strtoull(argv[6], 0, 10); i64 KMAX = argc > 7 ? atoll(argv[7]) : 2000;
  s0 = seed * 0x9E3779B97F4A7C15ULL + 3; s1 = seed ^ 0xD1B54A32D192ED03ULL; for (int i = 0; i < 10; i++) rnd();
  i64 Rp[64]; Rp[0] = 1; for (int i = 1; i < 40; i++) Rp[i] = Rp[i - 1] * R;
  // K bound per excess level: K_e = KMAX * R^e  (capped)
  i64 Ke[64]; size_t off[65]; off[0] = 0;
  for (int e = 0; e <= D; e++) { Ke[e] = KMAX * Rp[e]; if (Ke[e] > 40000000LL) Ke[e] = 40000000LL; off[e + 1] = off[e] + (size_t)(2 * Ke[e] + 1); }
  size_t NS = off[D + 1];
  unsigned char *A = calloc(NS, 1), *B = calloc(NS, 1);
  #define IDX(e, k) (off[(e)] + (size_t)((k) + Ke[(e)]))
  A[IDX(0, 0)] = 1;
  long overflow = 0; double sumfront = 0; long cnt0 = 0, cntle1 = 0; long n0 = 0; int front = 0; long live = 1;
  long hist[64] = {0};
  for (long t = 0; t < L; t++) {
    int r = (int)(rnd() & 1);
    int lam = (int)(((t + 1) * rn) / rd - (t * rn) / rd);
    memset(B, 0, NS);
    for (int e = 0; e <= D; e++) {
      i64 K = Ke[e];
      unsigned char *row = A + off[e];
      for (i64 j = 0; j <= 2 * K; j++) {
        if (!row[j]) continue;
        i64 k = j - K;
        if (((r + k) & 1) == 0) {
          int e2 = e - lam; i64 k2;
          if (e2 < 0) { e2 = 0; k2 = (r + R * k) / 2; }
          else k2 = (Rp[e2] * r + k) / 2;
          if (k2 < -Ke[e2] || k2 > Ke[e2]) { overflow++; continue; }
          B[IDX(e2, k2)] = 1;
        } else {
          for (int d = 1; ; d++) {
            int e2 = e + d - lam; if (e2 > D) break; if (e2 < 0) continue;
            i64 k2 = (Rp[e2] * r + Rp[d] * k - 1) / 2;
            if (k2 < -Ke[e2] || k2 > Ke[e2]) { overflow++; continue; }
            B[IDX(e2, k2)] = 1;
          }
        }
      }
    }
    unsigned char *tmp = A; A = B; B = tmp;
    front = -1; live = 0;
    for (int e = 0; e <= D; e++) { unsigned char *row = A + off[e]; long c = 0; for (i64 j = 0; j <= 2 * Ke[e]; j++) c += row[j]; if (c && front < 0) front = e; live += c; }
    if (front < 0) { printf("EXTINCT at t=%ld (all candidates exceeded excess cap D=%d)\n", t, D); break; }
    if (t > L / 10) { sumfront += front; n0++; if (front == 0) cnt0++; if (front <= 1) cntle1++; hist[front]++; }
  }
  double mu = log(2) / log((double)R);
  printf("R=%lld rho=%lld/%lld=%.5f (mu=%.5f, rho/mu=%.4f) D=%d L=%ld: mean front=%.3f  P(front=0)=%.3f  P(front<=1)=%.3f  final live=%ld  overflow=%ld  states=%zu\n",
         R, rn, rd, (double)rn / rd, mu, (double)rn / rd / mu, D, L, n0 ? sumfront / n0 : -1.0, n0 ? (double)cnt0 / n0 : 0, n0 ? (double)cntle1 / n0 : 0, live, overflow, NS);
  printf("front histogram:"); for (int e = 0; e <= D; e++) printf(" %d:%ld", e, hist[e]); printf("\n");
  return 0;
}
