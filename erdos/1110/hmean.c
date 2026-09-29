// Exact mean minimal encoding cost over ALL targets z in Z/B^k, for k = 1..Kmax.
// H_k(z) = min over staircases matching z mod B^k of the total increment (normalized residual z, first
// increment d >= 1).  Recurrence (min-plus transfer operator):
//   digit 0:  H_k(z) = H_{k-1}(z / B)
//   else:     H_k(z) = min_{d>=1, R^d z = 1 mod B} [ d + H_{k-1}( (R^d z - 1)/B mod B^{k-1} ) ]
// E[H_k] - E[H_{k-1}] converges to the quenched minimal cost rate per digit (from below, BRW log-correction),
// with no boundary bias.  Positive density of {R,B}-representables needs that rate < log_R B.
// Also prints the distribution P(H_k <= mu*k + c) (fraction of k-digit targets encodable within budget).
// usage: hmean B R Kmax
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
#include <omp.h>
typedef unsigned long long u64; typedef unsigned __int128 u128;
int main(int argc, char **argv) {
  int B = atoi(argv[1]), R = atoi(argv[2]), Kmax = atoi(argv[3]);
  double mu = log(B) / log(R);
  unsigned char *prev = calloc(1, 1), *cur = NULL; u64 Pk = 1; double prevmean = 0;
  printf("B=%d R=%d mu=%.5f\n k    E[H_k]      increment  inc/mu   E[H_k]/k   P(H_k<=mu k)  P(H_k<=mu k+2)\n", B, R, mu);
  for (int k = 1; k <= Kmax; k++) {
    u64 P = Pk * B; if (P > (1ULL << 32)) { fprintf(stderr, "P too large\n"); return 1; } cur = malloc(P);
    double sum = 0; long cnt0 = 0, cnt2 = 0; double thr = mu * k;
    #pragma omp parallel for schedule(static, 65536) reduction(+:sum,cnt0,cnt2)
    for (u64 z = 0; z < P; z++) {
      int dg = (int)(z % B), h;
      if (dg == 0) h = prev[z / B];
      else {
        int best = 255; u64 rd = 1;
        for (int d = 1; d < best && d <= 60; d++) {
          rd = (rd * R) % P;
          u64 t = (B == 2) ? ((rd * z) & (P - 1)) : ((rd * z) % P);   // P <= 2^32 so no overflow
          if (t % B != 1) continue;
          int c = d + prev[(t - 1) / B];
          if (c < best) best = c;
        }
        h = best;
      }
      cur[z] = (unsigned char)h; sum += h;
      if (h <= thr) cnt0++;
      if (h <= thr + 2) cnt2++;
    }
    double mean = sum / (double)P;
    printf("%2d  %10.5f  %9.5f  %7.4f  %8.5f   %9.5f   %9.5f\n", k, mean, mean - prevmean, (mean - prevmean) / mu,
           mean / k, (double)cnt0 / P, (double)cnt2 / P);
    fflush(stdout);
    free(prev); prev = cur; Pk = P; prevmean = mean;
  }
  return 0;
}
