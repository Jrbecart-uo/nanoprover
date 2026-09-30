// Sparse version of exactset.c: live candidates are a sorted, deduplicated list of (e,k) pairs.
// Same exact transitions (validated against big-integer 2-adic arithmetic, check_ek.py: 60000 steps, 0 errors).
// Reports the front (min excess e) statistics; optional cap on the number of live states (drop highest e first).
// usage: exactsp R rho_num rho_den D L seed [CAP]
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
typedef long long i64; typedef unsigned long long u64;
typedef struct { int e; i64 k; } St;
static int cmp(const void *a, const void *b) { const St *x = a, *y = b; if (x->e != y->e) return x->e - y->e; return (x->k > y->k) - (x->k < y->k); }
static u64 s0, s1;
static u64 rnd(void) { u64 x = s0, y = s1; s0 = y; x ^= x << 23; s1 = x ^ y ^ (x >> 17) ^ (y >> 26); return s1 + y; }
int main(int argc, char **argv) {
  i64 R = atoll(argv[1]); i64 rn = atoll(argv[2]), rd = atoll(argv[3]); int D = atoi(argv[4]); long L = atol(argv[5]);
  u64 seed = strtoull(argv[6], 0, 10); long CAP = argc > 7 ? atol(argv[7]) : 50000000L;
  s0 = seed * 0x9E3779B97F4A7C15ULL + 3; s1 = seed ^ 0xD1B54A32D192ED03ULL; for (int i = 0; i < 10; i++) rnd();
  i64 Rp[64]; Rp[0] = 1; for (int i = 1; i < 30; i++) Rp[i] = Rp[i - 1] * R;
  long cap = 1 << 20; St *A = malloc(sizeof(St) * cap), *B = malloc(sizeof(St) * cap * 8L); long nA = 1, bcap = cap * 8L;
  A[0].e = 0; A[0].k = 0;
  double sumf = 0; long nf = 0, c0 = 0, c1 = 0; long hist[64] = {0}; long maxlive = 0; i64 maxabsk[64] = {0};
  for (long t = 0; t < L; t++) {
    int r = (int)(rnd() & 1); int lam = (int)(((t + 1) * rn) / rd - (t * rn) / rd);
    long nB = 0;
    for (long i = 0; i < nA; i++) {
      int e = A[i].e; i64 k = A[i].k;
      if (nB + D + 4 >= bcap) { bcap *= 2; B = realloc(B, sizeof(St) * bcap); }
      if (((r + k) & 1) == 0) {
        int e2 = e - lam; i64 k2;
        if (e2 < 0) { e2 = 0; k2 = (r + R * k) / 2; } else k2 = (Rp[e2] * r + k) / 2;
        B[nB].e = e2; B[nB].k = k2; nB++;
      } else for (int d = 1; ; d++) {
        int e2 = e + d - lam; if (e2 > D) break; if (e2 < 0) continue;
        B[nB].e = e2; B[nB].k = (Rp[e2] * r + Rp[d] * k - 1) / 2; nB++;
      }
    }
    qsort(B, nB, sizeof(St), cmp);
    long m = 0; for (long i = 0; i < nB; i++) if (m == 0 || B[i].e != B[m - 1].e || B[i].k != B[m - 1].k) B[m++] = B[i];
    if (m > CAP) m = CAP;                       // sorted by e: drops the highest-excess states first
    { static int prune = -2; if (prune == -2) prune = getenv("PRUNE") ? atoi(getenv("PRUNE")) : -1;
      if (prune >= 0 && m > 0) { int f = B[0].e; long mm = 0; while (mm < m && B[mm].e <= f + prune) mm++; m = mm; } }
    if (m == 0) { printf("EXTINCT at t=%ld\n", t); break; }
    if (m > cap) { cap = m * 2; A = realloc(A, sizeof(St) * cap); }
    memcpy(A, B, sizeof(St) * m); nA = m;
    if (nA > maxlive) maxlive = nA;
    for (long i = 0; i < nA; i++) { i64 a = A[i].k < 0 ? -A[i].k : A[i].k; if (a > maxabsk[A[i].e]) maxabsk[A[i].e] = a; }
    int front = A[0].e;
    if (t % 250 == 0 || t == L - 1) {
      long atf = 0; for (long i = 0; i < nA && A[i].e == front; i++) atf++;
      long lev[64] = {0}; for (long i = 0; i < nA; i++) lev[A[i].e]++;
      printf("  t=%6ld front=%d live=%ld  per-level:", t, front, nA); for (int e = 0; e <= D && e < 8; e++) printf(" %ld", lev[e]); printf("\n"); fflush(stdout);
    }
    if (t > L / 5) { sumf += front; nf++; if (front == 0) c0++; if (front <= 1) c1++; hist[front]++; }
  }
  double mu = log(2) / log((double)R);
  printf("R=%lld rho=%lld/%lld (rho/mu=%.4f) D=%d L=%ld seed=%llu: mean front=%.3f P(front=0)=%.3f P(front<=1)=%.3f final live=%ld max live=%ld\n",
         R, rn, rd, (double)rn / rd / mu, D, L, seed, nf ? sumf / nf : -1.0, nf ? (double)c0 / nf : 0, nf ? (double)c1 / nf : 0, nA, maxlive);
  printf("  front hist:"); for (int e = 0; e <= D; e++) printf(" %d:%ld", e, hist[e]);
  printf("\n  max|k| per e:"); for (int e = 0; e <= D; e++) printf(" %d:%lld", e, maxabsk[e]); printf("\n");
  return 0;
}
