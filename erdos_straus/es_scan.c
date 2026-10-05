// es_scan: for primes p ≡ 1 (mod 24), p < N, find all a = 4x - p (a ≡ 3 mod 4, a <= AMAX) for which
// 4/p = 1/x + 1/y + 1/z has a solution with x = (p+a)/4 < y < z, and report the smallest such a plus the
// structure of a witness.  Method: a/(p x) = 1/y + 1/z iff some divisor d of B^2 (B = p x), d < B, has
// d ≡ -B (mod a); then y = (B+d)/a, z = (B+B^2/d)/a.  d = p^e * d', d' | x^2, e in {0,1,2}.
// Output CSV: p, a_min, e, dprime, count_of_working_a(<=AMAX), first_four_working_a
// usage: es_scan N AMAX [records]   (records: print only new maxima of a_min, then a histogram)
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef unsigned long long u64; typedef unsigned __int128 u128;
static int *spf;
static int divs_sq(u64 x, u64 *out) {  // all divisors of x^2
  int n = 1; out[0] = 1;
  while (x > 1) {
    u64 q = spf[x]; int e = 0; while (x % q == 0) { x /= q; e++; }
    int cur = n; u64 pw = 1;
    for (int k = 1; k <= 2 * e; k++) { pw *= q; for (int i = 0; i < cur; i++) out[n++] = out[i] * pw; }
  }
  return n;
}
int main(int argc, char **argv) {
  u64 N = atoll(argv[1]); int AMAX = atoi(argv[2]); int REC = argc > 3; int recmax = 0; static u64 hist[4096];
  u64 XM = (N + AMAX) / 4 + 2;
  spf = malloc(sizeof(int) * (XM + 1));
  for (u64 i = 0; i <= XM; i++) spf[i] = 0;
  for (u64 i = 2; i <= XM; i++) if (!spf[i]) for (u64 j = i; j <= XM; j += i) if (!spf[j]) spf[j] = i;
  char *comp = calloc(N + 1, 1);
  for (u64 i = 2; i * i <= N; i++) if (!comp[i]) for (u64 j = i * i; j <= N; j += i) comp[j] = 1;
  u64 *dv = malloc(sizeof(u64) * 200000);
  if (!REC) printf("p,a_min,e,dprime,nwork,a1,a2,a3,a4\n");
  for (u64 p = 25; p < N; p += 24) {
    if (comp[p]) continue;
    int amin = -1, ebest = -1, nw = 0; u64 dbest = 0; int alist[4] = {0, 0, 0, 0};
    for (int a = 3; a <= AMAX; a += 4) {
      u64 x = (p + a) / 4; u64 B = p * x;  // B < 2^63 for p < 3e9
      int nd = divs_sq(x, dv); int ok = 0; int eok = -1; u64 dok = 0;
      u64 Bm = B % a; u64 target = (a - Bm) % a;  // need d ≡ -B (mod a)
      u64 pe = 1;
      for (int e = 0; e <= 2 && !ok; e++, pe *= p) {
        u64 pem = pe % a;
        for (int i = 0; i < nd && !ok; i++) {
          u128 d = (u128)pe * dv[i];
          if (d >= B) continue;           // need d < B so that y < z
          if ((u64)((u128)pem * (dv[i] % a) % a) == target) { ok = 1; eok = e; dok = dv[i]; }
        }
      }
      if (ok) { if (amin < 0) { amin = a; ebest = eok; dbest = dok; } if (nw < 4) alist[nw] = a; nw++; }
    }
    if (REC) { if (amin < 0) { printf("UNSOLVED p=%llu (a<=%d)\n", p, AMAX); fflush(stdout); }
               else { hist[amin]++; if (amin > recmax) { recmax = amin; printf("record p=%llu a_min=%d nwork=%d\n", p, amin, nw); fflush(stdout); } } }
    else printf("%llu,%d,%d,%llu,%d,%d,%d,%d,%d\n", p, amin, ebest, dbest, nw, alist[0], alist[1], alist[2], alist[3]);
  }
  if (REC) { printf("histogram a_min:"); for (int a = 0; a < 4096; a++) if (hist[a]) printf(" %d:%llu", a, hist[a]); printf("\nDONE\n"); }
  return 0;
}
