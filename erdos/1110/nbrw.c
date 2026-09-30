// N-BRW (beam) estimate of the QUENCHED minimal cost rate of the digit encoding for Erdős #1110.
// Digit base B (2 or 3), other base R, R coprime to B.  Target y = random L-digit B-adic integer.
// A staircase matching y: terms B^b R^{-gamma}, b and gamma strictly increasing, sum == y (mod B^L).
// Process digit b = 0..L-1 with residual q = (y - partial)/B^b: digit q mod B must be 0 (no term) or
// equal R^{-gamma} mod B for the new term (gamma = G + d, d >= 1).  Cost = final gamma.
// Beam: keep the N particles with the smallest G (random tie-break).  Velocity v_N = slope of min G.
// Brunet-Derrida: v_N ~ v_inf + a/(ln N)^2.  Positive density needs v_inf < log_R B.
// usage: nbrw B R L N K seed        (K = max increment tried)
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
typedef unsigned long long u64; typedef unsigned __int128 u128;
static int NL, Bb, Rr; static u64 *T, *PB;   // T[g] = R^{-g} mod M;  PB = M = B^Lmax (base 3) or unused
static u64 st[2];
static u64 rnd(void) { u64 x = st[0], y = st[1]; st[0] = y; x ^= x << 23; st[1] = x ^ y ^ (x >> 17) ^ (y >> 26); return st[1] + y; }

// exact division of r (NL limbs, value mod 2^(64NL)) by odd small p, 2-adically: returns r/p mod 2^(64NL)
static void div2adic(u64 *out, const u64 *in, u64 p) {
  u64 inv = p; for (int i = 0; i < 6; i++) inv *= 2 - p * inv;   // p^{-1} mod 2^64
  u64 *r = malloc(8 * NL); memcpy(r, in, 8 * NL);
  for (int i = 0; i < NL; i++) {
    u64 x = r[i] * inv; out[i] = x;
    // r -= p*x << 64i
    u128 prod = (u128)p * x; u64 lo = (u64)prod, hi = (u64)(prod >> 64);
    u64 bor = 0; int j = i;
    { u128 t = (u128)r[j] - lo; r[j] = (u64)t; bor = (t >> 64) ? 1 : 0; j++; }
    if (j < NL) { u128 t = (u128)r[j] - hi - bor; r[j] = (u64)t; bor = (t >> 64) ? 1 : 0; j++; }
    while (bor && j < NL) { u128 t = (u128)r[j] - bor; r[j] = (u64)t; bor = (t >> 64) ? 1 : 0; j++; }
  }
  free(r);
}
static void mulsmall(u64 *x, u64 m) { u64 c = 0; for (int i = 0; i < NL; i++) { u128 t = (u128)x[i] * m + c; x[i] = (u64)t; c = (u64)(t >> 64); } }
static int geq(const u64 *a, const u64 *b) { for (int i = NL - 1; i >= 0; i--) if (a[i] != b[i]) return a[i] > b[i]; return 1; }
static void subin(u64 *a, const u64 *b) { u64 bor = 0; for (int i = 0; i < NL; i++) { u128 t = (u128)a[i] - b[i] - bor; a[i] = (u64)t; bor = (t >> 64) ? 1 : 0; } }
static void addin(u64 *a, const u64 *b) { u64 c = 0; for (int i = 0; i < NL; i++) { u128 t = (u128)a[i] + b[i] + c; a[i] = (u64)t; c = (u64)(t >> 64); } }
static u64 modB(const u64 *a) { u64 w = (u64)(((u128)1 << 64) % (u128)Bb), r = 0; for (int i = NL - 1; i >= 0; i--) r = (u64)(((u128)r * w + a[i] % Bb) % Bb); return r; }
static void divB(u64 *a) { u128 rem = 0; for (int i = NL - 1; i >= 0; i--) { u128 cur = (rem << 64) | a[i]; a[i] = (u64)(cur / Bb); rem = cur % Bb; } }
static void shr1(u64 *a) { for (int i = 0; i < NL - 1; i++) a[i] = (a[i] >> 1) | (a[i + 1] << 63); a[NL - 1] >>= 1; }

typedef struct { int g; int par; int d; } Cand;

int main(int argc, char **argv) {
  if (argc < 7) { fprintf(stderr, "usage: nbrw B R L N K seed\n"); return 1; }
  Bb = atoi(argv[1]); Rr = atoi(argv[2]); int L = atoi(argv[3]); long N = atol(argv[4]); int K = atoi(argv[5]);
  u64 seed = strtoull(argv[6], 0, 10); st[0] = seed * 0x9E3779B97F4A7C15ULL + 12345; st[1] = seed ^ 0xD1B54A32D192ED03ULL;
  for (int i = 0; i < 20; i++) rnd();
  double bits = (Bb == 2) ? L : (L + 2) * log2((double)Bb);
  NL = (int)(bits / 64) + 2;
  int Gmax = (int)(L * (2.0 * log(Bb) / log(Rr) + 0.5)) + K + 16;   // cost rate is ~mu = log_R B per digit
  T = calloc((size_t)(Gmax + 1) * NL, 8);
  u64 *M3 = NULL;
  if (Bb == 2) {
    T[0] = 1;
    for (int g = 1; g <= Gmax; g++) div2adic(T + (size_t)g * NL, T + (size_t)(g - 1) * NL, Rr);
  } else {
    // work mod M = 3^Lm with Lm = L+2 (fits: NL limbs); T[g] = R^{-g} mod M via R^{-1} = (M*k+1)/R
    M3 = calloc(NL, 8); M3[0] = 1; for (int i = 0; i < L + 2; i++) mulsmall(M3, Bb);
    // R^{-1} mod M: find k in [0,R) with M*k+1 = 0 mod R
    u64 Mmod = 0; { u128 rem = 0; for (int i = NL - 1; i >= 0; i--) { rem = ((rem << 64) | M3[i]) % Rr; } Mmod = (u64)rem; }
    int k = 0; while ((Mmod * k + 1) % Rr) k++;
    u64 *inv = calloc(NL, 8); memcpy(inv, M3, 8 * NL); mulsmall(inv, k); { u64 one[1]; (void)one; u64 c = 1; for (int i = 0; i < NL && c; i++) { u128 t = (u128)inv[i] + c; inv[i] = (u64)t; c = (u64)(t >> 64); } }
    { u128 rem = 0; for (int i = NL - 1; i >= 0; i--) { u128 cur = (rem << 64) | inv[i]; inv[i] = (u64)(cur / Rr); rem = cur % Rr; } if (rem) { fprintf(stderr, "inv fail\n"); return 1; } }
    T[0] = 1;
    // T[g] = T[g-1]*inv mod M  (schoolbook multiply then reduce by repeated subtraction is too slow; use: T[g] = T[g-1]/R mod M
    // computed as (T[g-1] + M*j)/R with j chosen so divisible)
    for (int g = 1; g <= Gmax; g++) {
      u64 *prev = T + (size_t)(g - 1) * NL, *cur = T + (size_t)g * NL;
      u64 pm = 0; { u128 rem = 0; for (int i = NL - 1; i >= 0; i--) rem = ((rem << 64) | prev[i]) % Rr; pm = (u64)rem; }
      int j = 0; while ((pm + Mmod * j) % Rr) j++;
      memcpy(cur, M3, 8 * NL); mulsmall(cur, j); addin(cur, prev);
      u128 rem = 0; for (int i = NL - 1; i >= 0; i--) { u128 c2 = (rem << 64) | cur[i]; cur[i] = (u64)(c2 / Rr); rem = c2 % Rr; }
      if (rem) { fprintf(stderr, "T fail\n"); return 1; }
    }
    free(inv);
  }
  long cap = N;
  int *G = malloc(sizeof(int) * cap), *G2 = malloc(sizeof(int) * cap);
  u64 *Q = malloc((size_t)cap * NL * 8), *Q2 = malloc((size_t)cap * NL * 8);
  long np = 1; G[0] = -1;
  for (int i = 0; i < NL; i++) Q[i] = rnd();
  if (Bb == 2) { /* top garbage is harmless */ }
  else { // uniform random L+2 trits by Horner
    memset(Q, 0, 8 * NL);
    for (int i = 0; i < L + 2; i++) { mulsmall(Q, Bb); u64 t = rnd() % Bb; u64 c = t; for (int k = 0; k < NL && c; k++) { u128 s2 = (u128)Q[k] + c; Q[k] = (u64)s2; c = (u64)(s2 >> 64); } }
  }
  int winsel = getenv("WINSEL") ? atoi(getenv("WINSEL")) : 0;
  long *Wbest = NULL;
  if (winsel > 0) { if (N < (1L << winsel)) { fprintf(stderr, "need N >= 2^WINSEL\n"); return 1; } Wbest = malloc(sizeof(long) << winsel); for (long i = 0; i < (1L << winsel); i++) Wbest[i] = -1; }
  long ccap = N * (long)K + 16; Cand *C = malloc(sizeof(Cand) * ccap);
  int *hist = calloc(Gmax + 2, sizeof(int));
  int *minG = malloc(sizeof(int) * L);
  int trace = (argc > 7 && !strcmp(argv[7], "trace"));
  int *TP = trace ? malloc(sizeof(int) * (size_t)L * N) : NULL, *TD = trace ? malloc(sizeof(int) * (size_t)L * N) : NULL;
  u64 *Y0 = malloc(8 * NL); memcpy(Y0, Q, 8 * NL);
  u64 *tmp = malloc(8 * NL);
  for (int b = 0; b < L; b++) {
    long nc = 0;
    for (long i = 0; i < np; i++) {
      u64 *q = Q + (size_t)i * NL; int dig;
      if (Bb == 2) dig = q[0] & 1; else dig = (int)modB(q);
      if (dig == 0) { C[nc].g = G[i]; C[nc].par = (int)i; C[nc].d = 0; nc++; }
      else {
        for (int d = 1; d <= K; d++) {
          int g = G[i] + d; if (g > Gmax) break;
          if (Bb != 2) { // R^{-g} mod B must equal the digit (else no term possible: dead if no g works)
            u64 tm = modB(T + (size_t)g * NL); if ((int)tm != dig) continue; }
          C[nc].g = g; C[nc].par = (int)i; C[nc].d = d; nc++;
        }
      }
    }
    // optional diversity selection: keep the cheapest child per W-bit window of its NEW residual (base 2)
    if (winsel > 0 && Bb == 2) {
      u64 wmask = (1ULL << winsel) - 1; long w = 0;
      for (long c = 0; c < nc; c++) {            // compute child's window: ((q - t) >> 1) & wmask, needs 2 limbs
        u64 *src = Q + (size_t)C[c].par * NL; u64 lo = src[0], hi = src[1];
        if (C[c].d) { u64 *t = T + (size_t)C[c].g * NL; u64 b0 = lo < t[0]; lo -= t[0]; hi = hi - t[1] - b0; }
        u64 win = ((lo >> 1) | (hi << 63)) & wmask;
        long slot = (long)win;
        if (Wbest[slot] < 0 || C[c].g < C[Wbest[slot]].g || (C[c].g == C[Wbest[slot]].g && (rnd() & 1))) Wbest[slot] = c;
      }
      for (long slot = 0; slot < (1L << winsel); slot++) {
        long c = Wbest[slot]; if (c < 0) continue; Wbest[slot] = -1;
        u64 *dst = Q2 + (size_t)w * NL, *src = Q + (size_t)C[c].par * NL;
        memcpy(dst, src, 8 * NL);
        if (C[c].d) subin(dst, T + (size_t)C[c].g * NL);
        shr1(dst); G2[w] = C[c].g; w++;
      }
      np = w; { int *tg = G; G = G2; G2 = tg; u64 *tq = Q; Q = Q2; Q2 = tq; }
      int mg = 1 << 30; for (long i = 0; i < np; i++) if (G[i] < mg) mg = G[i];
      minG[b] = mg; continue;
    }
    // select up to N smallest g
    long take = nc < N ? nc : N; int thr = 1 << 30; long below = 0, needeq = 0;
    if (nc > N) {
      int gmin = 1 << 30, gmx = -2; for (long c = 0; c < nc; c++) { if (C[c].g < gmin) gmin = C[c].g; if (C[c].g > gmx) gmx = C[c].g; }
      memset(hist, 0, sizeof(int) * (Gmax + 2));
      for (long c = 0; c < nc; c++) hist[C[c].g + 1]++;
      long acc = 0; for (int g = gmin; g <= gmx; g++) { if (acc + hist[g + 1] >= N) { thr = g; break; } acc += hist[g + 1]; }
      below = acc; needeq = N - acc;
    }
    long w = 0; long seeneq = 0, cnteq = (nc > N) ? hist[thr + 1] : 0;
    for (long c = 0; c < nc && w < take; c++) {
      int ok;
      if (nc <= N || C[c].g < thr) ok = 1;
      else if (C[c].g == thr) { // selection sampling: pick needeq of cnteq uniformly
        long remain = cnteq - seeneq; seeneq++;
        ok = (long)(rnd() % (u64)remain) < needeq; if (ok) needeq--;
      } else ok = 0;
      if (!ok) continue;
      u64 *dst = Q2 + (size_t)w * NL, *src = Q + (size_t)C[c].par * NL;
      memcpy(dst, src, 8 * NL);
      if (C[c].d) {
        u64 *t = T + (size_t)C[c].g * NL;
        if (Bb == 2) subin(dst, t);
        else { if (geq(dst, t)) subin(dst, t); else { addin(dst, M3); subin(dst, t); } }
      }
      if (Bb == 2) shr1(dst); else divB(dst);
      if (trace) { TP[(size_t)b * N + w] = C[c].par; TD[(size_t)b * N + w] = C[c].d; }
      G2[w] = C[c].g; w++;
    }
    (void)below;
    np = w; { int *tg = G; G = G2; G2 = tg; u64 *tq = Q; Q = Q2; Q2 = tq; }
    int mg = 1 << 30; for (long i = 0; i < np; i++) if (G[i] < mg) mg = G[i];
    minG[b] = mg;
  }
  // least squares slope of minG over b in [L/4, L)
  double sx = 0, sy = 0, sxx = 0, sxy = 0; long n = 0;
  for (int b = L / 4; b < L; b++) { double x = b, y = minG[b]; sx += x; sy += y; sxx += x * x; sxy += x * y; n++; }
  double slope = (n * sxy - sx * sy) / (n * sxx - sx * sx);
  double mu = log(Bb) / log(Rr);
  printf("B=%d R=%d L=%d N=%ld K=%d seed=%llu  v_N=%.5f  final minG/L=%.5f  mu=%.5f  ratio=%.4f  pop=%ld\n",
         Bb, Rr, L, N, K, seed, slope, (double)minG[L - 1] / L, mu, slope / mu, np);
  if (trace) {   // reconstruct best particle's staircase: print y and the (b, gamma) terms
    long best = 0; for (long i = 0; i < np; i++) if (G[i] < G[best]) best = i;
    int *pb = malloc(sizeof(int) * L), *pg = malloc(sizeof(int) * L); int nt = 0; long cur = best; int g = G[best];
    for (int b = L - 1; b >= 0; b--) { int d = TD[(size_t)b * N + cur]; if (d) { pb[nt] = b; pg[nt] = g; nt++; g -= d; } cur = TP[(size_t)b * N + cur]; }
    printf("Y=0x"); for (int i = NL - 1; i >= 0; i--) printf("%016llx", Y0[i]); printf("\nTERMS");
    for (int k = nt - 1; k >= 0; k--) printf(" %d:%d", pb[k], pg[k]); printf("\n");
  }
  return 0;
}
