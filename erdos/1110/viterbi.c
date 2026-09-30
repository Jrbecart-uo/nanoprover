// Forward reachable-set ("Viterbi") process on W-bit window states, base 2, other base R.
// State x = normalized residual mod 2^W.  Each step one fresh bit u enters as bit W (the SAME u for every
// state: the maximally-correlated "window model").  V[x] = min cost (final gamma) over all paths reaching x.
//   x even:  x' = (x + 2^W u) / 2                       cost 0
//   x odd :  x' = ((R^d (x + 2^W u) - 1) / 2) mod 2^W   cost d  (d = 1..K)
// Existence of a bounded-excess infinite path <=> the reachable set never empties (Koenig), and this set
// evolves FORWARD with no look-ahead.  Rate = growth of min_x V[x] per bit.  Compare with online rollout at
// the same W: if Viterbi << rollout, the offline advantage is "many live candidates", not "far look-ahead".
// usage: viterbi R W L K seed
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <omp.h>
typedef unsigned long long u64;
int main(int argc, char **argv) {
  u64 R = atoll(argv[1]); int W = atoi(argv[2]); long L = atol(argv[3]); int K = atoi(argv[4]); u64 seed = strtoull(argv[5], 0, 10);
  u64 S = 1ULL << W, M = S - 1, M1 = (S << 1) - 1;
  long keepN = getenv("KEEPN") ? atol(getenv("KEEPN")) : 0;
  int *V = malloc(sizeof(int) * S), *V2 = malloc(sizeof(int) * S);
  const int INF = 1 << 29;
  for (u64 x = 0; x < S; x++) V[x] = 0;                   // start: every window equally possible (uniform target)
  u64 Rd[64]; Rd[0] = 1; for (int d = 1; d <= K; d++) Rd[d] = Rd[d - 1] * R;   // mod 2^64 is enough (we mask)
  u64 s0 = seed * 0x9E3779B97F4A7C15ULL + 7, s1 = seed ^ 0xD1B54A32D192ED03ULL;
  #define RND() ({ u64 x_ = s0, y_ = s1; s0 = y_; x_ ^= x_ << 23; s1 = x_ ^ y_ ^ (x_ >> 17) ^ (y_ >> 26); s1 + y_; })
  // start from a single random window (a specific target), not all windows
  for (u64 x = 0; x < S; x++) V[x] = INF;
  V[RND() & M] = 0;
  double t0 = omp_get_wtime(); long base = 0; int minv0 = 0;
  long mark1 = L / 4; int minmark = 0;
  for (long t = 0; t < L; t++) {
    u64 u = RND() & 1;
    for (u64 x = 0; x < S; x++) V2[x] = INF;
    // push-style update (serial; W <= 24 is fine)
    for (u64 x = 0; x < S; x++) {
      int v = V[x]; if (v >= INF) continue;
      u64 z = x | (u << W);                               // W+1 bits
      if (!(z & 1)) { u64 nx = (z >> 1) & M; if (v < V2[nx]) V2[nx] = v; }
      else for (int d = 1; d <= K; d++) {
        u64 t2 = (Rd[d] * z) & M1; u64 nx = ((t2 - 1) >> 1) & M;
        int c = v + d; if (c < V2[nx]) V2[nx] = c;
      }
    }
    if (keepN > 0) {                                   // beam in the window model: keep only the keepN cheapest states
      static int *hist = NULL; if (!hist) hist = calloc(1 << 16, sizeof(int));
      int mx = 0; for (u64 x = 0; x < S; x++) if (V2[x] < INF && V2[x] > mx) mx = V2[x];
      int top = mx < (1 << 16) - 1 ? mx : (1 << 16) - 1;
      memset(hist, 0, sizeof(int) * (top + 1));
      long live2 = 0; for (u64 x = 0; x < S; x++) if (V2[x] < INF) { hist[V2[x] > top ? top : V2[x]]++; live2++; }
      if (live2 > keepN) {
        long acc = 0; int thr = 0; for (; thr <= top; thr++) { if (acc + hist[thr] >= keepN) break; acc += hist[thr]; }
        long need = keepN - acc;                       // keep all < thr, and `need` of those == thr (first ones)
        for (u64 x = 0; x < S; x++) { if (V2[x] >= INF) continue; if (V2[x] > thr) V2[x] = INF; else if (V2[x] == thr) { if (need > 0) need--; else V2[x] = INF; } }
      }
    }
    int mn = INF; for (u64 x = 0; x < S; x++) if (V2[x] < mn) mn = V2[x];
    // renormalize to avoid overflow
    for (u64 x = 0; x < S; x++) if (V2[x] < INF) V2[x] -= mn;
    base += mn;
    int *tmp = V; V = V2; V2 = tmp;
    if (t == mark1) minmark = (int)base;
    (void)minv0;
  }
  double mu = log(2) / log((double)R);
  double rate = (double)(base - minmark) / (L - mark1 - 1);
  long live = 0; for (u64 x = 0; x < S; x++) if (V[x] < INF) live++;
  printf("R=%llu W=%d L=%ld K=%d: viterbi rate=%.5f  mu=%.5f  ratio=%.4f  live states at end=%ld (%.3f)  %.1fs\n",
         R, W, L, K, rate, mu, rate / mu, live, (double)live / S, omp_get_wtime() - t0);
  return 0;
}
