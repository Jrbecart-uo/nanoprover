// Average minimal chain height for residues mod 2^s, chains {(alpha,gamma)} strictly increasing in both,
// value sum 2^alpha * p^{-gamma} mod 2^s.  U[h] = residues reachable with alpha < m, gamma < h.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef uint64_t u64;
static int s; static u64 M, NW;
static void rot_or(u64 *dst, const u64 *src, u64 k){ // dst |= src rotated by k (bit x -> x+k mod M)
  k %= M; u64 wq = k >> 6; unsigned br = k & 63;
  #pragma omp parallel for schedule(static)
  for (u64 i = 0; i < NW; i++){
    u64 j = (i + NW - wq) % NW; u64 v = src[j] << br;
    if (br) { u64 j2 = (j + NW - 1) % NW; v |= src[j2] >> (64 - br); }
    dst[i] |= v;
  }
}
static u64 popc(const u64 *a){ u64 c=0;
  #pragma omp parallel for reduction(+:c)
  for(u64 i=0;i<NW;i++) c+=__builtin_popcountll(a[i]); return c; }
int main(int argc, char **argv){
  int p = atoi(argv[1]); s = atoi(argv[2]); int H = atoi(argv[3]);
  M = 1ULL << s; NW = M >> 6; u64 mask = M - 1;
  // u_g = p^{-g} mod 2^s
  u64 pinv = 1; { u64 x = p; for (int i=0;i<64;i++){ pinv *= (2 - x*pinv); } } // 2-adic inverse
  u64 *u = malloc(sizeof(u64)*(H+1)); u[0]=1; for(int g=1;g<=H;g++) u[g]=(u[g-1]*pinv)&mask;
  u64 **A = malloc(sizeof(u64*)*(H+1));
  for(int h=0;h<=H;h++){ A[h]=calloc(NW,8); A[h][0]=1; }
  for(int m=1;m<=s;m++){
    u64 sh = (1ULL<<(m-1));
    for(int h=H; h>=1; h--) for(int g=0; g<h; g++) rot_or(A[h], A[g], (sh*u[g]) & mask);
  }
  double hbar=0; int full=-1;
  for(int h=0;h<=H;h++){ u64 c=popc(A[h]); double fr=(double)c/M;
    printf("h=%2d covered=%.6f\n",h,fr); if(h<H) hbar += 1.0-fr; if(c==M && full<0) full=h; }
  printf("p=%d s=%d  Hbar=%.4f (tail beyond H counted as 0)  bound s*log_p 2=%.4f  full_at_h=%d\n",
    p, s, hbar, s*0.69314718056/__builtin_log((double)p), full);
  return 0;
}
