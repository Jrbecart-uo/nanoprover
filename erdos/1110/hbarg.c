// Generic: residues mod M = P^s (P = block base), chain terms P^alpha * Q^{-beta} mod M, alpha<s, strict chains.
// Average minimal height H(s) in the beta direction; bound s*log(P)/log(Q).
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
typedef uint64_t u64;
static u64 M, NW, lastmask;
static inline int getb(const u64*a,u64 i){return (a[i>>6]>>(i&63))&1;}
// dst |= src rotated by k (bit x -> (x+k) mod M), generic M
static void rot_or(u64 *dst, const u64 *src, u64 k){
  k %= M; if(!k){ for(u64 i=0;i<NW;i++) dst[i]|=src[i]; return; }
  // part 1: bits x in [0, M-k) go to x+k   (left shift by k)
  // part 2: bits x in [M-k, M) go to x+k-M (right shift by M-k)
  u64 wq=k>>6; unsigned br=k&63;
  #pragma omp parallel for schedule(static)
  for(u64 i=wq;i<NW;i++){ u64 j=i-wq; u64 v=src[j]<<br; if(br && j>0) v|=src[j-1]>>(64-br); dst[i]|=v; }
  // bits shifted beyond M must be dropped: handled by masking last word later; but those bits (x+k>=M) are the part-2 bits.
  u64 r=M-k; u64 rq=r>>6; unsigned rb=r&63;
  #pragma omp parallel for schedule(static)
  for(u64 i=0;i<NW;i++){ u64 j=i+rq; u64 v=0; if(j<NW) v=src[j]>>rb; if(rb && j+1<NW) v|=src[j+1]<<(64-rb); dst[i]|=v; }
  dst[NW-1]&=lastmask;
}
static u64 popc(const u64*a){u64 c=0;
  #pragma omp parallel for reduction(+:c)
  for(u64 i=0;i<NW;i++)c+=__builtin_popcountll(a[i]);return c;}
static u64 mulmod(u64 a,u64 b){ return (unsigned __int128)a*b % M; }
int main(int argc,char**argv){
  u64 P=atoi(argv[1]),Q=atoi(argv[2]); int s=atoi(argv[3]), H=atoi(argv[4]);
  M=1; for(int i=0;i<s;i++) M*=P; NW=(M+63)>>6; lastmask = (M&63)? ((1ULL<<(M&63))-1) : ~0ULL;
  // Q^{-1} mod M
  long long t=0,nt=1; long long r=M, nr=Q%M; while(nr){ long long qq=r/nr, tmp; tmp=t-qq*nt; t=nt; nt=tmp; tmp=r-qq*nr; r=nr; nr=tmp; }
  u64 qinv = (u64)((t%(long long)M+M)%M);
  u64 *u=malloc(8*(H+1)); u[0]=1; for(int g=1;g<=H;g++) u[g]=mulmod(u[g-1],qinv);
  u64 **U=malloc(sizeof(u64*)*(H+1)); for(int h=0;h<=H;h++){ U[h]=calloc(NW,8); U[h][0]=1; }
  u64 pw=1;
  for(int m=1;m<=s;m++){
    // new U[h] = old U[h] ∪ ⋃_{g<h} (old U[g] + pw*u[g]); update h descending so U[g<h] still old
    for(int h=H; h>=1; h--) for(int g=0; g<h; g++) rot_or(U[h], U[g], mulmod(pw,u[g]));
    pw*=P;
  }
  double hbar=0; int full=-1;
  for(int h=0;h<=H;h++){ u64 c=popc(U[h]); double fr=(double)c/M; if(h<H) hbar+=1-fr; if(c==M&&full<0) full=h; }
  printf("P=%llu Q=%llu s=%d M=%llu Hbar=%.4f bound=%.4f full_at=%d (H=%d)\n",(unsigned long long)P,(unsigned long long)Q,s,(unsigned long long)M,hbar,s*log((double)P)/log((double)Q),full,H);
  return 0;
}
