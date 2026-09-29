// Bitset version of rep.c: fraction of n <= 2^L representable (antichain sums of p^a q^b),
// printed at each power of 2, plus the fraction inside each residue class mod M (argv[4]).
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef unsigned long long u64;
static u64 *R; static u64 X; static int P,Q;
#define SET(n) (R[(n)>>6] |= 1ULL<<((n)&63))
#define GET(n) ((R[(n)>>6]>>((n)&63))&1)
static void rec(u64 sum, int amin, int bmax){
  u64 pa=1; for(int i=0;i<amin;i++){ if(pa> X/P) return; pa*=P; }
  for(int a=amin;;a++){
    if(pa> X) break;
    u64 t=pa;
    for(int b=0;b<=bmax;b++){
      if(t> X-sum) break;
      u64 s=sum+t; SET(s);
      if(b>0) rec(s,a+1,b-1);
      if(t> X/Q) break; t*=Q;
    }
    if(pa> X/P) break; pa*=P;
  }
}
int main(int argc,char**argv){
  P=atoi(argv[1]);Q=atoi(argv[2]);int L=atoi(argv[3]); int M=argc>4?atoi(argv[4]):1; X=(1ULL<<L);
  R=calloc((X>>6)+2,8); rec(0,0,64);
  u64 c=0, nxt=1<<16; u64 cls[64]={0}, tot[64]={0};
  for(u64 n=1;n<=X;n++){ int g=GET(n); c+=g; cls[n%M]+=g; tot[n%M]++;
    if(n==nxt){ printf("(%d,%d) x=2^%d frac=%.5f |",P,Q,__builtin_ctzll(n),(double)c/n);
      for(int r=0;r<M;r++) printf(" %d:%.4f",r,(double)cls[r]/tot[r]); printf("\n"); fflush(stdout); nxt<<=1; } }
  return 0;
}
