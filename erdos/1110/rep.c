// mark n <= X representable as sum of p^a q^b over an antichain (a strictly up, b strictly down)
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef unsigned long long u64;
static unsigned char *R; static u64 X; static int P,Q;
// terms chosen in order of increasing a, decreasing b: next term needs a > a_prev, b < b_prev
static void rec(u64 sum, int amin, int bmax){ // next a >= amin, next b <= bmax
  u64 pa=1; for(int i=0;i<amin;i++){ if(pa> X/P) return; pa*=P; }
  for(int a=amin;;a++){
    if(pa> X) break;
    u64 t=pa;
    for(int b=0;b<=bmax;b++){
      if(t> X-sum) break;
      u64 s=sum+t; R[s]=1;
      if(b>0) rec(s,a+1,b-1);
      if(t> X/Q) break; t*=Q;
    }
    if(pa> X/P) break; pa*=P;
  }
}
int main(int argc,char**argv){
  P=atoi(argv[1]);Q=atoi(argv[2]);int L=atoi(argv[3]); X=(1ULL<<L);
  R=calloc(X+1,1); rec(0,0,64);
  u64 c=0; u64 nxt=1<<10;
  for(u64 n=1;n<=X;n++){ c+=R[n]; if(n==nxt){ printf("x=2^%d  frac=%.4f\n",__builtin_ctzll(n),(double)c/n); nxt<<=1;} }
  return 0;
}
