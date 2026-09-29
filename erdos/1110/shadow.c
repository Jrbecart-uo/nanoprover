// 2-adic shadow of the representable set, (p,2) with p odd.
// O_A = odd m representable with all p-exponents < A (first term has 2-exponent 0).
// Exact recursion (magnitudes dropped => superset mod 2^K):
//   O_A = U_{a<A} ( p^a + 2*Rep_a ),   Rep_a = {0} U { 2^b o : b>=0, o in O_a }.
// S_A = O_A mod 2^K, computed as bitsets. Upper bound: #odd representable n < 2^k  <=  |S_{A_k} mod 2^k|,
// A_k = floor(log_p(2^k)) + 1.   Prints fraction |S_A mod 2^k| / 2^(k-1) for all k <= K and A.
// usage: shadow p K Amax
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
typedef uint64_t u64;
#define GETB(s,i) (((s)[(i)>>6]>>((i)&63))&1)
#define SETB(s,i) ((s)[(i)>>6] |= 1ULL<<((i)&63))
static u64 popc(const u64 *s, u64 nbits){ u64 c=0; for(u64 i=0;i<(nbits+63)/64;i++) c+=__builtin_popcountll(s[i]); return c; }
int main(int argc,char**argv){
  int p=atoi(argv[1]), K=atoi(argv[2]), Amax=atoi(argv[3]);
  u64 M=1ULL<<K, W=(M+63)/64;
  // S[a] = S_a mod 2^K (a = 0..Amax), proj[a][k] = S_a mod 2^k (bitset of size 2^k)
  u64 **S=malloc(sizeof(u64*)*(Amax+1));
  u64 ***proj=malloc(sizeof(u64**)*(Amax+1));
  S[0]=calloc(W,8);
  u64 *Rb=malloc(8*((M/2+63)/64+1));
  u64 pa=1; // p^a mod 2^K
  double mu=log(2)/log(p);
  for(int a=0;a<=Amax;a++){
    // projections of S[a]
    proj[a]=malloc(sizeof(u64*)*(K+1));
    proj[a][K]=S[a];
    for(int k=K-1;k>=1;k--){
      u64 m=1ULL<<k; proj[a][k]=calloc((m+63)/64+1,8);
      for(u64 r=0;r<m;r++) if(GETB(proj[a][k+1],r)||GETB(proj[a][k+1],r+m)) SETB(proj[a][k],r);
    }
    if(a==Amax) break;
    // R_a mod 2^(K-1) = {0} U U_{b=0}^{K-2} 2^b * (S_a mod 2^(K-1-b))
    u64 M1=M/2; memset(Rb,0,8*((M1+63)/64+1)); SETB(Rb,0);
    for(int b=0;b<=K-2;b++){ int k=K-1-b; u64 m=1ULL<<k;
      for(u64 o=1;o<m;o+=2) if(GETB(proj[a][k],o)) SETB(Rb,(o<<b)&(M1-1)); }
    // S_{a+1} = S_a U (p^a + 2 R_a) mod 2^K
    S[a+1]=calloc(W,8); memcpy(S[a+1],S[a],8*W);
    for(u64 r=0;r<M1;r++) if(GETB(Rb,r)) SETB(S[a+1],(pa+2*r)&(M-1));
    pa=(pa*p)&(M-1);
  }
  printf("p=%d K=%d mu=log_p 2=%.5f\n",p,K,mu);
  printf(" k  A_k | frac(A_k-1) frac(A_k)  frac(A_k+1) frac(A_k+2)\n");
  for(int k=3;k<=K;k++){
    int Ak=(int)floor(k*mu)+1; // exponents a with p^a < 2^k: a <= floor(k*mu) (p^a != 2^k)
    printf("%2d %3d |",k,Ak);
    for(int d=-1;d<=2;d++){ int A=Ak+d; if(A<0||A>Amax){printf("   -   ");continue;}
      u64 c=popc(proj[A][k],1ULL<<k); printf(" %.5f",(double)c/(double)(1ULL<<(k-1))); }
    printf("\n");
  }
  return 0;
}
