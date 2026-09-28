// Optimal stopping tree for variable-length 2-adic blocks.
// m_l(x): min height of a chain with alpha < l realizing x mod 2^l (x in [0,2^l)).
// V_D(x) = m_D(x) - mu*D ; V_l(x) = min(m_l(x) - mu*l, (V_{l+1}(x)+V_{l+1}(x+2^l))/2).  Report V_0 (root).
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
typedef uint64_t u64;
static u64 M, NW;
static void rot_or(u64 *dst, const u64 *src, u64 k){
  k %= M; u64 wq = k >> 6; unsigned br = k & 63;
  #pragma omp parallel for schedule(static)
  for (u64 i = 0; i < NW; i++){ u64 j=(i+NW-wq)%NW; u64 v=src[j]<<br; if(br){u64 j2=(j+NW-1)%NW; v|=src[j2]>>(64-br);} dst[i]|=v; }
}
int main(int argc,char**argv){
  int p=atoi(argv[1]), D=atoi(argv[2]), H=atoi(argv[3]); double mu=atof(argv[4]);
  M=1ULL<<D; NW=M>>6; u64 mask=M-1;
  u64 pinv=1; { u64 x=p; for(int i=0;i<64;i++) pinv*=(2-x*pinv); }
  u64 *u=malloc(8*(H+1)); u[0]=1; for(int g=1;g<=H;g++) u[g]=(u[g-1]*pinv)&mask;
  u64 **A=malloc(sizeof(u64*)*(H+1)); for(int h=0;h<=H;h++){A[h]=calloc(NW,8);A[h][0]=1;}
  unsigned char **mm=malloc(sizeof(unsigned char*)*(D+1)); // mm[l][x] min height, 255 = unreachable within H
  mm[0]=malloc(1); mm[0][0]=0;
  for(int l=1;l<=D;l++){
    u64 sh=1ULL<<(l-1);
    for(int h=H;h>=1;h--) for(int g=0;g<h;g++) rot_or(A[h],A[g],(sh*u[g])&mask);
    u64 L=1ULL<<l; mm[l]=malloc(L); memset(mm[l],255,L);
    // project each A[h] mod 2^l, record min h
    for(int h=0;h<=H;h++){
      if(l>=6){
        u64 LW=L>>6; u64 *proj=calloc(LW,8);
        for(u64 i=0;i<NW;i++) proj[i%LW]|=A[h][i];
        #pragma omp parallel for
        for(u64 x=0;x<L;x++) if(mm[l][x]==255 && ((proj[x>>6]>>(x&63))&1)) mm[l][x]=h;
        free(proj);
      } else {
        for(u64 x=0;x<M;x++) if((A[h][x>>6]>>(x&63))&1){ u64 y=x&(L-1); if(mm[l][y]==255) mm[l][y]=h; }
      }
    }
  }
  // bottom-up V
  u64 L=1ULL<<D; double *V=malloc(8*L);
  for(u64 x=0;x<L;x++) V[x]= (mm[D][x]==255? 1e9 : mm[D][x]-mu*D);
  double *st=NULL; // stopping stats: probability-weighted E[h], E[l]
  // also track E[h] and E[len] of the optimal tree
  double *Eh=malloc(8*L), *El=malloc(8*L);
  for(u64 x=0;x<L;x++){ Eh[x]=mm[D][x]; El[x]=D; }
  unsigned char **dec=malloc(sizeof(unsigned char*)*(D+1));
  for(int l=D-1;l>=0;l--){
    u64 Ll=1ULL<<l; dec[l]=calloc(Ll,1);
    for(u64 x=0;x<Ll;x++){
      double c=(V[x]+V[x+Ll])/2, sv=(mm[l][x]==255?1e9:mm[l][x]-mu*l);
      if(l>0 && sv<=c){ V[x]=sv; Eh[x]=mm[l][x]; El[x]=l; }
      else { V[x]=c; Eh[x]=(Eh[x]+Eh[x+Ll])/2; El[x]=(El[x]+El[x+Ll])/2; dec[l][x]=1; }
    }
  }
  { // top-down reach counts
    unsigned char *reach=calloc(1,1); reach[0]=1;
    for(int l=0;l<D;l++){ u64 Ll=1ULL<<l; u64 nr=0,nc=0; unsigned char *nx=calloc(2*Ll,1);
      for(u64 x=0;x<Ll;x++) if(reach[x]){ nr++; if(dec[l][x]){ nc++; nx[x]=1; nx[x+Ll]=1; } }
      printf("depth %2d: reached %llu (prob %.3e), continue %llu\n",l,(unsigned long long)nr,(double)nr/Ll,(unsigned long long)nc);
      free(reach); reach=nx; }
  }
  printf("p=%d D=%d mu=%.5f  V(root)=%.5f  E[h]=%.4f E[len]=%.4f ratio=%.5f (need < %.5f)\n",
    p,D,mu,V[0],Eh[0],El[0],Eh[0]/El[0],log(2)/log(p));
  return 0;
}
