// Lookahead MDP: states c in Z/2^s. Chains C (alpha<s, strict in alpha & gamma, gamma<H) with value
// v(C)=sum 2^alpha 7^{-gamma} (2-adic, kept mod 2^{2s}); c(C)=v mod 2^s, k(C)=(v>>s) mod 2^s, h(C)=max gamma+1.
// Transition: fresh b uniform; c' = 7^{h}(b - k) mod 2^s.  Bellman (average cost):
//   phi'(c) = avg_b min_{C in chains(c)} [ h(C) + phi(c') ] ;  g = lim (phi' - phi).
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
typedef uint64_t u64;
int s,H,SLACK; u64 S,MS,M2;
typedef struct { u64 k; int h; } Ch;
Ch *ch; u64 nch=0, cap=0; u64 *res; // res[i] = residue c of chain i
u64 *u; // 7^{-g} mod 2^{2s}
void add(u64 v,int h){ if(nch==cap){cap=cap?cap*2:1<<20; ch=realloc(ch,cap*sizeof(Ch)); res=realloc(res,cap*8);} 
  ch[nch].k=(v>>s)&MS; ch[nch].h=h; res[nch]=v&MS; nch++; }
void gen(int a0,int g0,u64 v,int h){ // extend chain with alpha>=a0, gamma>=g0
  add(v,h);
  for(int a=a0;a<s;a++) for(int g=g0;g<H;g++){ u64 t=(u[g]<<a)&(M2-1); gen(a+1,g+1,(v+t)&(M2-1),g+1); }
}
int cmpres(const void*x,const void*y){ return 0; }
int main(int argc,char**argv){
  s=atoi(argv[1]); H=atoi(argv[2]); int iters=atoi(argv[3]); SLACK=atoi(argv[4]);
  S=1ULL<<s; MS=S-1; M2=1ULL<<(2*s);
  u64 pinv=1; { u64 x=7; for(int i=0;i<64;i++) pinv*=(2-x*pinv);} 
  u=malloc(8*(H+1)); u[0]=1; for(int g=1;g<=H;g++) u[g]=(u[g-1]*pinv)&(M2-1);
  gen(0,0,0,0);
  fprintf(stderr,"chains: %llu\n",(unsigned long long)nch);
  // bucket chains by residue
  u64 *cnt=calloc(S+1,8); for(u64 i=0;i<nch;i++) cnt[res[i]+1]++; for(u64 c=0;c<S;c++) cnt[c+1]+=cnt[c];
  Ch *bk=malloc(nch*sizeof(Ch)); u64 *pos=malloc(8*S); memcpy(pos,cnt,8*S);
  for(u64 i=0;i<nch;i++) bk[pos[res[i]]++]=ch[i];
  for(u64 c=0;c<S;c++) if(cnt[c+1]==cnt[c]){ fprintf(stderr,"residue %llu uncovered, raise H\n",(unsigned long long)c); return 1; }
  { // prune in place per residue
    u64 w=0; u64 *ncnt=calloc(S+1,8);
    for(u64 c=0;c<S;c++){ int mh=99; for(u64 j=cnt[c];j<cnt[c+1];j++) if(bk[j].h<mh) mh=bk[j].h;
      ncnt[c]=w; for(u64 j=cnt[c];j<cnt[c+1];j++) if(bk[j].h<=mh+SLACK) bk[w++]=bk[j]; }
    ncnt[S]=w; memcpy(cnt,ncnt,8*(S+1)); fprintf(stderr,"after prune: %llu chains (%.1f/residue)\n",(unsigned long long)w,(double)w/S);
  }
  u64 *p7=malloc(8*(H+2)); p7[0]=1; for(int i=1;i<=H+1;i++) p7[i]=(p7[i-1]*7)&MS;
  double *phi=calloc(S,8), *nphi=malloc(8*S);
  double g=0, mu=log(2)/log(7);
  for(int it=0;it<iters;it++){
    #pragma omp parallel for schedule(dynamic,64)
    for(u64 c=0;c<S;c++){
      double tot=0;
      for(u64 b=0;b<S;b++){
        double best=1e18;
        for(u64 j=cnt[c];j<cnt[c+1];j++){
          u64 cp=((b - bk[j].k)&MS)*p7[bk[j].h]&MS;
          double val=bk[j].h+phi[cp]; if(val<best) best=val;
        }
        tot+=best;
      }
      nphi[c]=tot/S;
    }
    double mn=1e18,mx=-1e18; for(u64 c=0;c<S;c++){ double d=nphi[c]-phi[c]; if(d<mn)mn=d; if(d>mx)mx=d; }
    double base=nphi[0]; for(u64 c=0;c<S;c++) phi[c]=nphi[c]-base;
    printf("s=%d H=%d it=%d  g in [%.5f, %.5f]  per-bit [%.5f, %.5f]  need < %.5f\n",s,H,it,mn,mx,mn/s,mx/s,mu);
    fflush(stdout);
  }
  return 0;
}
