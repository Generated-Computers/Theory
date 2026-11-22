// Mean max depth of the Kleene-prefix (d) and relevance-pruned (D) iterations on smoothed random
// block bases with equal blocks of length B (paper Table tab:block, Remark rem:kp-lower).
// usage: ./blockbase n B h eps reps seed
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
static uint64_t st;
static inline uint64_t rnd(){ st^=st<<13; st^=st>>7; st^=st<<17; return st; }
static inline double unif(){ return (rnd()>>11)*(1.0/9007199254740992.0); }
int main(int argc,char**argv){
  long n=atol(argv[1]); long B=atol(argv[2]); long h0=atol(argv[3]); double eps=atof(argv[4]);
  int reps=atoi(argv[5]); st=0x9E3779B97F4A7C15ULL ^ (uint64_t)atol(argv[6]);
  int *j=malloc((n+1)*sizeof(int)); char *x=malloc(n+1); int *D=malloc((n+1)*sizeof(int)); int *d=malloc((n+1)*sizeof(int));
  double sD=0,sd=0;
  for(int r=0;r<reps;r++){
    for(long i=1;i<=n;i++){
      long b=i/B, base;
      if(b==0) base = i>=2? i-2:0; else base=(b-1)*B+h0+(long)(rnd()%(uint64_t)(B-1-h0));
      if(i>=2 && unif()<eps) j[i]=(int)(rnd()%(uint64_t)i); else j[i]=(int)base;
    }
    x[0]=1; for(long i=1;i<=n;i++) x[i]=(x[i-1]==0 && x[j[i]]==0);
    D[0]=d[0]=0; D[1]=d[1]=1; int mD=1,md=1;
    for(long i=2;i<=n;i++){
      int nt=j[i]!=i-1, rel=x[i-1]==0, res=nt&&x[j[i]];
      int a=1+d[j[i]];
      d[i]= res? a : (nt? (d[i-1]>a?d[i-1]:a) : d[i-1]);
      int c=1+D[j[i]];
      if(res&&rel) D[i]=c; else if(res) D[i]=D[i-1]<c?D[i-1]:c; else if(rel&&nt) D[i]=D[i-1]>c?D[i-1]:c; else D[i]=D[i-1];
      if(D[i]>mD) mD=D[i]; if(d[i]>md) md=d[i];
    }
    sD+=mD; sd+=md;
  }
  printf("n=%ld B=%ld eps=%.3f blocks=%ld  KPR=%.1f  KP=%.1f\n",n,B,eps,n/B,sD/reps,sd/reps);
  return 0;
}
