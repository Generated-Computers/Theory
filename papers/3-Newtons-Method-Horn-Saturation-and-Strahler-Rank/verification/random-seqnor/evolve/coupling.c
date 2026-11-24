// Coalescence time of random block bases (NOTE.md §5j). A smoothed random block base is built as in
// ../blockbase.c (blocks of length B, targets at offsets h..B-2 of the previous block, noise eps);
// 64 copies are started at a block boundary s from independent random states on [s-B, s) (reads below
// s-B take the true values), and simulated bit-parallel. The coalescence time is the number of
// positions until all copies agree on a whole block. At eps = 0 they then agree forever (a block reads
// only the previous block), so this lower-bounds the grand coupling time and gives the window length
// that windowed Jacobi (wjacobi.c) needs. At eps > 0 agreement can be lost again, because noisy reads
// land in the region after s where copies still differ; there the first agreement is only indicative
// and wjacobi.c is the faithful test.
// With a seventh argument `profile`, it prints instead, at block offsets 1, 2, 4, ..., the fraction of
// copies that equal the true trace on the whole block and the mean disagreement of the other copies
// (over the trials that still have such copies).
// usage: ./coupling B h eps maxblocks trials seed [profile]
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
static uint64_t st;
static inline uint64_t rnd(){ st^=st<<13; st^=st>>7; st^=st<<17; return st; }
static inline double unif(){ return (rnd()>>11)*(1.0/9007199254740992.0); }
static int cmp(const void *a, const void *b){ long u=*(const long*)a, v=*(const long*)b; return (u>v)-(u<v); }

int main(int argc,char**argv){
  long B=atol(argv[1]), h0=atol(argv[2]); double eps=atof(argv[3]); long nb=atol(argv[4]);
  int trials=atoi(argv[5]); st=0x9E3779B97F4A7C15ULL ^ (uint64_t)atol(argv[6]); int prof=argc>7;
  double merged[40]={0}, dis[40]={0}; int live[40]={0}, K=0;
  long n=B*(2*nb+1); int *j=malloc((n+1)*sizeof(int)); char *x=malloc(n+1); uint64_t *w=malloc((n+1)*8);
  long *res=malloc(trials*sizeof(long)); int never=0;
  for(int t=0;t<trials;t++){
    for(long i=1;i<=n;i++){
      long b=i/B, base;
      if(b==0) base = i>=2? i-2:0; else base=(b-1)*B+h0+(long)(rnd()%(uint64_t)(B-1-h0));
      if(i>=2 && unif()<eps) j[i]=(int)(rnd()%(uint64_t)i); else j[i]=(int)base;
    }
    x[0]=1; for(long i=1;i<=n;i++) x[i]=(x[i-1]==0 && x[j[i]]==0);
    long s=nb*B;
    for(long p=0;p<s-B;p++) w[p]= x[p]? ~0ULL : 0;
    for(long p=s-B;p<s;p++) w[p]=rnd();
    res[t]=-1; int k=0; long next=1;
    for(long b=nb;b<2*nb && (prof || res[t]<0);b++){
      int agree=1; uint64_t bad=0; long cnt=0;
      for(long p=b*B;p<(b+1)*B;p++){
        w[p]=~(w[p-1]|w[j[p]]); if(w[p]!=0 && w[p]!=~0ULL) agree=0;
        uint64_t d=w[p]^(x[p]? ~0ULL : 0); bad|=d; cnt+=__builtin_popcountll(d);
      }
      if(agree && res[t]<0) res[t]=(b-nb+1)*B;
      if(prof && b-nb+1==next){
        int um=__builtin_popcountll(bad);
        merged[k]+=(64.0-um)/64; if(um){ dis[k]+=(double)cnt/(um*(double)B); live[k]++; } k++; next*=2;
      }
    }
    K=k;
    if(res[t]<0){ never++; res[t]=nb*B+1; }
  }
  if(prof){
    for(int k=0;k<K;k++){
      printf("B=%ld h=%ld eps=%.3f  after %6ld blocks: copies equal to the truth %.3f, disagreement of the others ",
             B,h0,eps,1L<<k,merged[k]/trials);
      if(live[k]) printf("%.3f (%d trials)\n",dis[k]/live[k],live[k]); else printf("- (none left)\n");
    }
    return 0;
  }
  qsort(res,trials,sizeof(long),cmp);
  printf("B=%-5ld h=%-4ld eps=%.3f  coalescence (positions): median %ld  p90 %ld  max %ld%s  [blocks: median %.1f]\n",
         B,h0,eps,res[trials/2],res[(9*trials)/10],res[trials-1],never?"  (some never within cap)":"",
         (double)res[trials/2]/B);
  return 0;
}
