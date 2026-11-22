// Windowed Jacobi with exact values (NOTE.md §5j). Each round recomputes every position: the tile
// [t, t+L) is simulated sequentially from t-LB, taking the previous round's values for the state at
// t-LB-1 and for every read below t-LB. A round costs parallel time L+LB and work about n(1+LB/L).
// The rounds stop when the local equations x_i = NOR(x_{i-1}, x_{j_i}) all hold; the solution is
// unique, so this certifies the trace and the algorithm is errorless. It succeeds fast when windows
// of length LB forget their start state (coalescence) and reads below the window resolve in few
// rounds. Instances: random block bases built exactly as in ../blockbase.c (mode bb, with the
// Kleene-prefix depth d and relevance-pruned depth D printed for comparison; they are the rounds of
// KP and KPR), or test-bed files (mode file).
// usage: ./wjacobi L LB MAXR bb n B h eps reps seed
//        ./wjacobi L LB MAXR file f1 f2 ...
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static uint64_t st;
static inline uint64_t rnd(){ st^=st<<13; st^=st>>7; st^=st<<17; return st; }
static inline double unif(){ return (rnd()>>11)*(1.0/9007199254740992.0); }

static long L, LB; static int MAXR;

// returns the number of rounds until the local equations hold (MAXR+1 if never); *wrong1 gets the
// number of wrong positions after round 1
static int wjacobi(long n, const int *j, const char *x, long *wrong1){
  char *y=calloc(n+1,1), *z=malloc(n+1), *v=malloc(L+LB+1); y[0]=1;
  int r;
  for(r=1;r<=MAXR;r++){
    z[0]=1;
    for(long t=1;t<=n;t+=L){
      long e=t+L<n+1? t+L : n+1, a=t-LB>1? t-LB : 1;
      v[0]=y[a-1];                                 // v[k-a+1] holds position k
      for(long k=a;k<e;k++){
        long p=j[k]; char u= p>=a? v[p-a+1] : y[p];
        v[k-a+1]= !(v[k-a] | u);
      }
      for(long k=t;k<e;k++) z[k]=v[k-a+1];
    }
    long bad=0, wr=0;
    for(long i=1;i<=n;i++){ bad += z[i] != !(z[i-1]|z[j[i]]); wr += z[i]!=x[i]; }
    if(r==1) *wrong1=wr;
    if((bad==0) != (wr==0)){ fprintf(stderr,"certificate mismatch\n"); exit(1); }
    char *s=y; y=z; z=s;
    if(bad==0) break;
  }
  free(y); free(z); free(v);
  return r;
}

static void depths(long n, const int *j, const char *x, int *md, int *mD){
  int *D=malloc((n+1)*sizeof(int)), *d=malloc((n+1)*sizeof(int));
  D[0]=d[0]=0; D[1]=d[1]=1; *mD=1; *md=1;
  for(long i=2;i<=n;i++){                          // as in ../blockbase.c
    int nt=j[i]!=i-1, rel=x[i-1]==0, res=nt&&x[j[i]];
    int a=1+d[j[i]];
    d[i]= res? a : (nt? (d[i-1]>a?d[i-1]:a) : d[i-1]);
    int c=1+D[j[i]];
    if(res&&rel) D[i]=c; else if(res) D[i]=D[i-1]<c?D[i-1]:c; else if(rel&&nt) D[i]=D[i-1]>c?D[i-1]:c; else D[i]=D[i-1];
    if(D[i]>*mD) *mD=D[i]; if(d[i]>*md) *md=d[i];
  }
  free(D); free(d);
}

int main(int argc,char**argv){
  L=atol(argv[1]); LB=atol(argv[2]); MAXR=atoi(argv[3]);
  if(!strcmp(argv[4],"bb")){
    long n=atol(argv[5]); long B=atol(argv[6]); long h0=atol(argv[7]); double eps=atof(argv[8]);
    int reps=atoi(argv[9]); st=0x9E3779B97F4A7C15ULL ^ (uint64_t)atol(argv[10]);
    int *j=malloc((n+1)*sizeof(int)); char *x=malloc(n+1);
    double sd=0,sD=0,sr=0,sw=0; int rmax=0;
    for(int rep=0;rep<reps;rep++){
      for(long i=1;i<=n;i++){                      // as in ../blockbase.c
        long b=i/B, base;
        if(b==0) base = i>=2? i-2:0; else base=(b-1)*B+h0+(long)(rnd()%(uint64_t)(B-1-h0));
        if(i>=2 && unif()<eps) j[i]=(int)(rnd()%(uint64_t)i); else j[i]=(int)base;
      }
      j[1]=0;
      x[0]=1; for(long i=1;i<=n;i++) x[i]=(x[i-1]==0 && x[j[i]]==0);
      int md,mD; depths(n,j,x,&md,&mD); long w1; int r=wjacobi(n,j,x,&w1);
      sd+=md; sD+=mD; sr+=r; sw+=w1; if(r>rmax) rmax=r;
    }
    printf("n=%ld B=%ld eps=%.3f  KP=%.1f KPR=%.1f  WJ(L=%ld,LB=%ld) rounds=%.2f max=%d depth=%.0f wrong1=%.1f\n",
           n,B,eps,sd/reps,sD/reps,L,LB,sr/reps,rmax,(sr/reps)*(L+LB),sw/reps);
  } else {
    for(int f=5;f<argc;f++){
      FILE *fh=fopen(argv[f],"rb"); int32_t n32; if(fread(&n32,4,1,fh)!=1) return 1; long n=n32;
      int *j=malloc((n+1)*sizeof(int)); int32_t *buf=malloc(n*4);
      if(fread(buf,4,n,fh)!=(size_t)n) return 1; fclose(fh);
      j[0]=0; for(long i=1;i<=n;i++) j[i]=buf[i-1];
      char *x=malloc(n+1); x[0]=1; for(long i=1;i<=n;i++) x[i]=(x[i-1]==0 && x[j[i]]==0);
      int md,mD; depths(n,j,x,&md,&mD); long w1; int r=wjacobi(n,j,x,&w1);
      const char *nm=strrchr(argv[f],'/'); nm=nm? nm+1 : argv[f];
      printf("%-24s n=%-7ld KP=%d KPR=%d  WJ(L=%ld,LB=%ld) rounds=%d%s depth=%ld wrong1=%ld\n",
             nm,n,md,mD,L,LB,r>MAXR?MAXR:r,r>MAXR?"+ (not certified)":"",(long)(r>MAXR?MAXR:r)*(L+LB),w1);
      free(j); free(buf); free(x);
    }
  }
  return 0;
}
