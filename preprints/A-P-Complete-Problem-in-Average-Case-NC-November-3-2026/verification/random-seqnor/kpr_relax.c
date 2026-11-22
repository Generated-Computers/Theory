// Depth of the relevance-pruned iteration (min over anchors) and three max-relaxations (Remark rem:kpr).
//   kp   : Kleene-prefix depth d: any reset sets the level, any non-reset non-NOT gate maxes it.
//   last : anchor = last reset of either kind, only relevant non-resets max the level.
//   rel  : anchor = last relevant reset, irrelevant resets ignored, relevant non-resets max.
//   kpr  : relevant reset sets, irrelevant reset mins, relevant non-reset maxes (Lemma kpr-switch (a)).
// usage: kpr_relax FAMILY n eps samples seed     FAMILY: fixC | spreadD | log | lgu | zero | half
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
static uint64_t s0, s1;
static inline uint64_t rnd(void){uint64_t a=s0,b=s1;s0=b;a^=a<<23;s1=a^b^(a>>17)^(b>>26);return s1+b;}
static double U(void){return (rnd()>>11)*(1.0/9007199254740992.0);}
static uint64_t hsh(uint64_t z){z+=0x9E3779B97F4A7C15ULL;z=(z^(z>>30))*0xBF58476D1CE4E5B9ULL;z=(z^(z>>27))*0x94D049BB133111EBULL;return z^(z>>31);}
int main(int argc,char**argv){
  const char*f=argv[1]; long n=atol(argv[2]); double e=atof(argv[3]); int T=atoi(argv[4]); s0=atoll(argv[5])*7+1; s1=99; for(int i=0;i<20;i++)rnd();
  long*j=malloc((n+1)*sizeof*j); unsigned char*x=malloc(n+1); int*d[4]; for(int a=0;a<4;a++)d[a]=malloc((n+1)*sizeof(int));
  double mean[4]={0};
  for(int t=0;t<T;t++){
    j[1]=0; for(long i=2;i<=n;i++){ long v;
      if(!strncmp(f,"fix",3)) v=i-atol(f+3); else if(!strncmp(f,"spread",6)){long D=atol(f+6); v=i-D-(long)(hsh(i)%D);}
      else if(!strcmp(f,"log")) v=i-1-(long)log((double)i); else if(!strcmp(f,"lgu")){double u=(hsh(i)>>11)*(1.0/9007199254740992.0); v=i-1-(long)pow((double)i,u);}
      else if(!strcmp(f,"zero")) v=0; else v=i/2;
      if(v<0)v=0; if(v>i-2)v=i-2; j[i]=(U()<e)?(long)(rnd()%(uint64_t)i):v; }
    x[0]=1; for(long i=1;i<=n;i++) x[i]=!(x[i-1]|x[j[i]]);
    int m[4]={0,0,0,0}, mx[4]={0,0,0,0}; for(int a=0;a<4;a++) d[a][0]=0;
    for(long i=1;i<=n;i++){ long q=j[i]; int isnot=(q==i-1), hit=!isnot&&x[q], rel=!x[i-1];
      for(int a=0;a<4;a++){ int dq=d[a][q];
        if(a==0){ if(hit) m[a]=dq; else if(!isnot && dq>m[a]) m[a]=dq; }
        else if(a==1){ if(hit) m[a]=dq; else if(rel&&!isnot&&dq>m[a]) m[a]=dq; }
        else if(a==2){ if(hit&&rel) m[a]=dq; else if(rel&&!isnot&&!hit&&dq>m[a]) m[a]=dq; }
        else { if(hit&&rel) m[a]=dq; else if(hit){ if(dq<m[a]) m[a]=dq; } else if(rel&&!isnot&&dq>m[a]) m[a]=dq; }
        d[a][i]=1+m[a]; if(d[a][i]>mx[a]) mx[a]=d[a][i]; } }
    for(int a=0;a<4;a++) mean[a]+=mx[a];
  }
  printf("%-9s n=2^%-2d eps=%.2f  kp=%8.1f  last=%8.1f  rel=%8.1f  kpr=%7.1f\n",f,(int)lround(log2((double)n)),e,mean[0]/T,mean[1]/T,mean[2]/T,mean[3]/T);
}
