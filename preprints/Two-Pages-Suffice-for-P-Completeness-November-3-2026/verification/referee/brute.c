/* reads lines "a b page" ; prints number of same-page crossing pairs, checking ALL pairs */
#include <stdio.h>
#include <stdlib.h>
int main(int argc,char**argv){FILE*f=fopen(argv[1],"r");int cap=1<<20,n=0;int*A=malloc(cap*4),*B=malloc(cap*4),*P=malloc(cap*4);
while(fscanf(f,"%d %d %d",&A[n],&B[n],&P[n])==3){n++;if(n==cap){cap*=2;A=realloc(A,cap*4);B=realloc(B,cap*4);P=realloc(P,cap*4);}}
long long bad=0,pairs=0;for(int x=0;x<n;x++)for(int y=x+1;y<n;y++){if(P[x]!=P[y])continue;pairs++;int a=A[x],b=B[x],c=A[y],e=B[y];
if((a<c&&c<b&&b<e)||(c<a&&a<e&&e<b))bad++;}
printf("%d %lld %lld\n",n,pairs,bad);return 0;}
