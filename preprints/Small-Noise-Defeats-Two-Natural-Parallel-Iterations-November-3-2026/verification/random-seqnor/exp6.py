import sys, random, statistics, math
sys.path.insert(0, sys.argv[1]); from core import *
def peel_rounds(j):
    n=len(j); xs=truth(j); val=[None]*(n+1); val[0]=1; r=0; unknown=n
    while unknown:
        r+=1; new={}
        for i in range(1,n+1):
            if val[i] is not None: continue
            a,b=val[i-1],val[j[i-1]]
            if a==1 or b==1: new[i]=0
            elif a==0 and b==0: new[i]=1
        for i,v in new.items(): val[i]=v
        unknown-=len(new)
    assert val==xs
    return r
random.seed(5)
print("n | Newton from (1,0..0) | Newton from random start | peeling rounds")
for n in (1024, 4096, 16384, 65536):
    T=6 if n<65536 else 2
    a=[];b=[];c=[]
    for _ in range(T):
        j=rand_j(n)
        a.append(len(trajectory(j)[1])-1)
        x0=[1]+[random.randint(0,1) for _ in range(n)]
        b.append(len(trajectory(j,x0)[1])-1)
        c.append(peel_rounds(j))
    print(n, statistics.mean(a), statistics.mean(b), statistics.mean(c), "  sqrt n =", int(math.sqrt(n)))
