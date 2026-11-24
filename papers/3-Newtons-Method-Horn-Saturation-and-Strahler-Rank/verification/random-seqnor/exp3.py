import sys, random, math, statistics
sys.path.insert(0, sys.argv[1]); from core import *
random.seed(int(sys.argv[3]))
n=int(sys.argv[2]); out=[]
for inst in range(int(sys.argv[4])):
    j=rand_j(n); xs,tr=trajectory(j)
    for t in range(len(tr)-1):
        x=tr[t]; e=[x[i]^xs[i] for i in range(n+1)]; f=e.index(1)
        y=tr[t+1]; e2=[y[i]^xs[i] for i in range(n+1)]
        f2=e2.index(1) if 1 in e2 else n+1
        M2=sum(e[f:min(2*f,n+1)]); M12=sum(e[f:min(int(1.25*f)+1,n+1)])
        out.append((f,f2,M2,M12,2*f<=n))
    print("inst",inst,"rounds",len(tr)-1, flush=True)
# bucket by f
import collections
B=collections.defaultdict(list)
for f,f2,M2,M12,full in out:
    if f>=4 and f2<=n: B[int(math.log2(f))].append((math.log(f2/f), f2>1.25*f, f2>2*f, M2/math.sqrt(f), M12/math.sqrt(f)))
print("log2 f | count | mean ln(ratio) | P(ratio>1.25) | P(ratio>2) | median M(2)/sqrt f | median M(1.25)/sqrt f")
for b in sorted(B):
    v=B[b]
    if len(v)<4: continue
    print(f"{b:6d} | {len(v):5d} | {statistics.mean(a for a,*_ in v):.3f} | {statistics.mean(p for _,p,*_ in v):.2f} | {statistics.mean(q for _,_,q,*_ in v):.2f} | {statistics.median(m for *_,m,_ in v):.2f} | {statistics.median(m for *_,m in v):.2f}")
