import sys, glob, math, statistics
v=[]
for fn in glob.glob(sys.argv[1]+"/runs2/*.txt"):
    for l in open(fn):
        if l.startswith("#") or not l.strip(): continue
        t,f,N,M,r,m0,W=l.split(); f=int(f)
        if int(t)>0 and f>=256: v.append((f,int(m0)/math.sqrt(f),int(W)/math.sqrt(f)))
v.sort()
print("rounds with f>=256:", len(v))
a=[x for _,x,_ in v]; w=[y for *_,y in v]
print(f"m0/sqrt(f): mean {statistics.mean(a):.2f}  median {statistics.median(a):.2f}  max {max(a):.2f}   P(>2) {sum(x>2 for x in a)/len(a):.3f}  P(>3) {sum(x>3 for x in a)/len(a):.3f}")
print(f"W/sqrt(f) (prev-round mass in [f,1.25f)): mean {statistics.mean(w):.2f} median {statistics.median(w):.2f} max {max(w):.2f}")
for lo,hi in ((2**8,2**12),(2**12,2**16),(2**16,2**20),(2**20,2**25)):
    s=[(x,y) for f,x,y in v if lo<=f<hi]
    if s: print(f"f in [2^{int(math.log2(lo))},2^{int(math.log2(hi))}): n={len(s):3d}  mean m0/sqrt f {statistics.mean(x for x,_ in s):.2f}  max {max(x for x,_ in s):.2f}   mean W/sqrt f {statistics.mean(y for _,y in s):.2f}")
