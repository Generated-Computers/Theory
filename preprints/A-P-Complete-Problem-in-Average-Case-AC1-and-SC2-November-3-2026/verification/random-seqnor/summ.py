import sys, glob, math, collections, statistics, re
rows=collections.defaultdict(list); rounds=collections.defaultdict(list); NB=collections.defaultdict(list)
for fn in glob.glob(sys.argv[1]+"/runs/*.txt"):
    e=int(re.search(r'n(\d+)_',fn).group(1)); L=open(fn).read().split("\n")
    pts=[tuple(float(v) for v in l.split()) for l in L if l and not l.startswith("#")]
    for l in L:
        if l.startswith("# rounds"): rounds[e].append(int(l.split()[2]))
    for a,b in zip(pts,pts[1:]):
        f,f2=a[1],b[1]
        if f>=64: rows[int(math.log2(f))].append(math.log(f2/f))
    for p in pts:
        if p[1]>=1024 and 1.25*p[1]<=2**e: NB[int(math.log2(p[1]))].append((p[2],p[3]*p[3]/p[1]))
print("log2 n : rounds (per seed)  mean  mean/log2 n")
for e in sorted(rounds): print(f"{e:5d} : {sorted(rounds[e])}  {statistics.mean(rounds[e]):.1f}  {statistics.mean(rounds[e])/e:.3f}")
print("\nlog2 f : #steps  mean ln(f_{t+1}/f_t)  min ratio")
for b in sorted(rows):
    v=rows[b]
    if len(v)>=5: print(f"{b:5d} : {len(v):4d}  {statistics.mean(v):.3f}  {math.exp(min(v)):.3f}")
print("\nlog2 f : window sources N_t (mean, max)   M^2/f (mean, max)")
for b in sorted(NB):
    v=NB[b]
    if len(v)>=3: print(f"{b:5d} : {statistics.mean(x for x,_ in v):5.1f} {max(x for x,_ in v):4.0f}    {statistics.mean(y for _,y in v):.4f} {max(y for _,y in v):.4f}")
