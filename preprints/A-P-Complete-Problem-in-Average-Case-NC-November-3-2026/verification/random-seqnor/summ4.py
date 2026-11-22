import sys, glob, math, statistics, collections
D=collections.defaultdict(dict)
for fn in glob.glob(sys.argv[1]+"/runs3/*.txt"):
    for l in open(fn):
        if not l.startswith("W"): continue
        _,t,f,lv,p,w=l.split(); D[(fn,int(t))][int(lv)]=(int(f),int(p),int(w))
rows=collections.defaultdict(list); inv=collections.defaultdict(list); win=collections.defaultdict(list)
for key,lv in D.items():
    for l,(f,p,w) in lv.items():
        if f<2**14: continue
        rows[l].append(math.log(max(p,1))/math.log(f))
        win[l].append(w/max(p,1))
        if l+1 in lv and p>0:
            f2,p2,_=lv[l+1]; inv[l].append(p2*p2/(f*p))
print("depth l | log p_l / log f (mean, max) | target 1-2^-l | inverse ratio p_{l+1}^2/(f p_l) (median, max) | window/pre ratio w_l/p_l (median, max)")
for l in sorted(rows):
    a=rows[l]; b=inv.get(l,[0]); c=win[l]
    print(f"{l:5d}  | {statistics.mean(a):.3f} {max(a):.3f} | {1-2**-l:.3f} | {statistics.median(b):7.3f} {max(b):8.3f} | {statistics.median(c):.3f} {max(c):.3f}   (n={len(a)})")
