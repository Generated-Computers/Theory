import sys, glob, math, statistics
r=[]
for fn in glob.glob(sys.argv[1]+"/runs2/*.txt"):
    for l in open(fn):
        if l.startswith("#") or not l.strip(): continue
        t,f,N,M,ra,m0,W=l.split(); f,N,M,m0,W=int(f),int(N),int(M),int(m0),int(W)
        if int(t)>0 and f>=4096:
            comp=(m0+W)*W/f          # compensator bound for previous-round sources in the window
            r.append((f,N,comp,M))
print("rounds with f>=4096:", len(r))
print("window sources N vs bound (m0+W)W/f :  mean N", round(statistics.mean(x[1] for x in r),2), " mean bound", round(statistics.mean(x[2] for x in r),2), " mean ratio N/bound", round(statistics.mean(x[1]/x[2] for x in r if x[2]>0),3))
print("round-t window mass M vs sources N   :  mean M/N", round(statistics.mean(x[3]/x[1] for x in r if x[1]>0),2), " max", round(max(x[3]/x[1] for x in r if x[1]>0),2))
print("squaring constant K = M / (W(m0+W)/f): median", round(statistics.median(x[3]/x[2] for x in r if x[2]>0),2), " 90th pct", round(sorted(x[3]/x[2] for x in r if x[2]>0)[int(.9*len(r))],2))
