# Check Def. 2.1 / Thm 2.2 of manuscript 010e (synchronous correction on the copy program).
def chi(d,L,a,m):
    # absolute stages a+1..a+m; real values all 1; cell written at stage s holds v_{s-1}
    def read_writer(t):  # stage t reads v_{t-d}: initial if t<=d else writer t-d+1
        return None if t<=d else t-d+1
    g={t:0 for t in range(a+1,a+m+1)}; r=0
    while True:
        val={a:1}
        for t in range(a+1,a+m+1):
            s=read_writer(t)
            if s is None or s<=a+1: h=1
            elif t-s+1<=L: h=val[s-1]
            else: h=g[t]
            val[t]=h
        if all(val[t]==1 for t in range(a+1,a+m+1)): return r
        for t in range(a+1,a+m+1):
            s=read_writer(t)
            if s is not None and s>a+1 and t-s+1>L: g[t]=val[s-1]
        r+=1
for L in range(0,5):
    d=L+1
    if d<2: continue
    for N in range(1,40):
        best=None
        for B in range(L+1,max(N,L+1)+2):
            for sig in range(B):
                cuts=sorted(set([0]+[c for c in range(1,N) if c%B==sig]+[N]))
                tot=sum(chi(d,L,cuts[i],cuts[i+1]-cuts[i])+1 for i in range(len(cuts)-1))
                for i in range(len(cuts)-1):
                    m=cuts[i+1]-cuts[i]; assert chi(d,L,cuts[i],m)==-(-m//d)-1
                best=tot if best is None else min(best,tot)
        assert best==-(-N//d),(L,N,best)
print("correction rank ok")
