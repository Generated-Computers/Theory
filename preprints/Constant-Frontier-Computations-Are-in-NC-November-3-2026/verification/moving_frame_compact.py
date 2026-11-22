# Checks: moving-frame sparse events (doc #26, W.3-W.6, W.9) and compact-frontier graph (C.1-C.4).
import random, itertools
rng=random.Random(7)
def compose(p,q): return tuple(p[q[i]] for i in range(len(q)))  # p∘q
def inv(p):
    r=[0]*len(p)
    for i,v in enumerate(p): r[v]=i
    return tuple(r)
def moving_frame(n,Gs,Es,x0):
    m=len(Gs); P=[tuple(range(n))]
    for t in range(m): P.append(compose(Gs[t],P[-1]))
    events=[]
    for t in range(1,m+1):
        Pi=inv(P[t])
        for u,v in Es[t-1].items():
            events.append((t,Pi[u],Pi[v]))
    # successor: earliest later event whose source is v
    bysrc={}
    for e in events: bysrc.setdefault(e[1],[]).append(e)
    def first_after(pt,t):
        c=[e for e in bysrc.get(pt,[]) if e[0]>t]
        return min(c) if c else None
    y0=P[0].index(x0) if False else inv(P[0])[x0]
    chain=[]; e=first_after(y0,0)
    while e: chain.append(e); e=first_after(e[2],e[0])
    y=[y0]*(m+1); 
    for (t,u,v) in chain:
        for s in range(t,m+1): y[s]=v
    return [P[t][y[t]] for t in range(m+1)]
for trial in range(3000):
    n=rng.randrange(2,8); m=rng.randrange(0,25)
    Gs=[tuple(rng.sample(range(n),n)) for _ in range(m)]
    Es=[]
    for _ in range(m):
        k=rng.randrange(0,3); dom=rng.sample(range(n),min(k,n)); E={}
        for u in dom:
            v=rng.randrange(n)
            if v!=u: E[u]=v
        Es.append(E)
    x0=rng.randrange(n); x=[x0]
    for t in range(m): z=Gs[t][x[-1]]; x.append(Es[t].get(z,z))
    assert moving_frame(n,Gs,Es,x0)==x
print("moving frame ok")
# W.9 cycle plus transposition, m=2^q
for q in range(1,6):
    M=2**q
    for trial in range(300):
        R=rng.randrange(0,30); word=[rng.choice('ct') for _ in range(R)]; x0=rng.randrange(M)
        x=[x0]
        for g in word:
            z=x[-1]
            if g=='c': x.append((z+1)%M)
            else: x.append(1 if z==0 else 0 if z==1 else z)
        # moving frame with explicit records
        r=0; rs=[0]; recs=[]
        for t,g in enumerate(word,1):
            if g=='c': r=(r+1)%M
            else: recs.append((t,(-r)%M,(1-r)%M)); recs.append((t,(1-r)%M,(-r)%M))
            rs.append(r)
        y=x0; ys=[y]; 
        for t in range(1,R+1):
            for (tt,u,v) in recs:
                if tt==t and u==y: y=v; break
            ys.append(y)
        assert [(ys[t]+rs[t])%M for t in range(R+1)]==x
print("cycle+transposition ok")
# compact-frontier graph
BOT='bot'
def run(p,w,phi,Hin,C0,N):
    m=len(Hin); C=[C0]; addr=[None]
    for t in range(1,N+1):
        a=p[C[t-1]]; addr.append(a)
        if a<m: h=Hin[a]
        elif m<=a<m+t-1: h=w[C[a-m]]   # cell m+s-1 written at stage s holds w(C_{s-1})
        else: h=BOT
        C.append(phi[(C[t-1],h)])
    return C,addr
def frontier(addr,m,a,b):
    # internal cells written at stages s in (a,b]; last use within (a,b]
    best=0
    for t in range(a,b+1):
        live=0
        for s in range(a+1,t+1):
            cell=m+s-1
            last=max([i for i in range(a+1,b+1) if addr[i]==cell]+[s])
            if t<last: live+=1
        best=max(best,live)
    return best
def compact_reach(p,w,phi,Hin,C,a,h,f):
    m=len(Hin)
    start=(C[a],frozenset())
    layer={start}; reach=[True]
    for t in range(h):   # build layer t+1 from layer t ; stage a+t+1
        nxt=set()
        stage=a+t+1
        for (c,D) in layer:
            ad=p[c]
            if ad<m: hv=Hin[ad]
            elif m<=ad<m+a: hv=w[C[ad-m]]   # external (written at stage <=a)
            elif m+a<=ad<m+stage-1:
                s=ad-m+1; Dd=dict(D)
                if s not in Dd: continue
                hv=Dd[s]
            else: hv=BOT
            c2=phi[(c,hv)]; new=dict(D); new[stage]=w[c]
            items=list(new.items())
            for k in range(0,min(f,len(items))+1):
                for sub in itertools.combinations(items,k):
                    nxt.add((c2,frozenset(sub)))
        layer=nxt; reach.append(bool(layer))
        if layer: assert len(set(c for c,_ in layer))==1 and next(iter(layer))[0]==C[a+t+1]
        if not layer: break
    reach+= [False]*(h+1-len(reach))
    return reach
for trial in range(400):
    ns=rng.randrange(2,5); nw=rng.randrange(1,3); m=rng.randrange(1,3); N=rng.randrange(1,12)
    p={c: rng.randrange(0,m+N+2) for c in range(ns)}; w={c: rng.randrange(nw) for c in range(ns)}
    phi={(c,h): rng.randrange(ns) for c in range(ns) for h in list(range(nw))+[BOT]}
    Hin=[rng.randrange(nw) for _ in range(m)]; C0=rng.randrange(ns)
    C,addr=run(p,w,phi,Hin,C0,N)
    a=rng.randrange(0,N); h=N-a
    for f in range(0,3):
        reach=compact_reach(p,w,phi,Hin,C,a,h,f)
        for t in range(h+1):
            assert reach[t]==(frontier(addr,m,a,a+t)<=f), (trial,a,t,f)
print("compact frontier ok")
