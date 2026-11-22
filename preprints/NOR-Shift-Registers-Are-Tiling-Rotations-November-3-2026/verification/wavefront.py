# Exhaustive checks of the homogeneous sweep-map statements (doc #26, App. D.2-D.6).
import itertools
def sweep(G, x):
    D=len(x); y=[0]*D; prev=x[-1]
    for s in range(D):
        prev=G(prev,x[s]); y[s]=prev
    return tuple(y)
NOR=lambda u,v: 1-(u|v)
def inT(w):
    n=len(w)
    for i in range(n):
        if w[i]&w[(i+1)%n]: return False
        if (1-w[i])&(1-w[(i+1)%n])&(1-w[(i+2)%n]): return False
    return True
gates={}
for tt in itertools.product([0,1],repeat=4):
    gates[tt]=(lambda tt: (lambda u,v: tt[2*u+v]))(tt)
def affine(tt):
    # tt[2u+v]; affine iff tt(0,0)^tt(0,1)^tt(1,0)^tt(1,1)==0
    return (tt[0]^tt[1]^tt[2]^tt[3])==0
for D in range(1,15):
    xs=list(itertools.product([0,1],repeat=D))
    # NOR: landing, extension, rotation
    T=[w for w in itertools.product([0,1],repeat=D+1) if inT(w)]
    piT=set(w[1:] for w in T)
    assert len(piT)==len(T), ("pi not injective",D)
    land=all(sweep(NOR,sweep(NOR,x)) in piT for x in xs)
    rot=all(sweep(NOR,w[1:])==(w[-1],)+w[:-1] [1:] for w in T)  # pi(rho(w)) = (w0..w_{D-1})
    rot=all(sweep(NOR,w[1:])==w[:-1] for w in T)
    ext=all(w[0]==1-(w[-1]|w[1%len(w)]) for w in T) if D>=2 else None
    # extension bit from z0=y_D agrees?
    ok_z0=True
    for x in xs:
        y=sweep(NOR,x); z=sweep(NOR,y)
        if D>=2 and (y[-1],)+z not in set(T): ok_z0=False
    # orbit preperiod/period
    per=True
    for x in xs:
        z=sweep(NOR,sweep(NOR,x)); u=z
        for _ in range(D+1): u=sweep(NOR,u)
        if u!=z: per=False
    # max preperiod exactly
    maxpre=0
    for x in xs:
        seen={}; u=x; k=0
        while u not in seen: seen[u]=k; u=sweep(NOR,u); k+=1
        maxpre=max(maxpre,seen[u])
    # other nonaffine gates
    res=[]
    for tt,G in gates.items():
        if affine(tt): continue
        # number of sweeps after which row is fixed, max over x, unless NOR/NAND
        mx=0
        for x in xs:
            seen={}; u=x; k=0
            while u not in seen: seen[u]=k; u=sweep(G,u); k+=1
            mx=max(mx,seen[u])
        # period
        res.append((tt,mx))
    print(D,"land",land,"rot",rot,"ext",ext,"z0ext",ok_z0,"period|D+1 after 2",per,"maxpre",maxpre,"nonaffine maxpre",res)
