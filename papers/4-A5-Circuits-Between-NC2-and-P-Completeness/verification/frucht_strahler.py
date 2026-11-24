import itertools, random
from collections import Counter
# ---------------- Frucht graph via LCF notation ----------------
lcf=[-5,-2,-4,2,5,-2,2,5,-2,-5,4,2]
n=12
E=set()
for i in range(n):
    E.add(frozenset((i,(i+1)%n)))
    E.add(frozenset((i,(i+lcf[i])%n)))
E=[tuple(sorted(e)) for e in E]
adj={i:set() for i in range(n)}
for u,v in E: adj[u].add(v); adj[v].add(u)
print('Frucht: vertices',n,'edges',len(E),'degrees',set(len(adj[i]) for i in range(n)))
# automorphisms by backtracking
auts=0
def extend(mp):
    global auts
    if len(mp)==n: auts+=1; return
    i=len(mp)
    for c in range(n):
        if c in mp.values(): continue
        if len(adj[c])!=len(adj[i]): continue
        if all(((j in adj[i])==(mp[j] in adj[c])) for j in mp):
            mp[i]=c; extend(mp); del mp[i]
extend({})
print('Frucht automorphism group order:', auts)
# color refinement on incidence graph
V=list(range(n)); En=list(range(n,n+len(E)))
iadj={x:set() for x in V+En}
for k,(u,v) in enumerate(E):
    iadj[n+k]|={u,v}; iadj[u].add(n+k); iadj[v].add(n+k)
col={x:(0 if x<n else 1) for x in iadj}
rounds=0
while True:
    sig={x:(col[x],tuple(sorted(Counter(col[y] for y in iadj[x]).items()))) for x in iadj}
    keys={s:i for i,s in enumerate(sorted(set(sig.values())))}
    new={x:keys[sig[x]] for x in iadj}
    rounds+=1
    if len(set(new.values()))==len(set(col.values())): break
    col=new
print('incidence graph: stable color classes', Counter(col.values()), 'after', rounds, 'round(s)')
# also: plain color refinement on G itself (uniform start) is stable with one class (regular graph)
# ---------------- C_q orbits on D^q (Burnside) ----------------
from math import gcd
def orbits(d,q): return sum(d**gcd(k,q) for k in range(q))//q
print('C_q orbit counts >= d^q/q:', all(orbits(d,q)*q>=d**q for d in range(2,6) for q in range(1,12)))
# ---------------- Strahler compiler checks ----------------
def rand_circuit(nin, ngates, D):
    preds=[]; funcs=[]
    for g in range(ngates):
        k=random.choice([1,2,2,2])
        ps=[random.randrange(nin+g) for _ in range(k)]
        preds.append(ps)
        funcs.append({t:random.randrange(D) for t in itertools.product(range(D),repeat=k)})
    return preds, funcs
def evaluate(nin, preds, funcs, inp):
    val=list(inp)
    for g,ps in enumerate(preds):
        val.append(funcs[g][tuple(val[p] for p in ps)])
    return val
def ranks_rec(nin,preds):
    rk=[0]*nin
    for g,ps in enumerate(preds):
        P=sorted(set(ps), key=lambda x:-rk[x])
        r1=rk[P[0]]
        rk.append(r1+1 if len(P)>1 and rk[P[1]]==r1 else r1)
    return rk
def ranks_phase(nin,preds):
    N=nin+len(preds)
    PP=[[]]*nin+[sorted(set(ps)) for ps in preds]
    rk=[None]*N
    for i in range(nin): rk[i]=0
    known_lower=set()  # vertices with rank < k determined
    k=0
    while any(r is None for r in rk) or k==0:
        # vertices not in R_{<k}
        notlow=[v for v in range(N) if v not in known_lower]
        B={v for v in notlow if v>=nin and sum(1 for u in PP[v] if u not in known_lower)>=2}
        # rank>=k+1 iff some ancestor-or-self in B (ancestors among all vertices)
        hi=set()
        for v in range(N):
            if v in B or any(u in hi for u in PP[v]): hi.add(v)
        for v in notlow:
            if v not in hi: rk[v]=k if rk[v] is None else rk[v]
        known_lower|={v for v in notlow if v not in hi}
        k+=1
        if len(known_lower)==N: break
    return rk
def leaves(nin,preds):
    L=[1]*nin
    for ps in preds: L.append(sum(L[p] for p in ps))
    return L
def layered_eval(nin,preds,funcs,inp,rk):
    N=nin+len(preds); val=[None]*N
    for i in range(nin): val[i]=inp[i]
    for k in range(max(rk)+1):
        layer=[v for v in range(nin,N) if rk[v]==k]
        # roots: no same-rank predecessor; others: unique same-rank predecessor (parent pointer)
        parent={}
        for v in layer:
            same=[u for u in set(preds[v-nin]) if u>=nin and rk[u]==k] + [u for u in set(preds[v-nin]) if u<nin and k==0]
            assert len(set(same))<=1
            parent[v]=same[0] if same else None
        # unary maps phi_v: value of parent -> value of v (other preds known)
        def phi(v,x):
            ps=preds[v-nin]
            return funcs[v-nin][tuple(x if p==parent[v] else val[p] for p in ps)]
        # evaluate by following parent chain (sequential simulation of pointer jumping)
        def get(v):
            if val[v] is not None: return val[v]
            p=parent[v]
            if p is None:
                val[v]=funcs[v-nin][tuple(val[q] for q in preds[v-nin])]
            else:
                val[v]=phi(v,get(p))
            return val[v]
        for v in sorted(layer): get(v)
    return val
random.seed(3)
okr=okv=okl=True
for t in range(300):
    nin=random.randint(1,4); ng=random.randint(1,40); D=random.randint(2,4)
    preds,funcs=rand_circuit(nin,ng,D)
    r1=ranks_rec(nin,preds); r2=ranks_phase(nin,preds)
    if r1!=r2: okr=False
    inp=[random.randrange(D) for _ in range(nin)]
    if layered_eval(nin,preds,funcs,inp,r1)!=evaluate(nin,preds,funcs,inp): okv=False
    L=leaves(nin,preds)
    if any(L[v] < 2**r1[v] for v in range(len(r1))): okl=False
print('rank via reachability phases == recursive rank:', okr)
print('layered (rank-by-rank) evaluation correct:', okv)
print('leaves of unfolding >= 2^rank:', okl)
# congruence quotient by earliest representative stays acyclic and value-correct
okq=True
for t in range(200):
    nin=random.randint(1,3); ng=random.randint(2,30); D=2
    preds,funcs=rand_circuit(nin,ng,D)
    inp=[random.randrange(D) for _ in range(nin)]
    val=evaluate(nin,preds,funcs,inp)
    # true congruence: group gates by value, random sub-partition
    cls={}
    for v in range(nin,nin+ng):
        key=(val[v], random.randrange(2))
        cls.setdefault(key,[]).append(v)
    rep={}
    for c in cls.values():
        for v in c: rep[v]=min(c)
    for i in range(nin): rep[i]=i
    qpreds=[[rep[p] for p in preds[g]] for g in range(ng)]
    # acyclic: rep of pred < g's rep? check for representatives only
    for c in cls.values():
        r=min(c)
        if any(p>=r for p in qpreds[r-nin]): okq=False
    # evaluate quotient on representatives in order
    qv=list(inp)+[None]*ng
    for g in range(ng):
        v=nin+g
        if rep[v]==v: qv[v]=funcs[g][tuple(qv[p] for p in qpreds[g])]
    for v in range(nin,nin+ng): qv[v]=qv[rep[v]]
    if qv!=val: okq=False
print('quotient by earliest representatives acyclic and value-preserving:', okq)
