# Checks for identity padding (doc #26, S.2, S.4): GF(2) Newton on affine-product circuits.
import random, itertools
# gate: ('const',c) | ('aff',c,[parents]) | ('prod',p,q)
def evaluate(G):
    x=[]
    for g in G:
        if g[0]=='const': x.append(g[1])
        elif g[0]=='aff': x.append((g[1]+sum(x[j] for j in g[2]))%2)
        else: x.append(x[g[1]]*x[g[2]])
    return x
def newton(G,x):
    n=len(G); F=[]; 
    # residual F_i = x_i + f_i(x); Jacobian rows
    for i,g in enumerate(G):
        if g[0]=='const': f=g[1]
        elif g[0]=='aff': f=(g[1]+sum(x[j] for j in g[2]))%2
        else: f=x[g[1]]*x[g[2]]
        F.append((x[i]+f)%2)
    # solve J delta = F by forward substitution: delta_i = F_i + sum_j dfi/dxj delta_j
    d=[0]*n
    for i,g in enumerate(G):
        s=F[i]
        if g[0]=='aff':
            for j in g[2]: s^=d[j]
        elif g[0]=='prod':
            p,q=g[1],g[2]; s^=(x[q]*d[p])^(x[p]*d[q])
        d[i]=s
    return [(x[i]+d[i])%2 for i in range(n)]
def ranks(G):
    r=[]
    for g in G:
        if g[0]=='const': r.append(0)
        elif g[0]=='aff': r.append(max([r[j] for j in g[2]],default=0))
        else:
            a,b=sorted([r[g[1]],r[g[2]]],reverse=True); r.append(a if a>b else a+1)
    return r
# S.2 ladder
for k in range(1,12):
    G=[('const',1)]; zprev=0; idx={}
    for l in range(1,k+1):
        G.append(('aff',0,[zprev])); s=len(G)-1
        G.append(('aff',0,[zprev])); d=len(G)-1
        G.append(('prod',s,d)); z=len(G)-1
        idx[l]=(s,d,z); zprev=z
    xstar=evaluate(G); x=[1]+[0]*(len(G)-1)
    t=0; first=None
    while True:
        for l,(s,d,z) in idx.items():
            assert (x[s]==1)==(l<=t) and (x[d]==1)==(l<=t), (k,t,l)
            assert (x[z]==1)==(l<t), (k,t,l)
        if x[idx[k][2]]==xstar[idx[k][2]] and first is None: first=t
        if t>k+2: break
        x=newton(G,x); t+=1
    assert first==k+1, (k,first)
    assert ranks(G)[idx[k][2]]==k
print("S.2 ladder delay ok (k<=11)")
# Newton-Strahler upper bound on random circuits (sanity)
rng=random.Random(5)
for trial in range(2000):
    n=rng.randrange(2,25); G=[('const',rng.randrange(2))]
    for i in range(1,n):
        if rng.random()<0.5 and i>=2:
            p,q=rng.sample(range(i),2); G.append(('prod',p,q))
        else:
            ps=rng.sample(range(i),rng.randrange(1,min(i,3)+1)); G.append(('aff',rng.randrange(2),ps))
    xs=evaluate(G); rk=ranks(G); x=[rng.randrange(2) for _ in G]
    for t in range(max(rk)+2):
        for i in range(n):
            if rk[i]<t: assert x[i]==xs[i]
        x=newton(G,x)
print("Newton-Strahler bound ok on random circuits")
# S.4 padding: rank and frontier on padded circuits
def frontier_width(G,rk,outputs):
    n=len(G); children=[[] for _ in G]
    for i,g in enumerate(G):
        if g[0]=='aff':
            for j in g[2]: children[j].append(i)
        elif g[0]=='prod': children[g[1]].append(i); children[g[2]].append(i)
    best=0
    for k in range(max(rk)+1):
        L=set(v for v in range(n) if rk[v]<=k and G[v][0]!='const' and any(rk[c]>k for c in children[v]))
        L|=set(o for o in outputs if rk[o]<=k)
        best=max(best,len(L))
    return best
for w in [1,2,4,8]:
    for k in [1,3,6]:
        base=[('const',1),('const',0),('prod',0,1)]  # y = gate 2 (value 0) ; try also value 1
        for yv in [0,1]:
            G=[('const',1),('const',yv),('prod',0,1)]; y=2
            outs=[]
            for j in range(w):
                z=y
                for l in range(k):
                    G.append(('aff',0,[z])); s=len(G)-1; G.append(('aff',0,[z])); d=len(G)-1
                    G.append(('prod',s,d)); z=len(G)-1
                outs.append(z)
            layer=outs
            while len(layer)>1:
                nl=[]
                for i in range(0,len(layer),2):
                    G.append(('prod',layer[i],layer[i+1])); nl.append(len(G)-1)
                layer=nl
            root=layer[0]; xs=evaluate(G); rk=ranks(G)
            assert xs[root]==xs[y]
            assert rk[root]>=rk[y]+k
            fw=frontier_width(G,rk,[root])
            assert fw>=2*w, (w,k,fw)
print("S.4 padding: output preserved, rank>=k, frontier>=2w ok")
