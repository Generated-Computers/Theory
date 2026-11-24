import itertools, random, math
from collections import defaultdict, Counter
random.seed(1)
# ---------- multigraph utilities (edge list) ----------
def core(n_alive, edges):
    # 2-core of multigraph restricted to alive vertex set; returns set of core vertices
    alive=set(n_alive)
    E=[(u,v) for (u,v) in edges if u in alive and v in alive]
    while True:
        deg=Counter()
        for u,v in E:
            deg[u]+=1; deg[v]+=1   # loop counts 2
        rem={x for x in alive if deg[x]<=1}
        if not rem: return alive, E
        alive-=rem
        E=[(u,v) for (u,v) in E if u in alive and v in alive]
def is_forest(alive, edges):
    c,_=core(alive,edges); return len(c)==0
def simple_cycles_vertex_sets(n, edges):
    # all cycles as vertex sets (small graphs) via brute force on subsets: a vertex set S supports a cycle through all of S
    adj=defaultdict(list)
    for i,(u,v) in enumerate(edges): adj[u].append((v,i)); adj[v].append((u,i))
    cycles=set()
    def dfs(start, cur, visited, used_edges):
        for (w,i) in adj[cur]:
            if i in used_edges: continue
            if w==start and len(used_edges)>=0:
                cycles.add(frozenset(visited)); continue
            if w in visited or w<start: continue
            dfs(start, w, visited|{w}, used_edges|{i})
    for s in range(n): dfs(s,s,frozenset([s]),frozenset())
    return [c for c in cycles]
def cp_brute(n, edges):
    cyc=simple_cycles_vertex_sets(n,edges)
    # keep minimal ones
    cyc=sorted(set(cyc), key=len)
    best=0
    def rec(i, used, cnt):
        nonlocal best
        best=max(best,cnt)
        if cnt + (n-len(used))//1 <= best: pass
        for j in range(i,len(cyc)):
            if not (cyc[j] & used):
                rec(j+1, used|cyc[j], cnt+1)
    rec(0,frozenset(),0)
    return best
def bfs_dist(adjK, s, banned_edge=None):
    dist={s:0}; fr=[s]
    while fr:
        nf=[]
        for x in fr:
            for (y,i) in adjK[x]:
                if i==banned_edge: continue
                if y not in dist: dist[y]=dist[x]+1; nf.append(y)
        fr=nf
    return dist
def greedy_fvs(n, edges):
    H=set(); cycles=[]; it=0
    while True:
        alive=set(range(n))-H
        C,E=core(alive,edges)
        if not C: return H, cycles, it
        it+=1
        deg=Counter()
        for u,v in E: deg[u]+=1; deg[v]+=1
        branch={x for x in C if deg[x]>=3}
        # components of core
        adj=defaultdict(list)
        for i,(u,v) in enumerate(E): adj[u].append((v,i)); adj[v].append((u,i))
        # pick a component
        start=min(C); comp={start}; st=[start]
        while st:
            x=st.pop()
            for y,_ in adj[x]:
                if y not in comp: comp.add(y); st.append(y)
        compb=branch & comp
        if not compb:
            H.add(start); cycles.append(frozenset(comp)); continue
        # build kernel: walk suppressed paths
        Kedges=[]; Kpaths=[]; seen_edge=set()
        for b in compb:
            for (y,i) in adj[b]:
                if i in seen_edge: continue
                path=[b]; prev_e=i; cur=y; seen_edge.add(i)
                while cur not in compb:
                    path.append(cur)
                    nxt=[(z,j) for (z,j) in adj[cur] if j!=prev_e]
                    assert len(nxt)==1
                    z,j=nxt[0]; seen_edge.add(j); prev_e=j; cur=z
                path.append(cur)
                Kedges.append((b,cur)); Kpaths.append(path)
        adjK=defaultdict(list)
        for i,(u,v) in enumerate(Kedges): adjK[u].append((v,i)); adjK[v].append((u,i))
        best=None
        for i,(u,v) in enumerate(Kedges):
            if u==v: L=1
            else:
                d=bfs_dist(adjK,u,banned_edge=i)
                if v not in d: continue
                L=d[v]+1
            if best is None or L<best[0]: best=(L,i)
        L,i=best
        u,v=Kedges[i]
        # reconstruct kernel cycle vertex set: edge i plus shortest path u->v avoiding edge i
        if u==v: kverts={u}; lifted=set(Kpaths[i])
        else:
            # BFS with parents
            par={u:None}; fr=[u]
            while fr and v not in par:
                nf=[]
                for x in fr:
                    for (y,j) in adjK[x]:
                        if j==i or y in par: continue
                        par[y]=(x,j); nf.append(y)
                fr=nf
            kverts={v}; lifted=set(Kpaths[i]); x=v
            while par[x] is not None:
                p,j=par[x]; kverts.add(p); lifted|=set(Kpaths[j]); x=p
        assert len(kverts)<=2*math.ceil(math.log2(max(2,len(compb))))+1, (len(kverts),len(compb))
        H|=kverts; cycles.append(frozenset(lifted))
# ---------- test greedy FVS on random small multigraphs ----------
viol=0; tested=0
for trial in range(400):
    n=random.randint(3,11); m=random.randint(n-1, n+6)
    edges=[]
    for _ in range(m):
        u=random.randrange(n); v=random.randrange(n)
        if u==v: continue   # avoid loops for simplicity of brute cycle enumeration
        edges.append((u,v))
    H,cyc,it=greedy_fvs(n,edges)
    assert is_forest(set(range(n))-H, edges)
    for a,b in itertools.combinations(cyc,2): assert not (a&b), 'cycles not disjoint'
    cp=cp_brute(n,edges)
    tested+=1
    if it>cp or len(H)>cp*(2*math.ceil(math.log2(n))+1): viol+=1
print('greedy FVS tests:',tested,'violations',viol)
# ---------- stress family of #30 Thm 1 ----------
def stress(w,R):
    perms=[None]+[random.sample(range(w),w) for _ in range(R)]
    # gates: ('T',k,j),('F',k,j); inputs layer 0
    pred={}
    for k in range(1,R+1):
        for j in range(w):
            pi=perms[k][j]
            pred[('T',k,j)]=[('F',k-1,j),('T',k-1,pi)]   # OR, first child displayed first
            pred[('F',k,j)]=[('F',k-1,j),('T',k-1,pi)]   # AND
    return perms,pred
def escape_rounds(w,R,pred):
    val={}
    for j in range(w): val[('T',0,j)]=1; val[('F',0,j)]=0
    order=[('T',k,j) for k in range(1,R+1) for j in range(w)]+[('F',k,j) for k in range(1,R+1) for j in range(w)]
    order.sort(key=lambda g:g[1])
    for g in order:
        a,b=[val[x] for x in pred[g]]
        val[g]= (a|b) if g[0]=='T' else (a&b)
    assert all(val[('T',k,j)]==1 and val[('F',k,j)]==0 for k in range(R+1) for j in range(w))
    sigma={g:0 for g in pred if g[0]=='T'}  # rank-biased, tie -> first child
    rounds=[]
    while True:
        # losing set: false input reachable in strategy graph
        L={}
        for k in range(R+1):
            for j in range(w):
                for t in 'TF':
                    g=(t,k,j)
                    if k==0: L[g]=(t=='F')
                    elif t=='T': L[g]=L[pred[g][sigma[g]]]
                    else: L[g]=L[pred[g][0]] or L[pred[g][1]]
        esc=[g for g in sigma if L[g] and not L[pred[g][1-sigma[g]]]]
        if not esc: break
        for g in esc: sigma[g]=1-sigma[g]
        rounds.append(sorted(esc))
    return rounds
ok=True
for (w,R) in [(1,1),(2,3),(3,4),(4,5),(5,2)]:
    perms,pred=stress(w,R)
    rounds=escape_rounds(w,R,pred)
    exp=[sorted(('T',k,j) for j in range(w)) for k in range(1,R+1)]
    if rounds!=exp: ok=False
print('stress family escape switching rounds == layers:', ok)
# disjoint diamonds count and Strahler ranks
def strahler(pred, inputs):
    rk={x:0 for x in inputs}
    for g in sorted(pred, key=lambda g:g[1]):
        P=sorted(set(pred[g]), key=lambda x:-rk[x])
        r1=rk[P[0]]
        rk[g]= r1+1 if (len(P)>1 and rk[P[1]]==r1) else r1
    return rk
w,R=4,6; perms,pred=stress(w,R)
inputs=[(t,0,j) for t in 'TF' for j in range(w)]
rk=strahler(pred,inputs)
print('Strahler ranks equal layer index:', all(rk[g]==g[1] for g in pred))
# build wire graph and compute cp brute force for small
idx={}
for g in inputs+list(pred): idx[g]=len(idx)
edges=[(idx[u],idx[g]) for g in pred for u in pred[g]]
print('stress w=4,R=6: vertices',len(idx),'cp (brute) =',cp_brute(len(idx),edges) if len(idx)<=60 else None, 'lower bound w*ceil(R/2)=',w*math.ceil(R/2))
