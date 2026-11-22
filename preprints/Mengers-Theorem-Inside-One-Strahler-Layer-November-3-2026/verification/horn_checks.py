"""Checks for 005d (rank-layer reachability lemma, unary-spine Menger) and 005c (the monotone
rank-layer operator).  Random Horn systems with rules of arity <= 2, Strahler proof rank."""
import random, itertools
INF = 10**9

def h(a, b):
    return max(a, b) if a != b else a + 1

def min_ranks(N, axioms, unary, binary):
    r = [INF]*N
    for a in axioms: r[a] = 0
    changed = True
    while changed:
        changed = False
        for (f, g) in unary:
            if r[f] < r[g]: r[g] = r[f]; changed = True
        for (f, g, c) in binary:
            if r[f] < INF and r[g] < INF:
                v = h(r[f], r[g])
                if v < r[c]: r[c] = v; changed = True
    return r

def reach(N, arcs, sources):
    adj = [[] for _ in range(N)]
    for (a, b) in arcs: adj[a].append(b)
    seen = set(sources); st = list(sources)
    while st:
        u = st.pop()
        for v in adj[u]:
            if v not in seen: seen.add(v); st.append(v)
    return seen

def layer_graph(N, unary, binary, below):
    arcs = list(unary)
    for (f, g, c) in binary:
        if g in below: arcs.append((f, c))
        if f in below: arcs.append((g, c))
    return arcs

def maxflow_vertex(N, arcs, S, T):
    # node split: v_in = 2v, v_out = 2v+1, source 2N, sink 2N+1
    s, t = 2*N, 2*N+1
    cap = {}
    def add(u, v, c):
        cap[(u, v)] = cap.get((u, v), 0) + c; cap.setdefault((v, u), 0)
    for v in range(N): add(2*v, 2*v+1, 1)
    for (a, b) in arcs: add(2*a+1, 2*b, N+5)
    for v in S: add(s, 2*v, N+5)
    for v in T: add(2*v+1, t, 1)
    adj = {}
    for (u, v) in cap: adj.setdefault(u, []).append(v)
    flow = 0
    while True:
        par = {s: None}; q = [s]
        while q and t not in par:
            u = q.pop(0)
            for v in adj.get(u, []):
                if v not in par and cap[(u, v)] > 0:
                    par[v] = u; q.append(v)
        if t not in par: return flow
        v = t
        while par[v] is not None:
            u = par[v]; cap[(u, v)] -= 1; cap[(v, u)] += 1; v = u
        flow += 1

def min_vertex_cut_bruteforce(N, arcs, S, T):
    for size in range(0, N+1):
        for Hc in itertools.combinations(range(N), size):
            Hs = set(Hc)
            src = [v for v in S if v not in Hs]
            adj = [[] for _ in range(N)]
            for (a, b) in arcs:
                if a not in Hs and b not in Hs: adj[a].append(b)
            seen = set(src); st = list(src)
            while st:
                u = st.pop()
                for v in adj[u]:
                    if v not in seen: seen.add(v); st.append(v)
            if not any(x in seen for x in T if x not in Hs):
                return size

random.seed(7)
n_sys = 0; n_menger = 0
for trial in range(400):
    N = random.randint(6, 12)
    axioms = random.sample(range(N), random.randint(1, 3))
    unary = [(random.randrange(N), random.randrange(N)) for _ in range(random.randint(0, N))]
    unary = [(a, b) for (a, b) in unary if a != b]
    binary = []
    for _ in range(random.randint(1, 2*N)):
        f, g, c = random.sample(range(N), 3)
        binary.append((f, g, c))
    r = min_ranks(N, axioms, unary, binary)
    K = max([x for x in r if x < INF] + [0])
    for k in range(1, K+2):
        below = {v for v in range(N) if r[v] < k}
        upto = {v for v in range(N) if r[v] <= k}
        seeds = {c for (f, g, c) in binary if r[f] == k-1 and r[g] == k-1 and r[c] >= k}
        arcs = layer_graph(N, unary, binary, below)
        R = reach(N, arcs, seeds)
        assert upto == below | R, (trial, k)
        # monotone operator Phi(X) = Reach_{G(X)}(X u Seeds(X)), Seeds(X)= binary concl. with premises in X
        seedsX = {c for (f, g, c) in binary if f in below and g in below}
        assert reach(N, arcs, below | seedsX) == upto
        # Menger: targets = random subset of facts of rank exactly k
        Tk = [v for v in range(N) if r[v] == k]
        if Tk and N <= 10:
            T = random.sample(Tk, random.randint(1, len(Tk)))
            p = maxflow_vertex(N, arcs, seeds, T)
            c = min_vertex_cut_bruteforce(N, arcs, seeds, T)
            assert p == c, (p, c)
            n_menger += 1
    n_sys += 1
print("rank-layer reachability lemma and monotone layer operator: OK on", n_sys, "systems")
print("vertex Menger (max flow == brute-force min vertex cut):", n_menger, "instances OK")
