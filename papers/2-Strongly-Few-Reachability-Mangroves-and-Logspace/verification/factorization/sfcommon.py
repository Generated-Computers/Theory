"""Shared helpers for the computer checks (Python 3 standard library only).

Graphs are given by an n x n matrix A of nonnegative integers, A[u][v] = number of
parallel edges u -> v.  Walks are edge sequences; the empty walk is counted.
"""
import itertools
import math


def topo_order(A):
    """Kahn's algorithm. Returns a topological order, or None if A has a directed cycle."""
    n = len(A)
    indeg = [sum(1 for u in range(n) if A[u][v]) for v in range(n)]
    order = [v for v in range(n) if indeg[v] == 0]
    i = 0
    while i < len(order):
        u = order[i]
        i += 1
        for v in range(n):
            if A[u][v]:
                indeg[v] -= 1
                if indeg[v] == 0:
                    order.append(v)
    return order if len(order) == n else None


def path_matrix(A):
    """C[u][v] = number of walks u -> v (DAG only) by dynamic programming."""
    n = len(A)
    order = topo_order(A)
    assert order is not None
    C = [[0] * n for _ in range(n)]
    for u in range(n):
        Cu = C[u]
        Cu[u] = 1
        for v in order:
            if Cu[v]:
                cv = Cu[v]
                Av = A[v]
                for w in range(n):
                    if Av[w]:
                        Cu[w] += cv * Av[w]
    return C


def matmul(X, Y):
    n, m, p = len(X), len(Y), len(Y[0])
    Z = [[0] * p for _ in range(n)]
    for i in range(n):
        Xi = X[i]
        Zi = Z[i]
        for k in range(m):
            x = Xi[k]
            if x:
                Yk = Y[k]
                for j in range(p):
                    if Yk[j]:
                        Zi[j] += x * Yk[j]
    return Z


def identity(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def path_matrix_powers(A):
    """Independent computation: C = I + A + ... + A^(n-1) by repeated multiplication."""
    n = len(A)
    C = identity(n)
    P = identity(n)
    for _ in range(n):
        P = matmul(P, A)
        C = [[C[i][j] + P[i][j] for j in range(n)] for i in range(n)]
    return C


def count_paths_dfs(A, s, t):
    """Independent computation of N(s,t) by explicit depth-first enumeration (DAG only)."""
    n = len(A)
    cnt = 0
    stack = [s]
    while stack:
        u = stack.pop()
        if u == t:
            cnt += 1
        for w in range(n):
            for _ in range(A[u][w]):
                stack.append(w)
    return cnt


def all_paths(A, s, t):
    """All s-t walks of a DAG as tuples of edge ids (u, v, copy)."""
    n = len(A)
    out = []

    def rec(u, acc):
        if u == t:
            out.append(tuple(acc))
        for w in range(n):
            for c in range(A[u][w]):
                acc.append((u, w, c))
                rec(w, acc)
                acc.pop()
    rec(s, [])
    return out


def maxentry(C):
    return max(max(row) for row in C)


def reach_sets(A):
    """R[u] = set of vertices reachable from u (including u); DAG or not."""
    n = len(A)
    R = []
    for u in range(n):
        seen = {u}
        st = [u]
        while st:
            x = st.pop()
            for y in range(n):
                if A[x][y] and y not in seen:
                    seen.add(y)
                    st.append(y)
        R.append(seen)
    return R


def induced(A, S):
    """Induced subgraph on the ordered list S, returned as a matrix indexed by positions in S."""
    return [[A[u][v] for v in S] for u in S]


def embed(M, S, n):
    """Embed a |S| x |S| matrix on the vertex list S into the n x n identity."""
    E = identity(n)
    for i, u in enumerate(S):
        for j, v in enumerate(S):
            E[u][v] = M[i][j]
    return E


def is_mangrove_path_matrix(M, D):
    """M must equal the path matrix of the DAG D and have all entries <= 1."""
    if topo_order(D) is None:
        return False
    return path_matrix(D) == M and maxentry(M) <= 1


def ilog2(x):
    return x.bit_length() - 1


def upper_triangular_dags(n):
    """All simple DAGs on 0..n-1 whose edges go from smaller to larger labels.
    Every DAG is isomorphic to one of them."""
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    for mask in range(1 << len(pairs)):
        A = [[0] * n for _ in range(n)]
        for b, (i, j) in enumerate(pairs):
            if mask >> b & 1:
                A[i][j] = 1
        yield A


def trimmed_vertices(A, s, t):
    """Vertices lying on some s-t walk (DAG)."""
    R = reach_sets(A)
    n = len(A)
    return [v for v in range(n) if v in R[s] and t in R[v]]


def cyclomatic(A, verts=None):
    n = len(A)
    if verts is None:
        verts = list(range(n))
    m = sum(A[u][v] for u in verts for v in verts)
    return m - len(verts) + 1


def blocks_of_multigraph(A, verts):
    """Biconnected components of the underlying undirected multigraph on verts.
    Returns a list of (vertex set, edge list) where edges are (u, v, copy) with u -> v."""
    edges = []
    for u in verts:
        for v in verts:
            for c in range(A[u][v]):
                edges.append((u, v, c))
    adj = {v: [] for v in verts}
    for eid, (u, v, c) in enumerate(edges):
        adj[u].append((v, eid))
        adj[v].append((u, eid))
    disc, low = {}, {}
    timer = [0]
    estack = []
    comps = []

    def dfs(u, pe):
        disc[u] = low[u] = timer[0]
        timer[0] += 1
        for (w, eid) in adj[u]:
            if eid == pe:
                continue
            if w not in disc:
                estack.append(eid)
                dfs(w, eid)
                low[u] = min(low[u], low[w])
                if low[w] >= disc[u]:
                    comp = []
                    while True:
                        e = estack.pop()
                        comp.append(e)
                        if e == eid:
                            break
                    comps.append(comp)
            elif disc[w] < disc[u]:
                estack.append(eid)
                low[u] = min(low[u], disc[w])
    for v in verts:
        if v not in disc:
            dfs(v, -1)
    out = []
    for comp in comps:
        es = [edges[e] for e in comp]
        vs = set()
        for (u, v, c) in es:
            vs.add(u)
            vs.add(v)
        out.append((vs, es))
    return out


def addition_chain_lengths(N):
    """l(r) for 1 <= r <= N: exact minimal addition-chain lengths by iterative deepening."""
    best = {1: 0}
    res = [None] * (N + 1)
    res[1] = 0

    def search(chain, depth_left, target):
        last = chain[-1]
        if last == target:
            return True
        if depth_left == 0:
            return False
        if last << depth_left < target:
            return False
        cand = set()
        for i in range(len(chain)):
            for j in range(i, len(chain)):
                s = chain[i] + chain[j]
                if last < s <= target:
                    cand.add(s)
        for s in sorted(cand, reverse=True):
            chain.append(s)
            if search(chain, depth_left - 1, target):
                chain.pop()
                return True
            chain.pop()
        return False

    for r in range(2, N + 1):
        L = max(1, (r - 1).bit_length())  # ceil(log2 r) lower bound
        while not search([1], L, r):
            L += 1
        res[r] = L
    return res
