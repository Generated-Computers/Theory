"""Shared helpers for the checking scripts (standard library only).

A digraph on vertices 0..n-1 is an n x n 0/1 adjacency matrix `adj`
(adj[u][v] = 1 means the arc u -> v; loops allowed).  Walk counts follow
the paper: walks are arc sequences, vertices may repeat, the empty walk is
counted, so N(v,v) >= 1.  INF stands for an infinite count.
"""
import itertools
import random
from collections import deque

INF = float("inf")


# ---------------------------------------------------------------- generators
def all_digraphs(n, loops=False):
    """All simple digraphs on n vertices (optionally with loops)."""
    cells = [(u, v) for u in range(n) for v in range(n) if loops or u != v]
    for mask in range(1 << len(cells)):
        adj = [[0] * n for _ in range(n)]
        for i, (u, v) in enumerate(cells):
            if mask >> i & 1:
                adj[u][v] = 1
        yield adj


def all_oriented(n):
    """All digraphs without loops and without antiparallel pairs
    (each unordered pair: absent, u->v, or v->u)."""
    pairs = [(u, v) for u in range(n) for v in range(u + 1, n)]
    for states in itertools.product(range(3), repeat=len(pairs)):
        adj = [[0] * n for _ in range(n)]
        for (u, v), st in zip(pairs, states):
            if st == 1:
                adj[u][v] = 1
            elif st == 2:
                adj[v][u] = 1
        yield adj


def random_digraph(n, p, rng, loops=False):
    adj = [[0] * n for _ in range(n)]
    for u in range(n):
        for v in range(n):
            if (u != v or loops) and rng.random() < p:
                adj[u][v] = 1
    return adj


def random_dag(n, p, rng):
    """Random DAG: arcs go forward in a random vertex order."""
    order = list(range(n))
    rng.shuffle(order)
    adj = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            if rng.random() < p:
                adj[order[i]][order[j]] = 1
    return adj


def reverse(adj):
    n = len(adj)
    return [[adj[v][u] for v in range(n)] for u in range(n)]


def succ(adj, v):
    return [w for w in range(len(adj)) if adj[v][w]]


# -------------------------------------------------------- brute-force counts
def walk_counts(adj):
    """N(u,v) by matrix powers, with INF where a cycle sits on a u-v walk."""
    n = len(adj)
    reach = [[False] * n for _ in range(n)]
    for u in range(n):
        reach[u][u] = True
        dq = deque([u])
        while dq:
            x = dq.popleft()
            for w in range(n):
                if adj[x][w] and not reach[u][w]:
                    reach[u][w] = True
                    dq.append(w)
    oncycle = [any(adj[c][w] and reach[w][c] for w in range(n)) for c in range(n)]
    # sum_{l < n} A^l
    total = [[1 if u == v else 0 for v in range(n)] for u in range(n)]
    power = [row[:] for row in total]
    for _ in range(n - 1):
        power = [[sum(power[u][x] * adj[x][v] for x in range(n)) for v in range(n)]
                 for u in range(n)]
        for u in range(n):
            for v in range(n):
                total[u][v] += power[u][v]
    N = [[0] * n for _ in range(n)]
    for u in range(n):
        for v in range(n):
            if any(oncycle[c] and reach[u][c] and reach[c][v] for c in range(n)):
                N[u][v] = INF
            else:
                N[u][v] = total[u][v]
    return N


def is_acyclic(adj):
    n = len(adj)
    indeg = [sum(adj[u][v] for u in range(n)) for v in range(n)]
    dq = deque(v for v in range(n) if indeg[v] == 0)
    seen = 0
    while dq:
        x = dq.popleft()
        seen += 1
        for w in range(n):
            if adj[x][w]:
                indeg[w] -= 1
                if indeg[w] == 0:
                    dq.append(w)
    return seen == n


def simple_path_counts(adj):
    """Number of directed vertex-simple u-v paths (the empty path for u=v)."""
    n = len(adj)
    C = [[0] * n for _ in range(n)]

    def dfs(u, v, visited):
        C[u][v] += 1
        for w in range(n):
            if adj[v][w] and w not in visited:
                visited.add(w)
                dfs(u, w, visited)
                visited.discard(w)

    for u in range(n):
        dfs(u, u, {u})
    return C


def valid(adj, k):
    """k-strong unambiguity: N(u,v) <= k for all u,v."""
    N = walk_counts(adj)
    return all(N[u][v] <= k for u in range(len(adj)) for v in range(len(adj))), N


def in_stcon_sf(adj, s, t, k):
    ok, N = valid(adj, k)
    return ok and N[s][t] >= 1


# ----------------------------------------------------- undirected structure
def und_edges(adj):
    """Underlying undirected multigraph: one edge per arc (loops kept)."""
    n = len(adj)
    return [(u, v) for u in range(n) for v in range(n) if adj[u][v]]


def components(n, edges, avoid=frozenset()):
    comp = [-1] * n
    nbr = [[] for _ in range(n)]
    for (u, v) in edges:
        if u in avoid or v in avoid:
            continue
        nbr[u].append(v)
        nbr[v].append(u)
    c = 0
    for r in range(n):
        if r in avoid or comp[r] != -1:
            continue
        comp[r] = c
        dq = deque([r])
        while dq:
            x = dq.popleft()
            for y in nbr[x]:
                if comp[y] == -1:
                    comp[y] = c
                    dq.append(y)
        c += 1
    return comp


def connected_avoiding(n, edges, x, y, avoid):
    if x in avoid or y in avoid:
        return False
    comp = components(n, edges, frozenset(avoid))
    return comp[x] == comp[y]


def bfs_path(n, edges, x, y, avoid):
    """An undirected x-y path (list of edge indices) avoiding `avoid`."""
    nbr = [[] for _ in range(n)]
    for i, (u, v) in enumerate(edges):
        if u in avoid or v in avoid:
            continue
        nbr[u].append((v, i))
        nbr[v].append((u, i))
    prev = {x: None}
    dq = deque([x])
    while dq:
        a = dq.popleft()
        if a == y:
            break
        for (b, i) in nbr[a]:
            if b not in prev:
                prev[b] = (a, i)
                dq.append(b)
    if y not in prev:
        return None
    path = []
    cur = y
    while prev[cur] is not None:
        a, i = prev[cur]
        path.append(i)
        cur = a
    return path


def cycle_rank_max(adj):
    """gamma(G): max over weak components of |E_C| - |V_C| + 1 (loops count)."""
    n = len(adj)
    E = und_edges(adj)
    comp = components(n, E)
    best = 0
    for c in set(comp):
        vs = sum(1 for v in range(n) if comp[v] == c)
        es = sum(1 for (u, v) in E if comp[u] == c)
        best = max(best, es - vs + 1)
    return best


def gf2_independent(vectors):
    """Are the given integer bitmasks linearly independent over GF(2)?"""
    basis = []
    for v in vectors:
        for b in basis:
            v = min(v, v ^ b)
        if v == 0:
            return False
        basis.append(v)
    return True


# ------------------------------------------------------------ blocks (Tarjan)
def blocks_tarjan(n, edges):
    """Biconnected blocks of a simple undirected graph, as sets of edge ids."""
    nbr = [[] for _ in range(n)]
    for i, (u, v) in enumerate(edges):
        nbr[u].append((v, i))
        nbr[v].append((u, i))
    disc = [-1] * n
    low = [0] * n
    timer = [0]
    stack = []
    out = []

    def dfs(u, pe):
        disc[u] = low[u] = timer[0]
        timer[0] += 1
        for (w, i) in nbr[u]:
            if i == pe:
                continue
            if disc[w] == -1:
                stack.append(i)
                dfs(w, i)
                low[u] = min(low[u], low[w])
                if low[w] >= disc[u]:
                    blk = set()
                    while True:
                        j = stack.pop()
                        blk.add(j)
                        if j == i:
                            break
                    out.append(frozenset(blk))
            elif disc[w] < disc[u]:
                stack.append(i)
                low[u] = min(low[u], disc[w])

    for r in range(n):
        if disc[r] == -1:
            dfs(r, -1)
    return out
