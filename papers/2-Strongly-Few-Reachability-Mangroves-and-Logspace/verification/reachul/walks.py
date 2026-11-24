"""Reference walk counts, computed independently of the algorithms under test.

Conventions (as in the paper): a walk is a finite sequence of edge occurrences
whose endpoints concatenate; vertices may repeat; the empty walk at each vertex is
counted; parallel edge occurrences are distinct.  Infinite counts are returned as
INF (a float infinity).

A graph is (n, edges) with vertices 0..n-1 and edges a list of pairs (u, v); the
occurrence index of edges[i] is i + 1.
"""

import itertools

INF = float("inf")


def multiplicity_matrix(n, edges):
    A = [[0] * n for _ in range(n)]
    for (u, v) in edges:
        A[u][v] += 1
    return A


def reach_sets(n, edges):
    """R[u] = set of vertices reachable from u (including u), by BFS."""
    succ = [[] for _ in range(n)]
    for (u, v) in edges:
        succ[u].append(v)
    R = []
    for u in range(n):
        seen = {u}
        stack = [u]
        while stack:
            x = stack.pop()
            for y in succ[x]:
                if y not in seen:
                    seen.add(y)
                    stack.append(y)
        R.append(seen)
    return R


def on_cycle(n, edges):
    """C[w] = True iff some nonempty closed walk passes through w."""
    # w lies on a nonempty closed walk iff some out-edge w -> x has x ~> w.
    R = reach_sets(n, edges)
    C = [False] * n
    for (u, v) in edges:
        if u in R[v]:
            C[u] = True
    return C


def walk_counts(n, edges):
    """N[u][v] for all pairs: INF iff some cycle vertex w has u ~> w ~> v;
    otherwise the sum of A^L[u][v] for L = 0..n-1 (walks avoid cycle vertices,
    hence are vertex-simple and have length at most n-1)."""
    A = multiplicity_matrix(n, edges)
    R = reach_sets(n, edges)
    C = on_cycle(n, edges)
    # matrix power sum
    P = [[1 if i == j else 0 for j in range(n)] for i in range(n)]
    S = [row[:] for row in P]
    for _ in range(1, n):
        P = [[sum(P[i][l] * A[l][j] for l in range(n)) for j in range(n)]
             for i in range(n)]
        for i in range(n):
            for j in range(n):
                S[i][j] += P[i][j]
    N = [[0] * n for _ in range(n)]
    for u in range(n):
        for v in range(n):
            inf = any(C[w] and (w in R[u]) and (v in R[w]) for w in range(n))
            N[u][v] = INF if inf else S[u][v]
    return N


def bounded_counts_from(n, edges, r, L):
    """List of vectors b[j][v] = number of walks r -> v of length <= j, j = 0..L,
    by dynamic programming over lengths."""
    A = multiplicity_matrix(n, edges)
    x = [0] * n
    x[r] = 1
    acc = x[:]
    out = [acc[:]]
    for _ in range(L):
        x = [sum(x[l] * A[l][v] for l in range(n)) for v in range(n)]
        acc = [acc[v] + x[v] for v in range(n)]
        out.append(acc[:])
    return out


def all_simple_digraphs(n, loops=True):
    """All 0/1 adjacency matrices on n vertices (self-loops allowed if loops)."""
    cells = [(i, j) for i in range(n) for j in range(n) if loops or i != j]
    for bits in itertools.product((0, 1), repeat=len(cells)):
        adj = [[0] * n for _ in range(n)]
        for (c, b) in zip(cells, bits):
            if b:
                adj[c[0]][c[1]] = 1
        yield adj


def edges_of(adj):
    n = len(adj)
    return [(i, j) for i in range(n) for j in range(n) if adj[i][j]]


def random_multigraph(rng, n, m, acyclic_bias=0.0):
    """m random edge occurrences on n vertices; with probability acyclic_bias an
    edge is forced to go from a smaller to a larger vertex (to produce many DAGs)."""
    edges = []
    for _ in range(m):
        u = rng.randrange(n)
        v = rng.randrange(n)
        if rng.random() < acyclic_bias:
            if u == v:
                continue
            if u > v:
                u, v = v, u
        edges.append((u, v))
    return edges


def is_prime(x):
    if x < 2:
        return False
    d = 2
    while d * d <= x:
        if x % d == 0:
            return False
        d += 1
    return True


def least_prime_above(x):
    p = x + 1
    while not is_prime(p):
        p += 1
    return p
