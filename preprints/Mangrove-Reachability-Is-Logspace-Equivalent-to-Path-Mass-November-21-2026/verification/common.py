"""Shared helpers for the computer checks (Python 3 standard library only).

A graph is a square list-of-lists `A` of nonnegative integers: A[u][v] is the
number of edge occurrences u -> v.  Walks are edge sequences, vertices may repeat,
the empty walk is counted, parallel edges are distinct.  INF stands for infinity.
"""
import itertools
from fractions import Fraction

INF = float("inf")


def size(A):
    return len(A)


def copy(A):
    return [row[:] for row in A]


def reach_closure(A):
    """R[u][v] = True iff there is a walk (possibly empty) from u to v."""
    n = len(A)
    R = [[A[u][v] > 0 or u == v for v in range(n)] for u in range(n)]
    for w in range(n):
        for u in range(n):
            if R[u][w]:
                for v in range(n):
                    if R[w][v]:
                        R[u][v] = True
    return R


def cyclic_vertices(A):
    """Vertices lying on a directed cycle (a nonempty closed walk)."""
    n = len(A)
    R = reach_closure(A)
    return [w for w in range(n) if any(A[w][x] > 0 and R[x][w] for x in range(n))]


def walk_counts(A):
    """N[u][v] in N u {INF}, computed by explicit enumeration of walks.

    Independent of matrix algebra: N(u,v) is infinite iff a cycle vertex lies on
    some u-v route; otherwise all u-v walks are enumerated by depth-first search
    restricted to vertices that can still reach v.
    """
    n = len(A)
    R = reach_closure(A)
    cyc = set(cyclic_vertices(A))
    N = [[0] * n for _ in range(n)]
    for u in range(n):
        for v in range(n):
            if not R[u][v]:
                continue
            if any(R[u][w] and R[w][v] for w in cyc):
                N[u][v] = INF
                continue
            count = 0
            stack = [u]
            while stack:
                x = stack.pop()
                if x == v:
                    count += 1
                for y in range(n):
                    if A[x][y] and R[y][v]:
                        for _ in range(A[x][y]):
                            stack.append(y)
            N[u][v] = count
    return N


def is_acyclic(A):
    return not cyclic_vertices(A)


def max_count(N):
    return max(max(row) for row in N)


def is_k_su(A, k, N=None):
    if N is None:
        N = walk_counts(A)
    return max_count(N) <= k


def masses(A, N=None):
    """Path mass M(v) = sum_x N(v,x) (INF if infinite)."""
    if N is None:
        N = walk_counts(A)
    return [sum(row) for row in N]


def matmul(X, Y):
    n, m, p = len(X), len(Y), len(Y[0])
    return [[sum(X[i][k] * Y[k][j] for k in range(m)) for j in range(p)] for i in range(n)]


def identity(n):
    return [[1 if i == j else 0 for j in range(n)] for i in range(n)]


def matpow(X, r):
    R = identity(len(X))
    for _ in range(r):
        R = matmul(R, X)
    return R


def matrix_path_counts(A):
    """C = I + A + ... + A^(n-1) (equals N on a DAG)."""
    n = len(A)
    C = identity(n)
    P = identity(n)
    for _ in range(1, n):
        P = matmul(P, A)
        C = [[C[i][j] + P[i][j] for j in range(n)] for i in range(n)]
    return C


def det_fraction(M):
    """Exact determinant by Gaussian elimination over the rationals."""
    n = len(M)
    M = [[Fraction(x) for x in row] for row in M]
    d = Fraction(1)
    for c in range(n):
        p = None
        for r in range(c, n):
            if M[r][c] != 0:
                p = r
                break
        if p is None:
            return Fraction(0)
        if p != c:
            M[c], M[p] = M[p], M[c]
            d = -d
        d *= M[c][c]
        for r in range(c + 1, n):
            f = M[r][c] / M[c][c]
            if f:
                for j in range(c, n):
                    M[r][j] -= f * M[c][j]
    return d


def solve_fraction(M, b):
    """Solve M x = b exactly; return None if M is singular."""
    n = len(M)
    T = [[Fraction(x) for x in M[i]] + [Fraction(b[i])] for i in range(n)]
    for c in range(n):
        p = None
        for r in range(c, n):
            if T[r][c] != 0:
                p = r
                break
        if p is None:
            return None
        T[c], T[p] = T[p], T[c]
        piv = T[c][c]
        T[c] = [x / piv for x in T[c]]
        for r in range(n):
            if r != c and T[r][c] != 0:
                f = T[r][c]
                T[r] = [T[r][j] - f * T[c][j] for j in range(n + 1)]
    return [T[i][n] for i in range(n)]


def all_digraphs(n, loops=True, maxmult=1):
    """All digraphs on n labelled vertices with edge multiplicities <= maxmult."""
    cells = [(u, v) for u in range(n) for v in range(n) if loops or u != v]
    for vals in itertools.product(range(maxmult + 1), repeat=len(cells)):
        A = [[0] * n for _ in range(n)]
        for (u, v), x in zip(cells, vals):
            A[u][v] = x
        yield A


def upper_dags(n, maxmult=1):
    """All DAGs whose edges go from lower to higher index (one per topological labelling)."""
    cells = [(u, v) for u in range(n) for v in range(u + 1, n)]
    for vals in itertools.product(range(maxmult + 1), repeat=len(cells)):
        A = [[0] * n for _ in range(n)]
        for (u, v), x in zip(cells, vals):
            A[u][v] = x
        yield A


def all_labelled_dags(n):
    """All labelled simple DAGs on n vertices (relabellings of upper-triangular ones)."""
    seen = set()
    for A in upper_dags(n):
        for perm in itertools.permutations(range(n)):
            key = tuple(A[perm[u]][perm[v]] for u in range(n) for v in range(n))
            if key not in seen:
                seen.add(key)
    for key in sorted(seen):
        yield [list(key[i * n:(i + 1) * n]) for i in range(n)]


def add_universal_sink(A):
    """G_bot: a fresh sink (last index) with one edge from every old vertex."""
    n = len(A)
    B = [row[:] + [1] for row in A]
    B.append([0] * (n + 1))
    return B


def add_terminal_chain(A, t, B):
    """G^{t,B}: append the chain t -> z1 -> ... -> zB (new indices n..n+B-1)."""
    n = len(A)
    m = n + B
    C = [[0] * m for _ in range(m)]
    for u in range(n):
        for v in range(n):
            C[u][v] = A[u][v]
    C[t][n] = 1
    for i in range(B - 1):
        C[n + i][n + i + 1] = 1
    return C


def induced(A, verts):
    verts = list(verts)
    return [[A[u][v] for v in verts] for u in verts]


def out_edges(A, v):
    """Canonical order of the outgoing edge occurrences at v: by head, then copy."""
    res = []
    for u in range(len(A)):
        for c in range(A[v][u]):
            res.append((u, c))
    return res


def walks_from_preorder(A, v):
    """All walks from v (as tuples of edge occurrences), in depth-first preorder
    of the canonical edge order.  Only for DAGs."""
    out = []

    def rec(x, prefix):
        out.append(tuple(prefix))
        for (u, c) in out_edges(A, x):
            prefix.append((x, u, c))
            rec(u, prefix)
            prefix.pop()

    rec(v, [])
    return out


def rank_formula(A, M, v, walk):
    """rank_v(e_i P) = 1 + sum_{j<i} M(u_j) + rank_{u_i}(P), unrolled along the walk."""
    r = 0
    x = v
    for (a, b, c) in walk:
        r += 1
        for (u, cc) in out_edges(A, x):
            if (u, cc) == (b, c):
                break
            r += M[u]
        x = b
    return r + 1


def unrank_stackless(A, mass_of, v, r):
    """Stackless unranking: keeps only current vertex, residual rank, one mass value."""
    walk = []
    x = v
    while r != 1:
        r -= 1
        for (u, c) in out_edges(A, x):
            mu = mass_of(u)
            if r <= mu:
                walk.append((x, u, c))
                x = u
                break
            r -= mu
        else:
            raise ValueError("rank out of range")
    return tuple(walk)


def topological_order(A):
    """Kahn's algorithm; returns None if A has a directed cycle."""
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


def dag_counts(A):
    """Path counts of a DAG by dynamic programming in reverse topological order
    (a second, independent way of computing N)."""
    n = len(A)
    order = topological_order(A)
    assert order is not None
    N = [None] * n
    for u in reversed(order):
        row = [0] * n
        row[u] = 1
        for w in range(n):
            if A[u][w]:
                rw = N[w]
                m = A[u][w]
                for x in range(n):
                    if rw[x]:
                        row[x] += m * rw[x]
        N[u] = row
    return N
