"""Shared helpers: exact walk counts in finite digraphs and multigraphs.

Walk convention of the paper: a walk is a sequence of edge occurrences, vertices
may repeat, the empty walk counts once from every vertex to itself, and parallel
edges are distinct.  N(u, v) is a non-negative integer or INF.

A graph is given as a list `adj` of length n where adj[u] is a dict
{v: multiplicity}.  Standard library only.
"""

INF = float("inf")


def reach_matrix(adj):
    """Reflexive-transitive closure: R[u][v] iff v is reachable from u."""
    n = len(adj)
    R = [[False] * n for _ in range(n)]
    for u in range(n):
        R[u][u] = True
        stack = [u]
        while stack:
            x = stack.pop()
            for y in adj[x]:
                if adj[x][y] and not R[u][y]:
                    R[u][y] = True
                    stack.append(y)
    return R


def bounded_counts_from(adj, r, L):
    """Number of walks from r of length <= L ending at each vertex (exact ints)."""
    n = len(adj)
    cur = [0] * n
    cur[r] = 1
    tot = cur[:]
    for _ in range(L):
        nxt = [0] * n
        for u in range(n):
            if cur[u]:
                for v, m in adj[u].items():
                    nxt[v] += cur[u] * m
        cur = nxt
        for v in range(n):
            tot[v] += cur[v]
        if not any(cur):
            break
    return tot


def exact_counts(adj):
    """Exact all-pairs walk counts N[u][v] in N u {INF}.

    N(u, v) = INF iff some vertex w on a directed cycle satisfies u ~> w ~> v.
    Otherwise every u-v walk is a simple path, so N(u, v) = N^{<= n-1}(u, v).
    """
    n = len(adj)
    R = reach_matrix(adj)
    cyc = [any(adj[w][x] and R[x][w] for x in adj[w]) for w in range(n)]
    N = []
    for u in range(n):
        b = bounded_counts_from(adj, u, max(n - 1, 0))
        row = []
        for v in range(n):
            if any(R[u][w] and cyc[w] and R[w][v] for w in range(n)):
                row.append(INF)
            else:
                row.append(b[v])
        N.append(row)
    return N


def exact_counts_from(adj, r):
    n = len(adj)
    R = reach_matrix(adj)
    cyc = [any(adj[w][x] and R[x][w] for x in adj[w]) for w in range(n)]
    b = bounded_counts_from(adj, r, max(n - 1, 0))
    out = []
    for v in range(n):
        if any(R[r][w] and cyc[w] and R[w][v] for w in range(n)):
            out.append(INF)
        else:
            out.append(b[v])
    return out


def dag_all_pairs(adj):
    """All-pairs walk counts in a DAG by dynamic programming over a topological order.
    Raises ValueError if the graph has a cycle."""
    n = len(adj)
    indeg = [0] * n
    for u in range(n):
        for v, m in adj[u].items():
            if m:
                indeg[v] += 1
    order, stack = [], [u for u in range(n) if indeg[u] == 0]
    while stack:
        u = stack.pop()
        order.append(u)
        for v, m in adj[u].items():
            if m:
                indeg[v] -= 1
                if indeg[v] == 0:
                    stack.append(v)
    if len(order) != n:
        raise ValueError("not a DAG")
    pos = {u: i for i, u in enumerate(order)}
    N = [[0] * n for _ in range(n)]
    for u in range(n):
        N[u][u] = 1
        for x in order[pos[u]:]:
            if N[u][x]:
                for v, m in adj[x].items():
                    N[u][v] += N[u][x] * m
    return N


def from_matrix(bits, n):
    """Simple digraph (loops allowed) from an n*n bitmask."""
    adj = [dict() for _ in range(n)]
    for u in range(n):
        for v in range(n):
            if bits >> (u * n + v) & 1:
                adj[u][v] = 1
    return adj


def add_vertex(adj):
    adj.append(dict())
    return len(adj) - 1


def add_edge(adj, u, v, m=1):
    adj[u][v] = adj[u].get(v, 0) + m


def copy_graph(adj):
    return [dict(d) for d in adj]


def is_simple(adj):
    return all(m <= 1 for d in adj for m in d.values())


def kmul(k, x):
    return INF if x == INF else k * x
