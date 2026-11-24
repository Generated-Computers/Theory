"""The example families of Remark 6.6 and Remark 4.8: for each we compute
k* = max N(u,v), lambda = min(#sources, #sinks), gamma (largest cycle rank of
a weak component) and bcw, and run the decider of Theorem 3.4 with k = k*,
recording the largest choice string.
Usage: python3 examples.py
"""
from common import walk_counts, cycle_rank_max, INF
from cycle_signatures import bcw
from choice_compressed import decide


def empty(n):
    return [[0] * n for _ in range(n)]


def zigzag(m):
    """s -> x_i (i < m), x_i -> y_i, x_i -> y_{i+1}: one source, k = 2."""
    n = 1 + m + (m + 1)
    adj = empty(n)
    x = lambda i: 1 + i
    y = lambda i: 1 + m + i
    for i in range(m):
        adj[0][x(i)] = 1
        adj[x(i)][y(i)] = 1
        adj[x(i)][y(i + 1)] = 1
    return adj


def diamond_comb(m):
    """m diamonds a->b->d, a->c->d joined by bridges a_{i+1} -> d_i."""
    n = 4 * m
    adj = empty(n)
    for i in range(m):
        a, b, c, d = 4 * i, 4 * i + 1, 4 * i + 2, 4 * i + 3
        adj[a][b] = adj[a][c] = adj[b][d] = adj[c][d] = 1
        if i + 1 < m:
            adj[4 * (i + 1)][d] = 1
    return adj


def caterpillar(m):
    """spine v_0 -> ... -> v_{m-1}, source tooth p_i -> v_i, sink tooth v_i -> q_i."""
    n = 3 * m
    adj = empty(n)
    for i in range(m):
        if i + 1 < m:
            adj[i][i + 1] = 1
        adj[m + i][i] = 1
        adj[i][2 * m + i] = 1
    return adj


def subdivided_grid(r):
    """Middle vertices X = r x r grid points, each with an arc to one sink z;
    every grid edge {x, x'} becomes a source a with arcs a -> x, a -> x'.
    Valid for k = 2 with one sink; its underlying graph contains a
    subdivided r x r grid."""
    pts = [(i, j) for i in range(r) for j in range(r)]
    gedges = [((i, j), (i + 1, j)) for i in range(r - 1) for j in range(r)] + \
             [((i, j), (i, j + 1)) for i in range(r) for j in range(r - 1)]
    n = len(pts) + 1 + len(gedges)
    adj = empty(n)
    pid = {p: i for i, p in enumerate(pts)}
    z = len(pts)
    for p in pts:
        adj[pid[p]][z] = 1
    for e, (p, q) in enumerate(gedges):
        a = len(pts) + 1 + e
        adj[a][pid[p]] = adj[a][pid[q]] = 1
    return adj


def params(adj):
    n = len(adj)
    N = walk_counts(adj)
    kstar = max(max(row) for row in N)
    tplus = sum(1 for v in range(n) if sum(adj[v]) == 0)
    tminus = sum(1 for v in range(n) if sum(adj[u][v] for u in range(n)) == 0)
    return kstar, min(tplus, tminus), cycle_rank_max(adj), bcw(adj)


def main():
    print(f"{'family':<18}{'n':>4}{'k*':>5}{'lambda':>8}{'gamma':>7}{'bcw':>5}"
          f"{'accept':>8}{'|sigma|':>9}{'k*lambda-1':>12}")
    fams = [("zigzag", zigzag, [2, 4, 8]), ("diamond comb", diamond_comb, [2, 4, 8]),
            ("comb", caterpillar, [2, 4, 8]), ("subdivided grid", subdivided_grid, [2, 3])]
    for name, f, sizes in fams:
        for m in sizes:
            adj = f(m)
            k, lam, g, b = params(adj)
            st = {"maxsigma": 0}
            n = len(adj)
            # pick s,t with N(s,t) >= 1: a source and something it reaches
            N = walk_counts(adj)
            s = next(v for v in range(n) if sum(adj[u][v] for u in range(n)) == 0)
            t = max(range(n), key=lambda v: N[s][v])
            acc, _ = decide(adj, s, t, k, st)
            print(f"{name + ' ' + str(m):<18}{n:>4}{k:>5}{lam:>8}{g:>7}{b:>5}"
                  f"{str(acc):>8}{st['maxsigma']:>9}{k * lam - 1:>12}")


if __name__ == "__main__":
    main()
