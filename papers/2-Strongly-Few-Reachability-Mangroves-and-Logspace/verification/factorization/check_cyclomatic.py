"""Checks of Sections 8-9 on all small trimmed two-terminal DAGs.

Families: every trimmed two-terminal simple DAG on n <= 7 vertices (s = 0, t = n-1, edges
from smaller to larger labels; every trimmed two-terminal DAG is isomorphic to one of them)
and every trimmed two-terminal multigraph on n <= 5 vertices with edge multiplicities <= 3.
For each H with r = N(s,t) and c = |E| - |V| + 1 we check
  * Theorem 8.3 (sandwich): c + 1 <= r <= 2^c, and the vertex form
    c(v) + 1 <= p(v) <= 2^c(v) for every vertex v (Lemma 8.2);
  * Theorem 8.8 (equality): r = 2^c iff every block of the underlying multigraph has
    cyclomatic number <= 1 (both directions for n <= 6 simple and n <= 4 multigraphs, the
    forward direction for all);
  * Theorem 8.6 (block product) and Theorem 8.5 (chord signatures, BFS spanning tree) for
    n <= 6 simple and n <= 4 multigraphs;
  * Theorem 10.1 (branch kernel): |V(K)| <= 2c + 2, |E(K)| <= 3c + 1;
  * Theorem 9.1: c >= l(r) for every H, and the minimum of c over the family equals l(r)
    for the values of r listed at the end.
Usage: python3 check_cyclomatic.py [max_n_simple=7] [max_n_multi=5]
"""
import itertools
import sys
from collections import deque

from sfcommon import (blocks_of_multigraph, addition_chain_lengths, all_paths, path_matrix)

min_c = {}
stats = {"graphs": 0, "equality graphs (r = 2^c)": 0}


def fail(msg, A):
    print("FAILURE:", msg)
    print("A =", A)
    sys.exit(1)


def light_checks(A, n, r, c, p, cv):
    for v in range(n):
        if not (cv[v] + 1 <= p[v] <= 2 ** cv[v]):
            fail("Lemma 8.2 vertex sandwich", A)
    if not (c + 1 <= r <= 2 ** c):
        fail("Theorem 8.3", A)
    # kernel: s, t and internal vertices that are not 1-in/1-out
    indeg = [sum(A[u][v] for u in range(n)) for v in range(n)]
    outdeg = [sum(A[v]) for v in range(n)]
    kept = 2 + sum(1 for v in range(1, n - 1) if not (indeg[v] == 1 and outdeg[v] == 1))
    if n == 1:
        kept = 1
    if kept > 2 * c + 2 or kept - 1 + c > 3 * c + 1:
        fail("Theorem 10.1", A)
    if r not in min_c or c < min_c[r]:
        min_c[r] = c
    stats["graphs"] += 1


def cycle_chain(A, n):
    blocks = blocks_of_multigraph(A, list(range(n)))
    return all(len(es) - len(vs) + 1 <= 1 for (vs, es) in blocks), blocks


def heavy_checks(A, n, r, c):
    is_chain, blocks = cycle_chain(A, n)
    if is_chain != (r == 2 ** c):
        fail("Theorem 8.8 equality classification", A)
    # block product
    prod = 1
    csum = 0
    for (vs, es) in blocks:
        vl = sorted(vs)
        a, b = vl[0], vl[-1]  # labels are topological
        B = [[0] * n for _ in range(n)]
        for (u, v, cc) in es:
            B[u][v] += 1
        prod *= path_matrix(B)[a][b]
        csum += len(es) - len(vs) + 1
    if n > 1 and (prod != r or csum != c):
        fail("Theorem 8.6 block product", A)
    # chord signature with a BFS spanning tree of the underlying multigraph
    edges = [(u, v, cc) for u in range(n) for v in range(n) for cc in range(A[u][v])]
    adj = {v: [] for v in range(n)}
    for e in edges:
        adj[e[0]].append((e[1], e))
        adj[e[1]].append((e[0], e))
    seen = {0}
    tree = set()
    dq = deque([0])
    while dq:
        x = dq.popleft()
        for (y, e) in adj[x]:
            if y not in seen:
                seen.add(y)
                tree.add(e)
                dq.append(y)
    chords = set(edges) - tree
    if len(chords) != c:
        fail("number of chords", A)
    sigs = set()
    for P in all_paths(A, 0, n - 1):
        sigs.add(frozenset(set(P) & chords))
    if len(sigs) != r:
        fail("Theorem 8.5 chord signature not injective", A)


def process(A, n, heavy):
    # trimmed?  labels are topological
    fwd = [False] * n
    fwd[0] = True
    for v in range(1, n):
        fwd[v] = any(A[u][v] and fwd[u] for u in range(v))
    bwd = [False] * n
    bwd[n - 1] = True
    for v in range(n - 2, -1, -1):
        bwd[v] = any(A[v][w] and bwd[w] for w in range(v + 1, n))
    if not (all(fwd) and all(bwd)):
        return
    m = sum(map(sum, A))
    c = m - n + 1
    p = [0] * n
    p[0] = 1
    for v in range(1, n):
        p[v] = sum(A[u][v] * p[u] for u in range(v))
    # c(v) = sum over ancestors w != s of (indeg(w) - 1); ancestors via bitmasks
    anc = [0] * n
    anc[0] = 1
    for v in range(1, n):
        a = 1 << v
        for u in range(v):
            if A[u][v]:
                a |= anc[u]
        anc[v] = a
    indeg = [sum(A[u][v] for u in range(n)) for v in range(n)]
    cv = [sum(indeg[w] - 1 for w in range(1, n) if anc[v] >> w & 1) for v in range(n)]
    r = p[n - 1]
    light_checks(A, n, r, c, p, cv)
    if r == 2 ** c:
        stats["equality graphs (r = 2^c)"] += 1
        is_chain, _ = cycle_chain(A, n)
        if not is_chain:
            fail("Theorem 8.8 (forward direction)", A)
    if heavy:
        heavy_checks(A, n, r, c)


def main():
    max_simple = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    max_multi = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    for n in range(1, max_simple + 1):
        pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
        for mask in range(1 << len(pairs)):
            A = [[0] * n for _ in range(n)]
            for b, (i, j) in enumerate(pairs):
                if mask >> b & 1:
                    A[i][j] = 1
            process(A, n, heavy=(n <= 6))
        print(f"simple DAGs, n = {n}: done ({stats['graphs']} trimmed graphs so far)")
    for n in range(2, max_multi + 1):
        pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
        for mult in itertools.product(range(4), repeat=len(pairs)):
            if max(mult) <= 1:
                continue  # simple graphs were done above
            A = [[0] * n for _ in range(n)]
            for (i, j), x in zip(pairs, mult):
                A[i][j] = x
            process(A, n, heavy=(n <= 4))
        print(f"multigraphs (multiplicity <= 3), n = {n}: done ({stats['graphs']} trimmed graphs so far)")
    for key in sorted(stats):
        print(f"  {key}: {stats[key]}")
    R = 40
    ell = addition_chain_lengths(max(R, max(min_c)))
    for r, c in min_c.items():
        if c < ell[r]:
            print("FAILURE: Theorem 9.1 lower bound, r =", r)
            sys.exit(1)
    eq = [r for r in range(1, R + 1) if min_c.get(r) == ell[r]]
    print("l(r) for r = 1..40:", [ell[r] for r in range(1, R + 1)])
    print("min c found     :", [min_c.get(r) for r in range(1, R + 1)])
    print("r in 1..40 with min c = l(r):", eq)
    print("c >= l(r) holds for every graph; all checks passed")


if __name__ == "__main__":
    main()
