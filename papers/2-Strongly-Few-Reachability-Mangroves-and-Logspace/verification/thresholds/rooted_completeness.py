"""Checks for the budget-mass truncation lemma and the reductions of Section 3.

  python3 rooted_completeness.py [nmax]      (default nmax = 4)

On every simple digraph (self-loops allowed) with at most nmax vertices and every
root s it checks:
  (T)  truncation lemma (Lemma 2.8): N(s,q) <= kappa(q) for all q  iff  N^{<=B}(s,q) <= kappa(q)
       for all q, B = sum kappa; all kappa in {0,1,2}^V for n <= 3, 4 random kappa
       for n = 4;
  (L)  DAG layering (Lemma 3.1): layers 0..D with catch sinks, for D = n and
       D = 2n-1: reach-unambiguity of the layered graph from (s,0) agrees with that
       of G from s, and (s,0) reaches c_t iff s reaches t; control: D = n-1 fails;
  (P)  k-fold prefix gadget (Lemma 2.9), k = 2, 3: N_H(r,v) = k N_G(s,v) (INF included);
  (C)  two-cone reduction (Theorem 3.5): <H,r,z> in FBFew_{k,1} iff <G,s> in
       RootFewRec_k, for k = 1, 2.
It also checks, on random reach-unambiguous "configuration graphs", the complement
reduction of Lemma 3.3 (recognition hardness).
"""
import itertools
import random
import sys

from walks import (INF, add_edge, add_vertex, bounded_counts_from, copy_graph,
                   dag_all_pairs, exact_counts, exact_counts_from, from_matrix,
                   is_simple, kmul, reach_matrix)


def layered(adj, s, D):
    """Layers 0..D, edge (u,i)->(v,i+1) for every edge u->v, catch sink c_v."""
    n = len(adj)
    idx = lambda v, i: i * n + v
    L = [dict() for _ in range(n * (D + 1) + n)]
    for i in range(D):
        for u in range(n):
            for v in adj[u]:
                L[idx(u, i)][idx(v, i + 1)] = 1
    for v in range(n):
        c = n * (D + 1) + v
        for i in range(D + 1):
            L[idx(v, i)][c] = 1
    return L, idx(s, 0), [n * (D + 1) + v for v in range(n)]


def prefix(adj, s, k):
    H = copy_graph(adj)
    r = add_vertex(H)
    for _ in range(k):
        a = add_vertex(H)
        add_edge(H, r, a)
        add_edge(H, a, s)
    return H, r


def main():
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    rng = random.Random(2026)
    stats = dict(graphs=0, roots=0, trunc=0, trunc_bad=0, lay_bad=0, lay_ctrl_fail=0,
                 pre_bad=0, cone_bad=0)
    for n in range(1, nmax + 1):
        for bits in range(1 << (n * n)):
            adj = from_matrix(bits, n)
            stats["graphs"] += 1
            NG = exact_counts(adj)
            R = reach_matrix(adj)
            for s in range(n):
                stats["roots"] += 1
                row = NG[s]
                valid1 = all(x <= 1 for x in row)
                # (T) truncation lemma
                kappas = (itertools.product(range(3), repeat=n) if n <= 3 else
                          [tuple(rng.randrange(3) for _ in range(n)) for _ in range(4)])
                for kap in kappas:
                    B = sum(kap)
                    lhs = all(row[q] <= kap[q] for q in range(n))
                    bc = bounded_counts_from(adj, s, B)
                    rhs = all(bc[q] <= kap[q] for q in range(n))
                    stats["trunc"] += 1
                    stats["trunc_bad"] += lhs != rhs
                # (L) layering, depth n and 2n-1; control depth n-1
                for D in (n, 2 * n - 1, n - 1):
                    if D < 0:
                        continue
                    Lg, root, sinks = layered(adj, s, D)
                    NL = dag_all_pairs(Lg)[root]
                    ok = all(x <= 1 for x in NL) == valid1
                    ok = ok and all((NL[sinks[t]] >= 1) == R[s][t] for t in range(n))
                    if D == n - 1:
                        stats["lay_ctrl_fail"] += not ok
                    else:
                        stats["lay_bad"] += not ok
                # (P) prefix gadget
                for k in (2, 3):
                    H, r = prefix(adj, s, k)
                    assert is_simple(H)
                    NH = exact_counts_from(H, r)
                    if any(NH[v] != kmul(k, row[v]) for v in range(n)):
                        stats["pre_bad"] += 1
                    if (all(x <= k for x in NH) != valid1):
                        stats["pre_bad"] += 1
                # (C) two-cone reduction: r->s, r->z, target z
                for k in (1, 2):
                    H = copy_graph(adj)
                    r = add_vertex(H)
                    z = add_vertex(H)
                    add_edge(H, r, s)
                    add_edge(H, r, z)
                    NH = exact_counts(H)
                    fwd = all(NH[r][v] <= k for v in range(len(H)))
                    bwd = all(NH[v][z] <= 1 for v in range(len(H)))
                    reach = NH[r][z] >= 1
                    validk = all(x <= k for x in row)
                    stats["cone_bad"] += (fwd and bwd and reach) != validk
    # complement reduction for recognition hardness (Lemma 3.3)
    comp_tests = comp_bad = 0
    while comp_tests < 3000:
        n = rng.randrange(2, 8)
        adj = [dict() for _ in range(n)]
        for u in range(n):
            for v in range(n):
                if rng.random() < 0.3:
                    adj[u][v] = 1
        row = exact_counts_from(adj, 0)
        if any(x > 1 for x in row):
            continue  # not reach-unambiguous from the start configuration 0
        acc = [v for v in range(n) if rng.random() < 0.3]
        H = copy_graph(adj)
        r = add_vertex(H)
        y = add_vertex(H)
        z = add_vertex(H)
        add_edge(H, r, 0)
        add_edge(H, r, y)
        add_edge(H, y, z)
        for a in acc:
            add_edge(H, a, z)
        NH = exact_counts_from(H, r)
        accepted = any(row[a] >= 1 for a in acc)
        comp_tests += 1
        comp_bad += all(x <= 1 for x in NH) != (not accepted)
    print("graphs:", stats["graphs"], " rooted instances:", stats["roots"])
    print("(T) truncation lemma: %d budget vectors, %d failures" % (stats["trunc"], stats["trunc_bad"]))
    print("(L) layering depth n and 2n-1: %d failures" % stats["lay_bad"])
    print("    control depth n-1: fails on %d rooted instances (expected > 0)" % stats["lay_ctrl_fail"])
    print("(P) prefix gadget k=2,3: %d failures" % stats["pre_bad"])
    print("(C) two-cone reduction k=1,2: %d failures" % stats["cone_bad"])
    print("complement reduction (recognition hardness): %d tests, %d failures" % (comp_tests, comp_bad))


if __name__ == "__main__":
    main()
