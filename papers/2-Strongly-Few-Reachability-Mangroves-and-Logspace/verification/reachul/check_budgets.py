"""Section 4: exact budget-mass truncation, the full-unfolding root-budget decider,
the universal-source lift, selected roots and the two-cone reduction.

Checks
  * Theorem 4.1 for every budget vector kappa in {0,1,2,3}^n on all simple digraphs
    (loops allowed) with n <= 3 and every root, for kappa in {0,1,2}^4 on all simple
    digraphs with n = 4, and on random multigraphs with n <= 6;
  * Corollary 4.2 (a violated budget is already violated by walks of length <= B);
  * Remark 4.3 (directed B-cycle with unit budgets);
  * Theorem 4.4: the full-unfolding decider (Listing 3) accepts exactly RootBudget;
  * Lemma 4.6: N_U(rho,(a,v)) = N_G(a,v), infinite values included;
  * Theorem 4.7 and Corollary 4.9 via the reductions of the paper.

Usage: python3 check_budgets.py [seed]
"""

import itertools
import random
import sys

from walks import INF, all_simple_digraphs, edges_of, walk_counts, bounded_counts_from


def full_traverse(n, edges, r, B, kappa, q=None):
    """Listing 3 (FULL-TRAVERSE).  Continuation indices are edge occurrences."""
    m = len(edges)
    stack = []
    current, nxt = r, 0
    total = 1
    tc = 1 if (q is not None and r == q) else 0
    if total > B:
        return ("GLOBAL_OVERFLOW",)
    if q is not None and tc > kappa[q]:
        return ("TARGET_OVERFLOW",)
    while True:
        i = nxt
        while i < m and edges[i][0] != current:
            i += 1
        if i >= m:
            if not stack:
                return ("OK", total, tc)
            current, nxt = stack.pop()
            continue
        nxt = i + 1
        stack.append((current, nxt))
        current, nxt = edges[i][1], 0
        total += 1
        if total == B + 1:
            return ("GLOBAL_OVERFLOW",)
        if q is not None and current == q:
            tc += 1
            if tc == kappa[q] + 1:
                return ("TARGET_OVERFLOW",)


def root_budget_decide(n, edges, r, F, kappa):
    """Theorem 4.4: global pass, then one recount per state."""
    B = sum(kappa)
    if full_traverse(n, edges, r, B, kappa)[0] != "OK":
        return False
    reached = False
    for q in range(n):
        res = full_traverse(n, edges, r, B, kappa, q)
        if res[0] != "OK":
            return False
        if q in F and res[2] >= 1:
            reached = True
    return reached


def root_budget_def(Nrow, F, kappa):
    return all(Nrow[q] <= kappa[q] for q in range(len(kappa))) and \
        any(Nrow[f] >= 1 for f in F)


def universal_lift(n, edges, roots=None):
    """Construction 4.5 (U(G)); with roots given, only rho -> (a,a) for a in roots."""
    roots = range(n) if roots is None else roots
    idx = lambda a, v: 1 + a * n + v
    E = [(0, idx(a, a)) for a in roots]
    for a in range(n):
        for (u, v) in edges:
            E.append((idx(a, u), idx(a, v)))
    return 1 + n * n, E, idx


def check_truncation_graph(n, edges, kappa_range, stats):
    N = walk_counts(n, edges)
    maxB = max(kappa_range) * n
    for r in range(n):
        bc = bounded_counts_from(n, edges, r, maxB)
        for kappa in itertools.product(kappa_range, repeat=n):
            B = sum(kappa)
            lhs = all(N[r][q] <= kappa[q] for q in range(n))
            rhs = all(bc[B][q] <= kappa[q] for q in range(n))
            assert lhs == rhs, ("Theorem 4.1", n, edges, r, kappa)
            if not lhs:
                # Corollary 4.2: some q has kappa(q)+1 walks of length <= B
                assert any(bc[B][q] >= kappa[q] + 1 for q in range(n))
                stats["violated"] += 1
            else:
                stats["valid"] += 1
                # on valid instances every walk from r has length <= B-1
                assert bc[B - 1][:] == [N[r][q] for q in range(n)] if B >= 1 else True


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 2026
    rng = random.Random(seed)

    stats = {"valid": 0, "violated": 0}
    for n in range(1, 4):
        for adj in all_simple_digraphs(n):
            check_truncation_graph(n, edges_of(adj), range(4), stats)
    for adj in all_simple_digraphs(4):
        check_truncation_graph(4, edges_of(adj), range(3), stats)
    print("Theorem 4.1 / Corollary 4.2, all simple digraphs n<=4: %d valid and %d violating"
          " (graph, root, kappa) triples, 0 mismatches" % (stats["valid"], stats["violated"]))

    stats = {"valid": 0, "violated": 0}
    for _ in range(400):
        n = rng.randint(1, 5)
        m = rng.randint(0, 7)
        dag = rng.random() < 0.8
        edges = []
        for _ in range(m):
            u, v = rng.randrange(n), rng.randrange(n)
            if dag:
                if u == v:
                    continue
                u, v = min(u, v), max(u, v)
            edges.append((u, v))
        check_truncation_graph(n, edges, range(4) if n <= 4 else range(3), stats)
    print("Theorem 4.1 / Corollary 4.2, random multigraphs n<=5: %d valid, %d violating, 0 mismatches"
          % (stats["valid"], stats["violated"]))

    # Remark 4.3
    for B in range(1, 13):
        edges = [(i, (i + 1) % B) for i in range(B)]
        bc = bounded_counts_from(B, edges, 0, B)
        assert bc[B - 1] == [1] * B
        assert bc[B][0] == 2 and all(bc[B][q] == 1 for q in range(1, B))
    print("Remark 4.3 confirmed for B = 1..12")

    # Theorem 4.4 (Listing 3) against the definition
    cnt = acc = 0
    for n in range(1, 4):
        for adj in all_simple_digraphs(n):
            edges = edges_of(adj)
            N = walk_counts(n, edges)
            for r in range(n):
                for kappa in itertools.product(range(3), repeat=n):
                    for F in ([], [0], [n - 1], list(range(n))):
                        got = root_budget_decide(n, edges, r, F, kappa)
                        want = root_budget_def(N[r], F, kappa)
                        assert got == want
                        cnt += 1
                        acc += got
    for _ in range(4000):
        n = rng.randint(1, 6)
        m = rng.randint(0, 9)
        dag = rng.random() < 0.8
        edges = []
        for _ in range(m):
            u, v = rng.randrange(n), rng.randrange(n)
            if dag:
                if u == v:
                    continue
                u, v = min(u, v), max(u, v)
            edges.append((u, v))
        N = walk_counts(n, edges)
        r = rng.randrange(n)
        if rng.random() < 0.5 and all(x != INF for x in N[r]):
            kappa = [max(0, N[r][q] + rng.choice([0, 0, 0, 1, -1])) for q in range(n)]
        else:
            kappa = [rng.randint(0, 3) for _ in range(n)]
        F = [q for q in range(n) if rng.random() < 0.3]
        got = root_budget_decide(n, edges, r, F, kappa)
        want = root_budget_def(N[r], F, kappa)
        assert got == want
        cnt += 1
        acc += got
    print("Theorem 4.4 (Listing 3): %d RootBudget instances, %d accepted, 0 mismatches" % (cnt, acc))

    # Lemma 4.6 and Theorem 4.7 (PairBudget through U(G))
    cnt = acc = 0
    for n in range(1, 4):
        for adj in all_simple_digraphs(n):
            edges = edges_of(adj)
            N = walk_counts(n, edges)
            nU, EU, idx = universal_lift(n, edges)
            NU = walk_counts(nU, EU)
            assert NU[0][0] == 1
            for a in range(n):
                for v in range(n):
                    assert NU[0][idx(a, v)] == N[a][v], "Lemma 4.6"
            for k in range(0, 3):
                for (s, t) in [(0, 0), (0, n - 1), (n - 1, 0)]:
                    kappa = [1] + [k] * (n * n)
                    got = root_budget_decide(nU, EU, 0, [idx(s, t)], kappa)
                    want = all(N[u][v] <= k for u in range(n) for v in range(n)) and N[s][t] >= 1
                    assert got == want
                    cnt += 1
                    acc += got
    for _ in range(300):
        n = rng.randint(1, 4)
        m = rng.randint(0, 6)
        edges = []
        for _ in range(m):
            u, v = rng.randrange(n), rng.randrange(n)
            if rng.random() < 0.8:
                if u == v:
                    continue
                u, v = min(u, v), max(u, v)
            edges.append((u, v))
        N = walk_counts(n, edges)
        nU, EU, idx = universal_lift(n, edges)
        NU = walk_counts(nU, EU)
        for a in range(n):
            for v in range(n):
                assert NU[0][idx(a, v)] == N[a][v], "Lemma 4.6 (multigraph)"
        # nonuniform pair budgets
        kap = {(u, v): rng.randint(0, 3) for u in range(n) for v in range(n)}
        s, t = rng.randrange(n), rng.randrange(n)
        kappa = [1] + [kap[(a, v)] for a in range(n) for v in range(n)]
        got = root_budget_decide(nU, EU, 0, [idx(s, t)], kappa)
        want = all(N[u][v] <= kap[(u, v)] for u in range(n) for v in range(n)) and N[s][t] >= 1
        assert got == want
        cnt += 1
        acc += got
    print("Lemma 4.6 on all simple digraphs n<=3 and 300 random multigraphs; "
          "PairBudget via U(G): %d instances, %d accepted, 0 mismatches" % (cnt, acc))

    # Corollary 4.9 (selected roots and two cones)
    cnt = acc = 0
    for _ in range(3000):
        n = rng.randint(1, 5)
        m = rng.randint(0, 8)
        edges = []
        for _ in range(m):
            u, v = rng.randrange(n), rng.randrange(n)
            if rng.random() < 0.7:
                if u == v:
                    continue
                u, v = min(u, v), max(u, v)
            edges.append((u, v))
        N = walk_counts(n, edges)
        # selected roots
        R = [a for a in range(n) if rng.random() < 0.5] or [0]
        s = rng.choice(R)
        t = rng.randrange(n)
        kap = {(a, v): rng.randint(0, 3) for a in R for v in range(n)}
        nU, EU, idx = universal_lift(n, edges, roots=R)
        kappa = [1] + [kap.get((a, v), 0) for a in range(n) for v in range(n)]
        got = root_budget_decide(nU, EU, 0, [idx(s, t)], kappa)
        want = all(N[a][v] <= kap[(a, v)] for a in R for v in range(n)) and N[s][t] >= 1
        assert got == want
        cnt += 1
        acc += got
        # two cones: rho -> s in copy 1 (G), rho -> t in copy 2 (reverse of G)
        kp, km = rng.randint(1, 3), rng.randint(1, 3)
        E2 = [(0, 1 + s), (0, 1 + n + t)]
        E2 += [(1 + u, 1 + v) for (u, v) in edges]
        E2 += [(1 + n + v, 1 + n + u) for (u, v) in edges]
        kappa = [1] + [kp] * n + [km] * n
        got = root_budget_decide(1 + 2 * n, E2, 0, [1 + t], kappa)
        want = all(N[s][v] <= kp for v in range(n)) and all(N[v][t] <= km for v in range(n)) \
            and N[s][t] >= 1
        assert got == want
        cnt += 1
        acc += got
    print("Corollary 4.9 reductions (selected roots, two cones): %d instances, %d accepted, 0 mismatches"
          % (cnt, acc))


if __name__ == "__main__":
    main()
