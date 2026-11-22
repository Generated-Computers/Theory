"""Section 5: the certified finite-field lift with the actual prime of the paper.

For a root-budget instance (H, r, F, kappa) with B = sum kappa >= 1 and kappa(r) >= 1:
S = sum_v binom(kappa(v), 2), p = least prime > max{m, B*S, 2}, and for alpha in F_p
the layered lift H_alpha on states (v, d, z), 0 <= d <= B, with
(u, d, z) -> (v, d+1, alpha*z + i mod p) for edge occurrence e_i = (u, v).

The controller of Definition 5.7 (Theorem 5.8) is run as written: scan alpha = 0, 1, ..., p-1; the
certification query asks whether H_alpha is reach-unambiguous from (r,0,0) (computed
here by counting lifted paths, saturated at 2, over the reachable states); at the first
certified alpha the fibre sizes are compared with the budgets.

Checks
  * the controller accepts exactly RootBudget (all simple digraphs n <= 3, all
    kappa in {0,1,2}^n, several F; random multigraphs n <= 5);
  * Lemma 5.3: on every valid instance some alpha is certified, and the number of
    non-separating alpha is at most (B-1)S;
  * Lemma 5.6: for EVERY certified alpha (valid or not) the fibre sizes equal the
    bounded walk counts N^{<=B}(r, v);
  * p > m, so edge indices are distinct and nonzero mod p;
  * Remark 5.9 (diamond);
  * Corollary 5.11: STCON_sf through U(G) on a sample of small instances.

Usage: python3 check_lift.py [seed]
"""

import itertools
import random
import sys

from walks import INF, all_simple_digraphs, edges_of, walk_counts, bounded_counts_from, \
    least_prime_above


def prime_for(kappa, m):
    B = sum(kappa)
    S = sum(c * (c - 1) // 2 for c in kappa)
    return least_prime_above(max(m, B * S, 2)), B, S


def lift_counts(n, edges, r, B, p, alpha):
    """Path counts (saturated at 2) from (r,0,0) to every reachable lifted state."""
    layer = {(r, 0): 1}          # (v, z) -> count, for the current depth d
    states = {}                  # (v, d, z) -> count
    for (v, z), c in layer.items():
        states[(v, 0, z)] = c
    for d in range(B):
        nxt = {}
        for (u, z), c in layer.items():
            for i, (a, b) in enumerate(edges, start=1):
                if a == u:
                    key = (b, (alpha * z + i) % p)
                    nxt[key] = min(2, nxt.get(key, 0) + c)
        layer = nxt
        for (v, z), c in layer.items():
            states[(v, d + 1, z)] = c
    return states


def controller(n, edges, r, F, kappa, stats=None, check_all_alpha=False, bc=None):
    """The controller of Definition 5.7.  Returns accept/reject."""
    B = sum(kappa)
    if B == 0 or kappa[r] == 0:
        return False
    m = len(edges)
    p, B, S = prime_for(kappa, m)
    assert p > m and p > (B - 1) * S
    decision = None
    certified_count = 0
    for alpha in range(p):
        st = lift_counts(n, edges, r, B, p, alpha)
        if any(c >= 2 for c in st.values()):
            continue                          # certification fails
        certified_count += 1
        fib = [0] * n
        for (v, d, z) in st:
            fib[v] += 1
        if bc is not None:                    # Lemma 5.6
            assert fib == bc[B], ("Lemma 5.6", n, edges, r, kappa, alpha)
        if decision is None:
            if any(fib[v] > kappa[v] for v in range(n)):
                decision = False
            else:
                decision = any(fib[f] >= 1 for f in F)
            if not check_all_alpha:
                break
    if stats is not None:
        stats["certified_alphas"] = certified_count
        stats["p"] = p
        stats["B"] = B
        stats["S"] = S
    return False if decision is None else decision


def root_budget_def(Nrow, F, kappa):
    return all(Nrow[q] <= kappa[q] for q in range(len(kappa))) and \
        any(Nrow[f] >= 1 for f in F)


def run_instance(n, edges, r, F, kappa, N, agg, check_all_alpha):
    valid = all(N[r][q] <= kappa[q] for q in range(n))
    B = sum(kappa)
    bc = bounded_counts_from(n, edges, r, B) if B >= 1 else None
    st = {}
    got = controller(n, edges, r, F, kappa, st, check_all_alpha, bc)
    want = root_budget_def(N[r], F, kappa)
    assert got == want, (n, edges, r, F, kappa)
    agg["inst"] += 1
    agg["acc"] += got
    if B >= 1 and kappa[r] >= 1 and check_all_alpha:
        p, S = st["p"], st["S"]
        bad = p - st["certified_alphas"]
        if valid:
            agg["valid"] += 1
            assert st["certified_alphas"] >= 1, "Lemma 5.3"
            assert bad <= (B - 1) * S, "Lemma 5.3 count"
            agg["max_bad_ratio"] = max(agg["max_bad_ratio"],
                                       bad / ((B - 1) * S) if (B - 1) * S else 0)
        else:
            if st["certified_alphas"] == 0:
                agg["invalid_uncertified"] += 1
            else:
                agg["invalid_certified"] += 1


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 2026
    rng = random.Random(seed)
    agg = {"inst": 0, "acc": 0, "valid": 0, "invalid_uncertified": 0,
           "invalid_certified": 0, "max_bad_ratio": 0.0}
    for n in range(1, 4):
        for adj in all_simple_digraphs(n):
            edges = edges_of(adj)
            N = walk_counts(n, edges)
            for r in range(n):
                for kappa in itertools.product(range(3), repeat=n):
                    F = [(r + 1) % n] if n > 1 else [0]
                    run_instance(n, edges, r, F, list(kappa), N, agg, check_all_alpha=True)
    print("exhaustive n<=3, kappa in {0,1,2}^n, all alpha scanned: %d instances, %d accepted;"
          % (agg["inst"], agg["acc"]))
    print("  valid: %d (each had a certified alpha; max (#bad alpha)/((B-1)S) = %.3f);"
          % (agg["valid"], agg["max_bad_ratio"]))
    print("  invalid with no certified alpha: %d; invalid with a certified alpha (rejected by"
          " the budget comparison): %d; Lemma 5.6 held for every certified alpha"
          % (agg["invalid_uncertified"], agg["invalid_certified"]))

    agg = {"inst": 0, "acc": 0, "valid": 0, "invalid_uncertified": 0,
           "invalid_certified": 0, "max_bad_ratio": 0.0}
    for _ in range(3000):
        n = rng.randint(1, 6)
        m = rng.randint(0, 8)
        edges = []
        for _ in range(m):
            u, v = rng.randrange(n), rng.randrange(n)
            if rng.random() < 0.8:
                if u == v:
                    continue
                u, v = min(u, v), max(u, v)
            edges.append((u, v))
        N = walk_counts(n, edges)
        r = rng.randrange(n)
        if rng.random() < 0.6 and all(x != INF for x in N[r]):
            kappa = [max(0, N[r][q] + rng.choice([0, 0, 0, 1, -1])) for q in range(n)]
        else:
            kappa = [rng.randint(0, 3) for _ in range(n)]
        if sum(kappa) > 16:
            continue
        F = [q for q in range(n) if rng.random() < 0.4]
        run_instance(n, edges, r, F, kappa, N, agg, check_all_alpha=True)
    print("random multigraphs n<=6, m<=8, all alpha scanned: %d instances, %d accepted; valid %d;"
          " invalid uncertified %d; invalid certified %d; max bad ratio %.3f"
          % (agg["inst"], agg["acc"], agg["valid"], agg["invalid_uncertified"],
             agg["invalid_certified"], agg["max_bad_ratio"]))

    # Remark 5.9: diamond r=0, a=1, b=2, v=3; e1=r->a, e2=r->b, e3=a->v, e4=b->v
    edges = [(0, 1), (0, 2), (1, 3), (2, 3)]
    for kappa, p_expected, bad_expected, accept in (([1, 1, 1, 2], 7, [6], True),
                                                     ([1, 1, 1, 1], 5, [4], False)):
        p, B, S = prime_for(kappa, 4)
        assert p == p_expected
        bad = [al for al in range(p)
               if any(c >= 2 for c in lift_counts(4, edges, 0, B, p, al).values())]
        assert bad == bad_expected, (kappa, bad)
        assert all((al * 1 + 3) % p == (al * 2 + 4) % p for al in bad)
        assert controller(4, edges, 0, [3], kappa) is accept
    print("Remark 5.9 confirmed: budgets (1,1,1,2): p=7, only alpha=6 collides, accepted;"
          " budgets (1,1,1,1): p=5, only alpha=4 collides, rejected by the fibre count 2 > 1")

    # Corollary 5.11: STCON_sf through U(G) (root rho budget 1, (a,v) budget k)
    cnt = acc = 0
    for _ in range(60):
        n = rng.randint(1, 3)
        dag = rng.random() < 0.75
        adj = [[0] * n for _ in range(n)]
        for i in range(n):
            for j in range(n):
                if (not dag or i < j) and rng.random() < 0.5:
                    adj[i][j] = 1
        edges = edges_of(adj)
        N = walk_counts(n, edges)
        k = rng.randint(0, 2)
        s, t = rng.randrange(n), rng.randrange(n)
        nU = 1 + n * n
        idx = lambda a, v: 1 + a * n + v
        EU = [(0, idx(a, a)) for a in range(n)] + \
             [(idx(a, u), idx(a, v)) for a in range(n) for (u, v) in edges]
        kappa = [1] + [k] * (n * n)
        got = controller(nU, EU, 0, [idx(s, t)], kappa)
        want = all(N[u][v] <= k for u in range(n) for v in range(n)) and N[s][t] >= 1
        assert got == want
        cnt += 1
        acc += got
    print("Corollary 5.11 (STCON_sf via U(G) and the certified lift): %d instances, %d accepted,"
          " 0 mismatches" % (cnt, acc))


if __name__ == "__main__":
    main()
