"""Checks for the single GapL zero test (Section 6).

  python3 zero_test.py

(U) Uniform threshold: g = P_st^2 + sum_{(u,v) != (s,t)} P_uv^2 with
    f_uv = N^{<= nk}(u,v), P_uv = prod_{j=0..k} (f_uv - j), P_st = prod_{j=1..k}
    (f_st - j).  g = 0 iff <G,s,t,1^k> in STCON_sf, on all digraphs with n <= 3
    (loops allowed), all s, t and k = 1, 2, 3, and on 3000 random digraphs with
    n = 4, 5.
(B) Pair budgets: f_uv = N^{<= L}(u,v), L = max_u sum_v kappa(u,v); P_uv with
    j = 0..kappa(u,v), P_st with j = 1..kappa(s,t) (kappa(s,t) = 0 rejected).
    g = 0 iff PairBudget membership, on 3000 random instances.
(R) Root budgets: f_v = N^{<= B}(r,v), P_v with j = 0..kappa(v), f_F = sum_{v in F} f_v,
    P_F = prod_{j=1..B} (f_F - j) (B = 0 rejected).  g = 0 iff RootBudget membership,
    on 3000 random instances.
"""
import random

from walks import bounded_counts_from, exact_counts, exact_counts_from, from_matrix


def prod_shift(f, lo, hi):
    out = 1
    for j in range(lo, hi + 1):
        out *= f - j
    return out


def uniform_g(adj, s, t, k):
    n = len(adj)
    g = 0
    for u in range(n):
        f = bounded_counts_from(adj, u, n * k)
        for v in range(n):
            if (u, v) == (s, t):
                g += prod_shift(f[v], 1, k) ** 2
            else:
                g += prod_shift(f[v], 0, k) ** 2
    return g


def main():
    rng = random.Random(2026)
    tests = bad = members = 0
    for n in range(1, 4):
        for bits in range(1 << (n * n)):
            adj = from_matrix(bits, n)
            N = exact_counts(adj)
            for k in (1, 2, 3):
                allpairs = all(N[u][v] <= k for u in range(n) for v in range(n))
                for s in range(n):
                    for t in range(n):
                        member = allpairs and N[s][t] >= 1
                        tests += 1
                        members += member
                        bad += (uniform_g(adj, s, t, k) == 0) != member
    for _ in range(3000):
        n = rng.randrange(4, 6)
        dens = rng.random() * 0.5
        adj = [dict() for _ in range(n)]
        for u in range(n):
            for v in range(u + 1, n) if rng.random() < 0.8 else range(n):
                if rng.random() < dens:
                    adj[u][v] = 1
        N = exact_counts(adj)
        k = rng.randrange(1, 4)
        s, t = rng.randrange(n), rng.randrange(n)
        member = all(N[u][v] <= k for u in range(n) for v in range(n)) and N[s][t] >= 1
        tests += 1
        members += member
        bad += (uniform_g(adj, s, t, k) == 0) != member
    print("(U) uniform threshold: %d instances (%d members), %d failures" % (tests, members, bad))

    tests = bad = members = 0
    for _ in range(3000):
        n = rng.randrange(1, 5)
        adj = [dict() for _ in range(n)]
        acyclic_bias = rng.random() < 0.7
        for u in range(n):
            for v in range(n):
                if (v > u or not acyclic_bias) and rng.random() < 0.4:
                    adj[u][v] = 1
        kap = [[rng.randrange(0, 4) for _ in range(n)] for _ in range(n)]
        for u in range(n):
            kap[u][u] = max(kap[u][u], rng.randrange(0, 2))
        s, t = rng.randrange(n), rng.randrange(n)
        N = exact_counts(adj)
        member = all(N[u][v] <= kap[u][v] for u in range(n) for v in range(n)) and N[s][t] >= 1
        if kap[s][t] == 0:
            zero = False
        else:
            L = max(sum(kap[u]) for u in range(n))
            g = 0
            for u in range(n):
                f = bounded_counts_from(adj, u, L)
                for v in range(n):
                    if (u, v) == (s, t):
                        g += prod_shift(f[v], 1, kap[s][t]) ** 2
                    else:
                        g += prod_shift(f[v], 0, kap[u][v]) ** 2
            zero = g == 0
        tests += 1
        members += member
        bad += zero != member
    print("(B) pair budgets: %d instances (%d members), %d failures" % (tests, members, bad))

    tests = bad = members = 0
    for _ in range(3000):
        n = rng.randrange(1, 6)
        adj = [dict() for _ in range(n)]
        acyclic_bias = rng.random() < 0.7
        for u in range(n):
            for v in range(n):
                if (v > u or not acyclic_bias) and rng.random() < 0.4:
                    adj[u][v] = adj[u].get(v, 0) + rng.randrange(1, 3)  # parallel edges
        r = rng.randrange(n)
        kap = [rng.randrange(0, 4) for _ in range(n)]
        kap[r] = max(kap[r], rng.randrange(0, 2))
        F = [v for v in range(n) if rng.random() < 0.4]
        B = sum(kap)
        ex = exact_counts_from(adj, r)
        member = all(ex[v] <= kap[v] for v in range(n)) and any(ex[f] >= 1 for f in F)
        if B == 0:
            zero = False
        else:
            f = bounded_counts_from(adj, r, B)
            fF = sum(f[v] for v in F)
            g = sum(prod_shift(f[v], 0, kap[v]) ** 2 for v in range(n)) + prod_shift(fF, 1, B) ** 2
            zero = g == 0
        tests += 1
        members += member
        bad += zero != member
    print("(R) root budgets (multigraphs): %d instances (%d members), %d failures" % (tests, members, bad))


if __name__ == "__main__":
    main()
