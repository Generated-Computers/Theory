"""Checks for the collision-averaged fingerprint decoding (Section 7).

  python3 fingerprints.py [trials]     (default 3000)

Random multigraphs (loops and parallel edges allowed), root r, length bound B and
cap K.  With q0 = (B-1) C(K+1,2) + 1, the least prime p > max(m, q0) and the
evaluation points A = {0, ..., q0-1}, the census D_v is computed by breadth-first
search in the aggregate lift (states (alpha, v, d, z)).  Checked:
  (1) min{c_v, K+1} = min{ceil(D_v/q0), K+1}, c_v = N^{<=B}(r, v);
  (2) c_v <= t  iff  D_v <= q0 t, for all 0 <= t <= K;
  (3) the maximum variant: min{c_v, K+1} = min{max_alpha D_{v,alpha}, K+1};
  (4) the lift is faithful: for instances with few walks, D_{v,alpha} equals the
      number of distinct pairs (d, h_alpha(P)) over explicitly enumerated walks P;
  (5) the FL^NL root-budget decision (all D_v <= q0 kappa(v) and a positive decoded
      count in F) agrees with exact RootBudget membership (exact counts with INF);
  (6) same with A a random q0-subset of F_p.
It also reports how often the floor formula min{floor(D_v/q0), K+1} is wrong
(it is wrong whenever collisions occur and c_v <= K), and how often the maximum
variant fails with the single evaluation point alpha = 0 (it should fail often).
"""
import math
import random
import sys

from walks import INF, bounded_counts_from, exact_counts_from


def next_prime(x):
    p = x + 1
    while True:
        if p >= 2 and all(p % d for d in range(2, int(p ** 0.5) + 1)):
            return p
        p += 1


def random_multigraph(rng):
    n = rng.randrange(1, 7)
    m = rng.randrange(0, 11) if rng.random() < 0.5 else rng.randrange(6, 16)
    edges = [(rng.randrange(n), rng.randrange(n)) for _ in range(m)]
    return n, edges


def census(n, edges, r, B, A, p):
    """Return per-alpha counts D[alpha][v] of reachable lifted states in fiber v."""
    out = {}
    for alpha in A:
        seen = {(r, 0, 0)}
        frontier = [(r, 0, 0)]
        while frontier:
            nxt = []
            for (u, d, z) in frontier:
                if d == B:
                    continue
                for i, (x, y) in enumerate(edges, start=1):
                    if x == u:
                        st = (y, d + 1, (alpha * z + i) % p)
                        if st not in seen:
                            seen.add(st)
                            nxt.append(st)
            frontier = nxt
        cnt = [0] * n
        for (v, d, z) in seen:
            cnt[v] += 1
        out[alpha] = cnt
    return out


def enumerate_walks(n, edges, r, B, limit):
    walks = [[]]
    ends = [r]
    res = [([], r)]
    frontier = [([], r)]
    for _ in range(B):
        nxt = []
        for (w, v) in frontier:
            for i, (x, y) in enumerate(edges, start=1):
                if x == v:
                    nxt.append((w + [i], y))
                    if len(res) + len(nxt) > limit:
                        return None
        res.extend(nxt)
        frontier = nxt
    return res


def main():
    trials = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
    rng = random.Random(2026)
    s = dict(endpoints=0, bad1=0, bad2=0, bad3=0, bad4=0, faith=0, bad5=0, bad6=0,
             floor_wrong=0, single_wrong=0, single_tests=0)
    for _ in range(trials):
        n, edges = random_multigraph(rng)
        m = len(edges)
        adj = [dict() for _ in range(n)]
        for (x, y) in edges:
            adj[x][y] = adj[x].get(y, 0) + 1
        r = rng.randrange(n)
        B = rng.randrange(1, 7)
        K = rng.randrange(1, 5)
        q0 = (B - 1) * math.comb(K + 1, 2) + 1
        p = next_prime(max(m, q0))
        A = list(range(q0))
        cen = census(n, edges, r, B, A, p)
        c = bounded_counts_from(adj, r, B)
        for v in range(n):
            s["endpoints"] += 1
            D = sum(cen[a][v] for a in A)
            dec = min(-(-D // q0), K + 1)
            s["bad1"] += min(c[v], K + 1) != dec
            for t in range(K + 1):
                s["bad2"] += (c[v] <= t) != (D <= q0 * t)
            s["bad3"] += min(c[v], K + 1) != min(max(cen[a][v] for a in A), K + 1)
            s["floor_wrong"] += min(c[v], K + 1) != min(D // q0, K + 1)
        # (4) faithfulness of the lift against explicit walks
        W = enumerate_walks(n, edges, r, B, 4000)
        if W is not None:
            s["faith"] += 1
            for a in A:
                imgs = [set() for _ in range(n)]
                for (w, v) in W:
                    h = 0
                    for i in w:
                        h = (a * h + i) % p
                    imgs[v].add((len(w), h))
                if [len(x) for x in imgs] != cen[a]:
                    s["bad4"] += 1
        # (5) root-budget decision with K = max kappa, B = sum kappa
        kap = [rng.randrange(0, 3) for _ in range(n)]
        F = [v for v in range(n) if rng.random() < 0.5]
        Bk, Kk = sum(kap), max(kap)
        exact = exact_counts_from(adj, r)
        member = all(exact[v] <= kap[v] for v in range(n)) and any(exact[f] >= 1 for f in F)
        if Bk == 0 or Kk == 0:
            decision = False  # handled directly: the empty walk at r violates kappa(r) = 0
        else:
            q = (Bk - 1) * math.comb(Kk + 1, 2) + 1
            pp = next_prime(max(m, q))
            for trial, AA in enumerate((list(range(q)), rng.sample(range(pp), q))):
                cc = census(n, edges, r, Bk, AA, pp)
                Dv = [sum(cc[a][v] for a in AA) for v in range(n)]
                dec = [min(-(-Dv[v] // q), Kk + 1) for v in range(n)]
                decision = all(Dv[v] <= q * kap[v] for v in range(n)) and any(dec[f] >= 1 for f in F)
                s["bad5" if trial == 0 else "bad6"] += decision != member
            continue
        s["bad5"] += decision != member
        # control: a single evaluation point
    for _ in range(trials):
        n, edges = random_multigraph(rng)
        adj = [dict() for _ in range(n)]
        for (x, y) in edges:
            adj[x][y] = adj[x].get(y, 0) + 1
        r = rng.randrange(n)
        B, K = rng.randrange(2, 7), rng.randrange(2, 5)
        p = next_prime(max(len(edges), 3))
        cen = census(n, edges, r, B, [0], p)
        c = bounded_counts_from(adj, r, B)
        for v in range(n):
            s["single_tests"] += 1
            s["single_wrong"] += min(c[v], K + 1) != min(cen[0][v], K + 1)
    print("endpoints checked:", s["endpoints"])
    print("(1) ceiling decoding failures:", s["bad1"])
    print("(2) threshold equivalence failures:", s["bad2"])
    print("(3) maximum-variant failures:", s["bad3"])
    print("(4) lift faithfulness: %d instances enumerated, failures: %d" % (s["faith"], s["bad4"]))
    print("(5) root-budget decision (A = {0..q0-1}) failures:", s["bad5"])
    print("(6) root-budget decision (random A) failures:", s["bad6"])
    print("control: floor formula wrong on %d endpoints" % s["floor_wrong"])
    print("control: single evaluation point alpha=0 wrong on %d of %d endpoints"
          % (s["single_wrong"], s["single_tests"]))


if __name__ == "__main__":
    main()
