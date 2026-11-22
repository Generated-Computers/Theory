"""Section 3: the capped decider (Listings 1-2) against the definition of STCON_sf.

Checks
  * all simple digraphs (self-loops allowed) on n <= 4 vertices, all s, t, and
    k = 0, 1, 2, 3: DECIDE-STCON-sf accepts exactly the instances of STCON_sf;
  * the same on random simple digraphs with 5 <= n <= 7;
  * the occurrence-indexed multigraph version (Proposition 3.9) on random
    multigraphs with parallel edges;
  * Lemma 3.2-3.6 on the way (tree sizes, overflow soundness, cycle exposure);
  * Remark 3.7: on the directed n-cycle the unfolding to depth nk-1 has exactly
    nk nodes, each endpoint k times, and depth nk-1 with cap nk would accept it.

Usage: python3 check_capped.py [seed]
"""

import random
import sys

from walks import INF, all_simple_digraphs, edges_of, walk_counts


def traverse_simple(adj, n, k, a, b=None, depth=None):
    """Listing 1 for the 0/1 adjacency-matrix model.  depth defaults to n*k;
    the global cap is always n*k + 1 nodes."""
    cap = n * k
    D = cap if depth is None else depth
    stack = []
    current, nxt, d, total = a, 0, 0, 1
    tc = 1 if (b is not None and a == b) else 0
    while True:
        if d == D or nxt >= n:
            if not stack:
                return ("OK", total, tc)
            current, nxt = stack.pop()
            d -= 1
            continue
        w = nxt
        nxt += 1
        if not adj[current][w]:
            continue
        stack.append((current, nxt))
        current, nxt = w, 0
        d += 1
        total += 1
        if total == cap + 1:
            return ("GLOBAL_OVERFLOW",)
        if b is not None and current == b:
            tc = min(k + 1, tc + 1)
            if tc == k + 1:
                return ("TARGET_OVERFLOW",)


def decide_simple(adj, n, s, t, k, depth=None):
    """Listing 2."""
    if k == 0:
        return False
    reached = False
    for a in range(n):
        if traverse_simple(adj, n, k, a, None, depth)[0] != "OK":
            return False
        for b in range(n):
            res = traverse_simple(adj, n, k, a, b, depth)
            if res[0] != "OK":
                return False
            if a == s and b == t and res[2] >= 1:
                reached = True
    return reached


def decide_simple_all(adj, n, k, depth=None):
    """Listing 2 for all (s, t) at once: the traversals do not depend on (s, t),
    which only selects the bit 'reached'.  Returns the accepted set of pairs."""
    if k == 0:
        return set()
    counts = {}
    for a in range(n):
        if traverse_simple(adj, n, k, a, None, depth)[0] != "OK":
            return set()
        for b in range(n):
            res = traverse_simple(adj, n, k, a, b, depth)
            if res[0] != "OK":
                return set()
            counts[(a, b)] = res[2]
    return {p for p, c in counts.items() if c >= 1}


def traverse_multi(n, edges, k, a, b=None):
    """Listing 1, occurrence-indexed version: the continuation index ranges over
    edge occurrences 0..m (m = past the end)."""
    m = len(edges)
    cap = n * k
    stack = []
    current, nxt, d, total = a, 0, 0, 1
    tc = 1 if (b is not None and a == b) else 0
    while True:
        if d == cap or nxt >= m:
            if not stack:
                return ("OK", total, tc)
            current, nxt = stack.pop()
            d -= 1
            continue
        i = nxt
        nxt += 1
        if edges[i][0] != current:
            continue
        stack.append((current, nxt))
        current, nxt = edges[i][1], 0
        d += 1
        total += 1
        if total == cap + 1:
            return ("GLOBAL_OVERFLOW",)
        if b is not None and current == b:
            tc = min(k + 1, tc + 1)
            if tc == k + 1:
                return ("TARGET_OVERFLOW",)


def decide_multi_all(n, edges, k):
    if k == 0:
        return set()
    counts = {}
    for a in range(n):
        if traverse_multi(n, edges, k, a)[0] != "OK":
            return set()
        for b in range(n):
            res = traverse_multi(n, edges, k, a, b)
            if res[0] != "OK":
                return set()
            counts[(a, b)] = res[2]
    return {p for p, c in counts.items() if c >= 1}


def in_language_all(N, n, k):
    """Accepted pairs (s, t) by the definition of STCON_sf."""
    ok = all(N[u][v] <= k for u in range(n) for v in range(n))
    if not ok:
        return set()
    return {(s, t) for s in range(n) for t in range(n) if N[s][t] >= 1}


def check_lemmas(adj, n, k, N):
    """Lemmas 3.3, 3.5, 3.6 for one graph and k >= 1 (tree sizes via the
    reference counts and a direct bounded-depth count)."""
    edges = edges_of(adj)
    cyclic = any(N[v][v] == INF for v in range(n))
    sizes = []
    for a in range(n):
        res = traverse_simple(adj, n, k, a)
        overflow = res[0] != "OK"
        sizes.append(overflow)
        if overflow:
            # Lemma 3.3: overflow => not k-strongly unambiguous
            assert any(N[a][b] > k for b in range(n)), "Lemma 3.3"
        else:
            # Lemma 3.6 (when acyclic): total equals sum of exact counts
            if not cyclic:
                assert res[1] == sum(N[a][b] for b in range(n)), "Lemma 3.6"
    if cyclic:
        assert any(sizes), "Lemma 3.5"
    return True


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 2026
    rng = random.Random(seed)
    total_inst = 0
    accepted = 0
    for n in range(1, 5):
        for adj in all_simple_digraphs(n):
            N = walk_counts(n, edges_of(adj))
            for k in range(0, 4):
                got = decide_simple_all(adj, n, k)
                want = in_language_all(N, n, k)
                assert got == want, (n, adj, k, got, want)
                if k >= 1:
                    check_lemmas(adj, n, k, N)
                total_inst += n * n
                accepted += len(got)
    print("exhaustive n<=4, k<=3: %d instances (G,s,t,k), %d accepted, 0 mismatches"
          % (total_inst, accepted))

    # direct Listing 2 on a random subset, to confirm decide_simple_all
    cnt = 0
    for _ in range(3000):
        n = rng.randint(1, 4)
        adj = [[1 if rng.random() < 0.3 else 0 for _ in range(n)] for _ in range(n)]
        k = rng.randint(0, 3)
        s, t = rng.randrange(n), rng.randrange(n)
        allset = decide_simple_all(adj, n, k)
        assert decide_simple(adj, n, s, t, k) == ((s, t) in allset)
        cnt += 1
    print("Listing 2 run per (s,t) agrees with the all-pairs run on %d random instances" % cnt)

    # random larger simple digraphs, biased towards DAGs so that acceptance occurs
    cnt = acc = 0
    for _ in range(1500):
        n = rng.randint(5, 7)
        p = rng.choice([0.15, 0.25, 0.4])
        dag = rng.random() < 0.7
        adj = [[0] * n for _ in range(n)]
        for i in range(n):
            for j in range(n):
                if (not dag or i < j) and rng.random() < p:
                    adj[i][j] = 1
        N = walk_counts(n, edges_of(adj))
        mx = max(N[u][v] for u in range(n) for v in range(n))
        ks = [rng.randint(1, 4)]
        if mx != INF:
            ks += [mx, max(1, mx - 1)]
        for k in ks:
            got = decide_simple_all(adj, n, k)
            want = in_language_all(N, n, k)
            assert got == want
            cnt += n * n
            acc += len(got)
    print("random simple digraphs 5<=n<=7: %d instances, %d accepted, 0 mismatches" % (cnt, acc))

    # multigraphs (Proposition 3.9)
    cnt = acc = 0
    for _ in range(3000):
        n = rng.randint(1, 5)
        m = rng.randint(0, 8)
        dag = rng.random() < 0.7
        edges = []
        for _ in range(m):
            u, v = rng.randrange(n), rng.randrange(n)
            if dag:
                if u == v:
                    continue
                u, v = min(u, v), max(u, v)
            edges.append((u, v))
        N = walk_counts(n, edges)
        mx = max(N[u][v] for u in range(n) for v in range(n))
        ks = [rng.randint(0, 4)]
        if mx != INF:
            ks += [mx, max(1, mx - 1)]
        for k in ks:
            got = decide_multi_all(n, edges, k)
            want = in_language_all(N, n, k)
            assert got == want, (n, edges, k)
            cnt += n * n
            acc += len(got)
    print("random multigraphs n<=5, m<=8 (parallel edges): %d instances, %d accepted, 0 mismatches"
          % (cnt, acc))

    # Remark 3.7
    for n in range(1, 8):
        adj = [[0] * n for _ in range(n)]
        for i in range(n):
            adj[i][(i + 1) % n] = 1
        for k in range(1, 5):
            # depth nk-1: exactly nk nodes, each endpoint k times
            for b in range(n):
                res = traverse_simple(adj, n, k, 0, b, depth=n * k - 1)
                assert res[0] == "OK" and res[1] == n * k and res[2] == k
            # depth nk: overflow at node nk+1
            assert traverse_simple(adj, n, k, 0)[0] == "GLOBAL_OVERFLOW"
            # the depth-(nk-1) variant of Listing 2 accepts the cycle, wrongly
            assert decide_simple(adj, n, 0, n - 1, k, depth=n * k - 1) is True
            assert decide_simple(adj, n, 0, n - 1, k) is False
    print("Remark 3.7 confirmed on directed n-cycles, n<=7, k<=4")


if __name__ == "__main__":
    main()
