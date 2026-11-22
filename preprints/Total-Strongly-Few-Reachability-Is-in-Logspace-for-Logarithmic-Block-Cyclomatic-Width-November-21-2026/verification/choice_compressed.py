"""Checks for Section 3: the branching-budget identity (Theorem 3.1) and the
total decider of Theorem 3.4 (choice-compressed search with the compact
choice string).

The decider stores only: the choice string sigma (bits), the depth D, the
node counter, the target counter and loop indices.  The current vertex is
recomputed by replaying sigma from the root, exactly as in the paper.
We compare with brute-force walk counts (matrix powers) on
  - all digraphs with loops on n <= 3 vertices, k = 1..4,
  - all loopless digraphs on n = 4 vertices, k = 1..3,
  - random digraphs and random DAGs on 5..9 vertices,
and record the largest |sigma| against the bound k*lambda - 1.
Usage: python3 choice_compressed.py [seed]
"""
import sys
import random
from math import ceil, log2
from common import (all_digraphs, random_digraph, random_dag, reverse, succ,
                    walk_counts, in_stcon_sf, valid, is_acyclic, INF)


class Reject(Exception):
    pass


def width(d):
    return ceil(log2(d)) if d >= 2 else 0


def replay(adj, a, sigma, D):
    """Follow sigma from root a for D steps.  Returns the endpoint and the
    list of branching ancestors (depth, field position, width, value, d)."""
    v = a
    pos = 0
    branches = []
    for depth in range(D):
        S = succ(adj, v)
        d = len(S)
        if d == 1:
            v = S[0]
        else:
            w = width(d)
            val = 0
            for bit in sigma[pos:pos + w]:
                val = 2 * val + bit
            assert val < d
            branches.append((depth, pos, w, val, d))
            pos += w
            v = S[val]
    assert pos == len(sigma)
    return v, branches


def traverse(adj, a, b, k, cap, stats):
    """Canonical DFS of the unfolding tree from a with all four caps.
    Returns min(N(a,b), k) or raises Reject."""
    n = len(adj)
    sigma, D = [], 0
    total = 1
    cnt = 1 if a == b else 0

    def enter(v):
        nonlocal total, cnt
        total += 1
        if total == n * k + 1:
            raise Reject("node cap")
        if v == b:
            cnt += 1
            if cnt == k + 1:
                raise Reject("target cap")

    while True:
        v, branches = replay(adj, a, sigma, D)
        S = succ(adj, v)
        if S:                                   # descend to first child
            if D + 1 == n:
                raise Reject("depth cap")
            if len(S) >= 2:
                w = width(len(S))
                if len(sigma) + w > cap:
                    raise Reject("stack cap")
                sigma = sigma + [0] * w
            D += 1
            stats["maxsigma"] = max(stats["maxsigma"], len(sigma))
            enter(replay(adj, a, sigma, D)[0])
        else:                                   # leaf: move to next sibling
            for (depth, pos, w, val, d) in reversed(branches):
                if val < d - 1:
                    nv = val + 1
                    sigma = sigma[:pos] + [(nv >> (w - 1 - i)) & 1 for i in range(w)]
                    D = depth + 1
                    enter(replay(adj, a, sigma, D)[0])
                    break
            else:
                return cnt


def decide(adj, s, t, k, stats):
    """The total decider of Theorem 3.4.  Returns (accept, counts or None)."""
    n = len(adj)
    if k == 0:
        return False, None
    outd = [sum(adj[v]) for v in range(n)]
    ind = [sum(adj[u][v] for u in range(n)) for v in range(n)]
    tplus = sum(1 for v in range(n) if outd[v] == 0)
    tminus = sum(1 for v in range(n) if ind[v] == 0)
    if tplus == 0 or tminus == 0:
        return False, None
    flipped = tminus < tplus
    if flipped:
        adj = reverse(adj)
        s, t = t, s
        lam = tminus
    else:
        lam = tplus
    cap = k * lam - 1
    counts = [[0] * n for _ in range(n)]
    try:
        for a in range(n):
            for b in range(n):
                counts[a][b] = traverse(adj, a, b, k, cap, stats)
    except Reject as e:
        stats[str(e)] = stats.get(str(e), 0) + 1
        return False, None
    if flipped:   # report counts of the original orientation
        counts = [[counts[b][a] for b in range(n)] for a in range(n)]
        s, t = t, s
    return counts[s][t] >= 1, counts


def leaves(adj, a):
    """Number of maximal walks from a (DAG only)."""
    S = succ(adj, a)
    return 1 if not S else sum(leaves(adj, w) for w in S)


def check_identity(adj, N):
    """Theorem 3.1: L_a = 1 + sum_v N(a,v)(d+(v)-1) over non-sinks."""
    n = len(adj)
    for a in range(n):
        La = leaves(adj, a)
        rhs = 1 + sum(N[a][v] * (sum(adj[v]) - 1) for v in range(n) if sum(adj[v]) > 0)
        if La != rhs:
            return False
    return True


def run_case(adj, k, stats, tally):
    n = len(adj)
    ok, N = valid(adj, k)
    # one decider run gives the answer for every (s,t): the traversals do not
    # depend on (s,t) except for the orientation, which is symmetric.
    for (s, t) in [(0, n - 1), (n - 1, 0)] if n > 1 else [(0, 0)]:
        st = {"maxsigma": 0}
        acc, counts = decide(adj, s, t, k, st)
        want = ok and N[s][t] >= 1
        tally["cases"] += 1
        if acc != want:
            tally["errors"] += 1
            print("MISMATCH", adj, s, t, k, acc, want)
        if ok:
            tplus = sum(1 for v in range(n) if sum(adj[v]) == 0)
            tminus = sum(1 for v in range(n) if sum(adj[u][v] for u in range(n)) == 0)
            lam = min(tplus, tminus)
            bound = k * lam - 1
            tally["valid"] += 1
            if counts is None:
                tally["errors"] += 1
                print("valid input rejected", adj, k)
            else:
                if any(counts[a][b] != N[a][b] for a in range(n) for b in range(n)):
                    tally["errors"] += 1
                    print("COUNT MISMATCH", adj, k)
            tally["maxsigma"] = max(tally["maxsigma"], st["maxsigma"])
            if st["maxsigma"] > bound:
                tally["errors"] += 1
                print("SIGMA BOUND VIOLATED", adj, k, st["maxsigma"], bound)
            if bound > 0:
                tally["ratio"] = max(tally["ratio"], st["maxsigma"] / bound)
        for key in st:
            if key != "maxsigma":
                stats[key] = stats.get(key, 0) + st[key]


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 2026
    rng = random.Random(seed)
    tally = {"cases": 0, "errors": 0, "valid": 0, "maxsigma": 0, "ratio": 0.0}
    stats = {}
    # identity of Theorem 3.1 on all DAGs with n <= 5
    nid = 0
    for n in range(1, 6):
        for adj in all_digraphs(n):
            if is_acyclic(adj):
                N = walk_counts(adj)
                nid += 1
                if not check_identity(adj, N):
                    tally["errors"] += 1
                    print("IDENTITY FAILS", adj)
    print(f"branching-budget identity: {nid} DAGs on <= 5 vertices checked")
    for n in range(1, 4):
        for adj in all_digraphs(n, loops=True):
            for k in range(1, 5):
                run_case(adj, k, stats, tally)
    for adj in all_digraphs(4):
        for k in range(1, 4):
            run_case(adj, k, stats, tally)
    for _ in range(1500):
        n = rng.randint(5, 9)
        if rng.random() < 0.5:
            adj = random_dag(n, rng.choice([0.15, 0.25, 0.35]), rng)
        else:
            adj = random_digraph(n, rng.choice([0.1, 0.2]), rng, loops=rng.random() < 0.2)
        N = walk_counts(adj)
        finite = [x for row in N for x in row if x != INF]
        kmax = max(finite) if finite else 1
        for k in sorted({1, 2, max(1, kmax - 1), kmax, kmax + 1}):
            run_case(adj, k, stats, tally)
    print(f"decider cases: {tally['cases']}, of which valid inputs: {tally['valid']}")
    print(f"rejections by cap (invalid inputs): {stats}")
    print(f"largest |sigma| on valid inputs: {tally['maxsigma']}, "
          f"largest ratio |sigma|/(k*lambda-1): {tally['ratio']:.3f}")
    print(f"errors: {tally['errors']}")


if __name__ == "__main__":
    main()
