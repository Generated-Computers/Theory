"""Checks for Section 8 (robustification, Theorem 8.1) and Section 7
(path flow and rank-one updates, Propositions 7.1 and 7.2), plus the
second-path construction of Proposition 8.4.

Robustification: for G and rho we build G_rho and check by brute force
  (1)-(3) all walk counts (finite and infinite) between the listed vertex
          types, and that every other off-diagonal count is at most one;
  (4)     k-strong unambiguity of G and G_rho agree for k = 1..4;
  (5)     the s-t count and the live set {x : s ~> x ~> t} agree;
  (6)     minimum degree rho, vertex connectivity rho (all deletion sets of
          size rho-1, and one explicit separating set of size rho), edge
          connectivity rho (max flow), diameter <= 4.
Usage: python3 robustification.py [seed]
"""
import sys
import random
import itertools
from collections import deque
from common import (all_digraphs, random_digraph, random_dag, components, INF,
                    walk_counts, is_acyclic)


def fast_counts(adj):
    """Walk counts with INF, by DP on the acyclic part (fast for ~50 vertices)."""
    n = len(adj)
    out = [[w for w in range(n) if adj[v][w]] for v in range(n)]
    reach = []
    for u in range(n):
        seen = [False] * n
        seen[u] = True
        dq = deque([u])
        while dq:
            x = dq.popleft()
            for w in out[x]:
                if not seen[w]:
                    seen[w] = True
                    dq.append(w)
        reach.append(seen)
    oncyc = [any(reach[w][c] for w in out[c]) for c in range(n)]
    # DP on non-cycle vertices in reverse topological order
    keep = [v for v in range(n) if not oncyc[v]]
    indeg = {v: 0 for v in keep}
    for v in keep:
        for w in out[v]:
            if not oncyc[w]:
                indeg[w] += 1
    order, dq = [], deque(v for v in keep if indeg[v] == 0)
    while dq:
        x = dq.popleft()
        order.append(x)
        for w in out[x]:
            if not oncyc[w]:
                indeg[w] -= 1
                if indeg[w] == 0:
                    dq.append(w)
    H = {v: [0] * n for v in keep}
    for v in reversed(order):
        H[v][v] += 1
        for w in out[v]:
            if not oncyc[w]:
                for x in range(n):
                    H[v][x] += H[w][x]
    N = [[0] * n for _ in range(n)]
    for u in range(n):
        for v in range(n):
            if any(oncyc[c] and reach[u][c] and reach[c][v] for c in range(n)):
                N[u][v] = INF
            elif reach[u][v]:
                N[u][v] = H[u][v]
    return N, reach


def robustify(adj, rho):
    n0 = len(adj)
    h = rho - 1
    N = max(n0, rho)
    idx = {}
    nxt = N
    for v in range(N):
        for i in range(h):
            idx[("a", v, i)] = nxt; nxt += 1
        for i in range(h):
            idx[("b", v, i)] = nxt; nxt += 1
    for j in range(h):
        idx[("p", j)] = nxt; nxt += 1
    for j in range(h):
        idx[("q", j)] = nxt; nxt += 1
    R = [[0] * nxt for _ in range(nxt)]
    for u in range(n0):
        for v in range(n0):
            R[u][v] = adj[u][v]
    for v in range(N):
        for i in range(h):
            a, b = idx[("a", v, i)], idx[("b", v, i)]
            R[a][v] = 1
            R[v][b] = 1
            for j in range(h):
                R[a][idx[("q", j)]] = 1
                R[idx[("p", j)]][b] = 1
    return R, idx, N


def und(R):
    n = len(R)
    return [(u, v) for u in range(n) for v in range(u + 1, n) if R[u][v] or R[v][u]]


def maxflow_und(n, edges, s, t):
    cap = {}
    nbr = [set() for _ in range(n)]
    for (u, v) in edges:
        cap[(u, v)] = cap.get((u, v), 0) + 1
        cap[(v, u)] = cap.get((v, u), 0) + 1
        nbr[u].add(v)
        nbr[v].add(u)
    flow = 0
    while True:
        prev = {s: None}
        dq = deque([s])
        while dq and t not in prev:
            x = dq.popleft()
            for y in nbr[x]:
                if y not in prev and cap[(x, y)] > 0:
                    prev[y] = x
                    dq.append(y)
        if t not in prev:
            return flow
        y = t
        while prev[y] is not None:
            x = prev[y]
            cap[(x, y)] -= 1
            cap[(y, x)] += 1
            y = x
        flow += 1


def check_robust(adj, rho, tally, full_connectivity=True):
    n0 = len(adj)
    R, idx, Ncore = robustify(adj, rho)
    h = rho - 1
    NG, reachG = fast_counts(adj)
    NR, reachR = fast_counts(R)
    nR = len(R)
    A = {v: [idx[("a", v, i)] for i in range(h)] for v in range(Ncore)}
    B = {v: [idx[("b", v, i)] for i in range(h)] for v in range(Ncore)}
    special = set()
    for u in range(n0):
        for v in range(n0):
            for x in [u] + A[u]:
                for y in [v] + B[v]:
                    special.add((x, y))
                    if NR[x][y] != NG[u][v]:
                        tally["errors"] += 1
                        print("COUNT NOT PRESERVED", adj, rho, u, v, x, y)
    for x in range(nR):
        for y in range(nR):
            if x != y and (x, y) not in special and NR[x][y] > 1:
                tally["errors"] += 1
                print("OTHER PAIR WITH MULTIPLICITY > 1", adj, rho, x, y, NR[x][y])
    for k in range(1, 5):
        vG = all(NG[u][v] <= k for u in range(n0) for v in range(n0))
        vR = all(NR[u][v] <= k for u in range(nR) for v in range(nR))
        if vG != vR:
            tally["errors"] += 1
            print("VALIDITY NOT PRESERVED", adj, rho, k)
    for s in range(n0):
        for t in range(n0):
            liveG = {x for x in range(n0) if reachG[s][x] and reachG[x][t]}
            liveR = {x for x in range(nR) if reachR[s][x] and reachR[x][t]}
            if liveG != liveR or NG[s][t] != NR[s][t]:
                tally["errors"] += 1
                print("INTERVAL NOT PRESERVED", adj, rho, s, t)
    E = und(R)
    deg = [0] * nR
    for (u, v) in E:
        deg[u] += 1
        deg[v] += 1
    if min(deg) != rho:
        tally["errors"] += 1
        print("MIN DEGREE", adj, rho, min(deg))
    # diameter
    nbr = [[] for _ in range(nR)]
    for (u, v) in E:
        nbr[u].append(v)
        nbr[v].append(u)
    for r in range(nR):
        dist = {r: 0}
        dq = deque([r])
        while dq:
            x = dq.popleft()
            for y in nbr[x]:
                if y not in dist:
                    dist[y] = dist[x] + 1
                    dq.append(y)
        if len(dist) < nR or max(dist.values()) > 4:
            tally["errors"] += 1
            print("DIAMETER", adj, rho)
            break
    tally["maxdiam_checked"] += 1
    if full_connectivity:
        for S in itertools.combinations(range(nR), rho - 1):
            comp = components(nR, E, frozenset(S))
            if len({comp[v] for v in range(nR) if v not in S}) != 1:
                tally["errors"] += 1
                print("VERTEX CONNECTIVITY < rho", adj, rho, S)
                break
        tally["kappa_sets"] += 1
    a = idx[("a", 0, 0)]
    S = set(nbr[a])
    comp = components(nR, E, frozenset(S))
    if len({comp[v] for v in range(nR) if v not in S}) == 1:
        tally["errors"] += 1
        print("neighbourhood of a private vertex does not separate", adj, rho)
    lam = min(maxflow_und(nR, E, 0, v) for v in range(1, nR))
    if lam != rho:
        tally["errors"] += 1
        print("EDGE CONNECTIVITY", adj, rho, lam)
    tally["robust"] += 1


def path_list(adj, s, t):
    n = len(adj)
    out = []

    def dfs(v, path):
        if v == t:
            out.append(list(path))
        for w in range(n):
            if adj[v][w]:
                path.append(w)
                dfs(w, path)
                path.pop()
    dfs(s, [s])
    return out


def check_flow_and_updates(rng, tally):
    for _ in range(400):
        n = rng.randint(3, 9)
        adj = random_dag(n, rng.choice([0.2, 0.35, 0.5]), rng)
        C = walk_counts(adj)
        s, t = rng.randrange(n), rng.randrange(n)
        paths = path_list(adj, s, t)
        assert len(paths) == C[s][t]
        for v in range(n):
            through = sum(1 for P in paths if v in P)
            if through != C[s][v] * C[v][t]:
                tally["errors"] += 1
            if C[s][t] > 0 and (through == C[s][t]) != (C[s][v] * C[v][t] == C[s][t]):
                tally["errors"] += 1
        for x in range(n):
            for y in range(n):
                if adj[x][y]:
                    through = sum(1 for P in paths
                                  if any(P[i] == x and P[i + 1] == y for i in range(len(P) - 1)))
                    if through != C[s][x] * C[y][t]:
                        tally["errors"] += 1
        tally["flow"] += 1
        # insertion
        cand = [(x, y) for x in range(n) for y in range(n)
                if x != y and not adj[x][y] and C[y][x] == 0]
        if cand:
            x, y = rng.choice(cand)
            adj2 = [row[:] for row in adj]
            adj2[x][y] = 1
            C2 = walk_counts(adj2)
            if not is_acyclic(adj2):
                tally["errors"] += 1
            for u in range(n):
                for v in range(n):
                    if C2[u][v] != C[u][v] + C[u][x] * C[y][v]:
                        tally["errors"] += 1
            tally["insert"] += 1
        # deletion
        arcs = [(x, y) for x in range(n) for y in range(n) if adj[x][y]]
        if arcs:
            x, y = rng.choice(arcs)
            adj3 = [row[:] for row in adj]
            adj3[x][y] = 0
            C3 = walk_counts(adj3)
            for u in range(n):
                for v in range(n):
                    if C3[u][v] != C[u][v] - C[u][x] * C[y][v]:
                        tally["errors"] += 1
            tally["delete"] += 1
    # an insertion with C[y][x] > 0 creates a cycle
    for _ in range(200):
        n = rng.randint(3, 8)
        adj = random_dag(n, 0.4, rng)
        C = walk_counts(adj)
        cand = [(x, y) for x in range(n) for y in range(n) if x != y and C[y][x] > 0]
        if cand:
            x, y = rng.choice(cand)
            adj[x][y] = 1
            if is_acyclic(adj):
                tally["errors"] += 1


def check_second_path(rng, tally):
    for _ in range(300):
        n = rng.randint(2, 8)
        adj = random_dag(n, 0.35, rng)
        s, t = rng.sample(range(n), 2)
        m = n + 3
        R = [[0] * m for _ in range(m)]
        for u in range(n):
            for v in range(n):
                R[u][v] = adj[u][v]
        sp, d, tp = n, n + 1, n + 2
        R[sp][d] = R[d][tp] = R[sp][s] = R[t][tp] = 1
        if walk_counts(R)[sp][tp] != 1 + walk_counts(adj)[s][t]:
            tally["errors"] += 1
        tally["second"] += 1


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 2026
    rng = random.Random(seed)
    tally = {"errors": 0, "robust": 0, "kappa_sets": 0, "maxdiam_checked": 0,
             "flow": 0, "insert": 0, "delete": 0, "second": 0}
    for n in range(1, 4):
        for adj in all_digraphs(n, loops=True):
            check_robust(adj, 2, tally)
    for adj in all_digraphs(3):
        check_robust(adj, 3, tally)
    for _ in range(60):
        n = rng.randint(4, 6)
        adj = (random_dag(n, 0.4, rng) if rng.random() < 0.6
               else random_digraph(n, 0.25, rng))
        rho = rng.choice([2, 3, 3, 4])
        check_robust(adj, rho, tally, full_connectivity=(rho <= 3))
    print(f"robustification: {tally['robust']} (G, rho) pairs; vertex connectivity by "
          f"exhaustive deletion on {tally['kappa_sets']} of them")
    check_flow_and_updates(rng, tally)
    print(f"path flow: {tally['flow']} DAGs; insertions: {tally['insert']}; "
          f"deletions: {tally['delete']}")
    check_second_path(rng, tally)
    print(f"second-path construction: {tally['second']} DAGs")
    print(f"errors: {tally['errors']}")


if __name__ == "__main__":
    main()
