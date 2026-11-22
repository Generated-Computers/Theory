"""Checks for Section 4: bypass-pruned traversal (Theorem 4.6).

For every traversal (cycle search and pair recounts) we check
  - the active frames never exceed gamma (cycle rank of the root's weak
    component), on ALL inputs, cyclic ones included (Corollary 4.5);
  - at every push, the bypass cycles C_1..C_h of the active frames are
    linearly independent over GF(2) (Lemma 4.4), using explicit cycles;
  - on valid inputs the frames never exceed k*tau_plus - 1;
and compare the decision and all pair counts with brute force.
Connectivity tests (Reingold's algorithm in the paper) are done by BFS.
Usage: python3 bypass_pruning.py [seed]
"""
import sys
import random
from common import (all_digraphs, random_digraph, random_dag, succ, und_edges,
                    components, connected_avoiding, bfs_path, gf2_independent,
                    valid, INF)


class Reject(Exception):
    pass


def gamma_of_component(n, E, a):
    comp = components(n, E)
    vs = sum(1 for v in range(n) if comp[v] == comp[a])
    es = sum(1 for (u, v) in E if comp[u] == comp[a])
    return es - vs + 1


def edge_index(E, u, v):
    for i, (x, y) in enumerate(E):
        if (x, y) == (u, v):
            return i
    raise KeyError


def traverse(adj, E, a, t, k, tally):
    n = len(adj)
    g = gamma_of_component(n, E, a)

    def adm(v, S):
        if v == t:
            return []
        X = set(S) | {v}
        return [w for w in succ(adj, v)
                if w not in X and connected_avoiding(n, E, w, t, X)]

    frames = []          # [vertex, next index into its admissible list, depth, cycle mask]
    v, D = a, 0
    total = 1
    cnt = 1 if a == t else 0

    def enter(w):
        nonlocal total, cnt
        total += 1
        if total == n * k + 1:
            raise Reject("node cap")
        if w == t:
            cnt += 1
            if cnt == k + 1:
                raise Reject("target cap")

    while True:
        S = [f[0] for f in frames]
        A = adm(v, S)
        if A:
            if D + 1 == n:
                raise Reject("depth cap")
            if len(A) >= 2:
                # explicit bypass cycle through v (Lemma 4.4)
                a1, b1 = A[0], A[1]
                pi = bfs_path(n, E, a1, b1, set(S) | {v})
                assert pi is not None
                mask = (1 << edge_index(E, v, a1)) | (1 << edge_index(E, v, b1))
                for i in pi:
                    mask ^= 1 << i
                frames.append([v, 1, D, mask])
                tally["maxh"] = max(tally["maxh"], len(frames))
                if len(frames) > g:
                    tally["errors"] += 1
                    print("STACK EXCEEDS GAMMA", adj, a, t)
                if not gf2_independent([f[3] for f in frames]):
                    tally["errors"] += 1
                    print("CYCLES DEPENDENT", adj, a, t)
                tally["pushes"] += 1
                tally["maxh_rel"] = max(tally["maxh_rel"], len(frames) / max(g, 1))
            v, D = A[0], D + 1
            enter(v)
        else:
            while frames:
                x, idx, Dx, _ = frames[-1]
                Ax = adm(x, [f[0] for f in frames[:-1]])
                if idx < len(Ax):
                    frames[-1][1] += 1
                    v, D = Ax[idx], Dx + 1
                    enter(v)
                    break
                frames.pop()
            else:
                return cnt, tally


def decide(adj, s, t, k, tally):
    """Total decider of Theorem 4.6; returns (accept, counts or None)."""
    n = len(adj)
    if k == 0:
        return False, None
    for u in range(n):
        if adj[u][u]:
            return False, None
        for v in range(u + 1, n):
            if adj[u][v] and adj[v][u]:
                return False, None
    E = und_edges(adj)
    # canonical spanning forest by scanning the edges in order
    parent = list(range(n))

    def find(x):
        while parent[x] != x:
            x = parent[x]
        return x
    chords = []
    for (x, y) in E:
        rx, ry = find(x), find(y)
        if rx == ry:
            chords.append((x, y))
        else:
            parent[rx] = ry
    try:
        for (x, y) in chords:           # cycle search from y to x
            c, _ = traverse(adj, E, y, x, k, tally)
            if c >= 1:
                raise Reject("cycle found")
        counts = [[traverse(adj, E, a, b, k, tally)[0] for b in range(n)]
                  for a in range(n)]
    except Reject as e:
        tally["rej"][str(e)] = tally["rej"].get(str(e), 0) + 1
        return False, None
    return counts[s][t] >= 1, counts


def run_case(adj, k, tally):
    n = len(adj)
    ok, N = valid(adj, k)
    before = tally["maxh"]
    tally["maxh"] = 0
    acc, counts = decide(adj, 0, n - 1, k, tally)
    want = ok and N[0][n - 1] >= 1
    tally["cases"] += 1
    if acc != want:
        tally["errors"] += 1
        print("MISMATCH", adj, k, acc, want)
    if ok:
        tally["valid"] += 1
        tplus = sum(1 for v in range(n) if sum(adj[v]) == 0)
        if counts is None or any(counts[a][b] != N[a][b] for a in range(n) for b in range(n)):
            tally["errors"] += 1
            print("COUNT MISMATCH", adj, k)
        if tally["maxh"] > k * tplus - 1:
            tally["errors"] += 1
            print("LEAF BOUND VIOLATED", adj, k)
    tally["maxh"] = max(before, tally["maxh"])
    # stack bound and independence also on cyclic inputs (no loops):
    if not ok and all(adj[v][v] == 0 for v in range(n)):
        E = und_edges(adj)
        for a in range(n):
            for b in range(n):
                try:
                    traverse(adj, E, a, b, k, tally)
                except Reject:
                    pass
        tally["cyclic_runs"] += 1


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 2026
    rng = random.Random(seed)
    tally = {"cases": 0, "valid": 0, "errors": 0, "maxh": 0, "pushes": 0,
             "maxh_rel": 0.0, "rej": {}, "cyclic_runs": 0}
    for n in range(1, 5):
        for adj in all_digraphs(n):
            for k in ([1, 2, 3] if n <= 3 else [1, 2]):
                run_case(adj, k, tally)
    for _ in range(600):
        n = rng.randint(5, 9)
        if rng.random() < 0.6:
            adj = random_dag(n, rng.choice([0.2, 0.3, 0.45]), rng)
        else:
            adj = random_digraph(n, rng.choice([0.15, 0.25]), rng)
        N = valid(adj, 1)[1]
        finite = [x for row in N for x in row if x != INF]
        kmax = max(finite) if finite else 1
        for k in sorted({1, max(1, kmax - 1), kmax}):
            run_case(adj, k, tally)
    print(f"decider cases: {tally['cases']}, valid inputs: {tally['valid']}")
    print(f"rejections: {tally['rej']}")
    print(f"invalid loopless inputs traversed for all pairs: {tally['cyclic_runs']}")
    print(f"pushes checked for GF(2) independence: {tally['pushes']}")
    print(f"largest number of active frames: {tally['maxh']}; "
          f"largest frames/gamma: {tally['maxh_rel']:.3f}")
    print(f"errors: {tally['errors']}")


if __name__ == "__main__":
    main()
