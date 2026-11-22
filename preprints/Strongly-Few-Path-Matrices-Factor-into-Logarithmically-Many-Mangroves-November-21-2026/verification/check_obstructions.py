"""Checks of Section 10 (minimal violations and the finite obstruction basis).

1. Theorem 10.4: every trimmed two-terminal multigraph H on n <= 5 vertices (multiplicities
   <= 3) and every simple one on n <= 7 vertices that is edge-minimal subject to N(s,t) > k
   (for some k >= 1) is reduced by contracting its mandatory terminal chains; the result
   satisfies d+(s) >= 2, d-(t) >= 2, k+1 <= r <= 2k, c <= k, and its kernel has at most 2k
   vertices and 3k-1 edges.  Without the contraction the kernel has at most 2k+2 vertices and
   3k+1 edges (Remark 10.5).
2. Theorem 10.6 (extraction): for every simple DAG on n <= 6 vertices and every k with
   max N > k, the procedure of the proof (trim, delete edges greedily while N > k, contract,
   suppress) yields a core of F_k.
3. For k = 1, 2, 3 the reduced cores (the family F_k of Theorem 10.6) are enumerated up to
   isomorphism (Remark 10.7), and the members containing a subdivision of another member are removed.
Usage: python3 check_obstructions.py
"""
import itertools
import sys

from sfcommon import path_matrix, topo_order


def fail(msg, A):
    print("FAILURE:", msg)
    print("A =", A)
    sys.exit(1)


def npaths(A, s, t):
    return path_matrix(A)[s][t]


def edge_list(A):
    n = len(A)
    return [(u, v) for u in range(n) for v in range(n) for _ in range(A[u][v])]


def is_edge_minimal(A, s, t, k):
    n = len(A)
    for u in range(n):
        for v in range(n):
            if A[u][v]:
                A[u][v] -= 1
                r2 = npaths(A, s, t)
                A[u][v] += 1
                if r2 > k:
                    return False
    return True


def trim(A, s, t):
    C = path_matrix(A)
    n = len(A)
    keep = [v for v in range(n) if C[s][v] and C[v][t]]
    idx = {v: i for i, v in enumerate(keep)}
    B = [[A[u][v] for v in keep] for u in keep]
    return B, idx[s], idx[t]


def contract_chains(A, s, t):
    """Move s forward while it has outdegree 1, and t backward while it has indegree 1."""
    n = len(A)
    while s != t and sum(A[s]) == 1:
        s = next(v for v in range(n) if A[s][v])
    while s != t and sum(A[u][t] for u in range(n)) == 1:
        t = next(u for u in range(n) if A[u][t])
    return trim(A, s, t)


def kernel_size(A, s, t):
    n = len(A)
    indeg = [sum(A[u][v] for u in range(n)) for v in range(n)]
    outdeg = [sum(A[v]) for v in range(n)]
    kept = [v for v in range(n) if v in (s, t) or not (indeg[v] == 1 and outdeg[v] == 1)]
    c = sum(map(sum, A)) - n + 1
    return len(kept), len(kept) - 1 + c


def check_minimal(A, s, t, k, stats):
    r = npaths(A, s, t)
    V0, E0 = kernel_size(A, s, t)
    if V0 > 2 * k + 2 or E0 > 3 * k + 1:
        fail("Remark 10.5", A)
    B, s2, t2 = contract_chains(A, s, t)
    n2 = len(B)
    if npaths(B, s2, t2) != r:
        fail("contraction changed r", A)
    if not is_edge_minimal(B, s2, t2, k):
        fail("contraction destroyed edge-minimality", A)
    if sum(B[s2]) < 2 or sum(B[u][t2] for u in range(n2)) < 2:
        fail("degrees after contraction", A)
    c = sum(map(sum, B)) - n2 + 1
    V, E = kernel_size(B, s2, t2)
    if not (k + 1 <= r <= 2 * k) or c > k or V > 2 * k or E > 3 * k - 1:
        fail("Theorem 10.4", A)
    stats[k] = stats.get(k, 0) + 1


def part1():
    stats = {}
    families = [(n, 3) for n in range(2, 6)] + [(n, 1) for n in range(6, 8)]
    for (n, mmax) in families:
        pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
        for mult in itertools.product(range(mmax + 1), repeat=len(pairs)):
            A = [[0] * n for _ in range(n)]
            for (i, j), x in zip(pairs, mult):
                A[i][j] = x
            C = path_matrix(A)
            if any(C[0][v] == 0 or C[v][n - 1] == 0 for v in range(n)):
                continue
            r = C[0][n - 1]
            for k in range(1, r):
                if is_edge_minimal(A, 0, n - 1, k):
                    check_minimal(A, 0, n - 1, k, stats)
    print("Theorem 10.4: edge-minimal violators checked, per k:", dict(sorted(stats.items())))


def part2():
    cnt = 0
    for n in range(2, 7):
        pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
        for mask in range(1 << len(pairs)):
            A = [[0] * n for _ in range(n)]
            for b, (i, j) in enumerate(pairs):
                if mask >> b & 1:
                    A[i][j] = 1
            C = path_matrix(A)
            K = max(map(max, C))
            for k in range(1, K):
                s, t = next((u, v) for u in range(n) for v in range(n) if C[u][v] > k)
                B, s2, t2 = trim(A, s, t)
                changed = True
                while changed:
                    changed = False
                    for (u, v) in edge_list(B):
                        B[u][v] -= 1
                        if npaths(B, s2, t2) > k:
                            changed = True
                            break
                        B[u][v] += 1
                B, s2, t2 = trim(B, s2, t2)
                B, s3, t3 = contract_chains(B, s2, t2)
                r = npaths(B, s3, t3)
                c = sum(map(sum, B)) - len(B) + 1
                V, E = kernel_size(B, s3, t3)
                if not (k + 1 <= r <= 2 * k and c <= k and V <= 2 * k and E <= 3 * k - 1):
                    fail("extraction", A)
                cnt += 1
    print(f"Theorem 10.6 extraction: {cnt} (graph, k) cases on n <= 6 vertices")


def canon(A):
    """Canonical form of a two-terminal multigraph with s = 0, t = n-1 (internal vertices permuted)."""
    n = len(A)
    best = None
    for perm in itertools.permutations(range(1, n - 1)):
        lab = [0] + list(perm) + [n - 1]
        es = tuple(sorted((lab[u], lab[v]) for (u, v) in edge_list(A)))
        if best is None or es < best:
            best = es
    return (n, best)


def all_paths_vertices(A, a, b):
    n = len(A)
    out = []

    def rec(u, acc):
        if u == b:
            out.append(list(acc))
            return
        for w in range(n):
            if A[u][w]:
                acc.append(w)
                rec(w, acc)
                acc.pop()
    rec(a, [a])
    return out


def contains_subdivision(G, F):
    """Does the multigraph G contain a subdivision of the multigraph F (as a subgraph)?"""
    nG, nF = len(G), len(F)
    Fedges = edge_list(F)
    pathcache = {}

    def paths(a, b):
        if (a, b) not in pathcache:
            pathcache[(a, b)] = all_paths_vertices(G, a, b)
        return pathcache[(a, b)]

    for phi in itertools.permutations(range(nG), nF):
        image = set(phi)
        used_v = set()
        used_e = {}

        def route(i):
            if i == len(Fedges):
                return True
            x, y = Fedges[i]
            for P in paths(phi[x], phi[y]):
                inner = P[1:-1]
                if any(v in image or v in used_v for v in inner):
                    continue
                es = list(zip(P, P[1:]))
                if any(used_e.get(e, 0) + es.count(e) > G[e[0]][e[1]] for e in set(es)):
                    continue
                for v in inner:
                    used_v.add(v)
                for e in es:
                    used_e[e] = used_e.get(e, 0) + 1
                if route(i + 1):
                    return True
                for v in inner:
                    used_v.discard(v)
                for e in es:
                    used_e[e] -= 1
            return False
        if route(0):
            return True
    return False


def part3(kmax=3):
    for k in range(1, kmax + 1):
        cores = {}
        for nv in range(2, 2 * k + 1):
            pairs = [(i, j) for i in range(nv) for j in range(i + 1, nv)]
            emax = 3 * k - 1

            def gen(idx, left, mult):
                if idx == len(pairs):
                    yield list(mult)
                    return
                for x in range(left + 1):
                    mult.append(x)
                    yield from gen(idx + 1, left - x, mult)
                    mult.pop()
            for mult in gen(0, emax, []):
                A = [[0] * nv for _ in range(nv)]
                for (i, j), x in zip(pairs, mult):
                    A[i][j] = x
                s, t = 0, nv - 1
                if sum(A[s]) < 2 or sum(A[u][t] for u in range(nv)) < 2:
                    continue
                indeg = [sum(A[u][v] for u in range(nv)) for v in range(nv)]
                outdeg = [sum(A[v]) for v in range(nv)]
                if any(indeg[v] == 0 or outdeg[v] == 0 or (indeg[v] == 1 and outdeg[v] == 1)
                       for v in range(1, nv - 1)):
                    continue
                C = path_matrix(A)
                if any(C[s][v] == 0 or C[v][t] == 0 for v in range(nv)):
                    continue
                if C[s][t] <= k or not is_edge_minimal(A, s, t, k):
                    continue
                key = canon(A)
                if key not in cores:
                    cores[key] = A
        members = list(cores.values())
        minimal = []
        for i, Fi in enumerate(members):
            redundant = any(j != i and contains_subdivision(Fi, Fj) for j, Fj in enumerate(members))
            if not redundant:
                minimal.append(Fi)
        rs = sorted(npaths(F, 0, len(F) - 1) for F in members)
        print(f"k = {k}: {len(members)} reduced cores up to isomorphism "
              f"(path counts {rs}); {len(minimal)} remain after removing members that contain "
              f"a subdivision of another member")
        for F in minimal:
            print("    minimal core: n =", len(F), "edges", edge_list(F), "r =", npaths(F, 0, len(F) - 1))


def main():
    part1()
    part2()
    part3()
    print("all checks passed")


if __name__ == "__main__":
    main()
