"""Exact values of ex_sf(n,k) for n <= 7 by exhaustive search, compared with Section 11.

ex_sf(n,k) is the maximum number of edges of a simple n-vertex k-strongly-unambiguous
digraph.  Such a digraph is acyclic, hence isomorphic to one whose edges go from smaller to
larger labels; the search adds vertices 0, 1, ..., n-1 in turn, choosing the in-neighbour set
of each new vertex among the earlier ones (all 2^(n(n-1)/2) graphs), and updates the
path-count column of the new vertex.  It checks
  * Theorem 11.1: ex_sf(n,k) <= min(n(n-1)/2, n^2/4 + 3(k-1)n/4);
  * Proposition 11.2: ex_sf(n,k) >= floor((n-k+1)^2/4) + (k-1)(n-k+1) for 1 <= k <= n-1,
    and the construction itself (three layers) is k-strongly unambiguous with that many edges.
With a second argument cap, graphs whose largest count exceeds cap are pruned (used for n = 8).
Usage: python3 check_density.py [max_n=7] [cap]
"""
import sys

from sfcommon import path_matrix, maxentry


def exhaustive(n, cap=None):
    """best[k'] = max edges over graphs whose largest path count is exactly k' (k' <= cap)."""
    best = {}
    cols = []  # cols[v] = list of C[u][v] for u < v (path counts into v from earlier vertices)

    def rec(j, edges, mx):
        if j == n:
            if best.get(mx, -1) < edges:
                best[mx] = edges
            return
        for S in range(1 << j):
            col = [0] * j
            e = 0
            s = S
            v = 0
            while s:
                if s & 1:
                    e += 1
                    cv = cols[v]
                    for u in range(v):
                        col[u] += cv[u]
                    col[v] += 1
                s >>= 1
                v += 1
            m2 = max(col) if col else 0
            if cap is not None and m2 > cap:
                continue
            cols.append(col)
            rec(j + 1, edges + e, max(mx, m2))
            cols.pop()

    rec(0, 0, 1)
    return best


def three_layer(n, k):
    b = k - 1
    rest = n - b
    a = rest // 2
    c = rest - a
    A = [[0] * n for _ in range(n)]
    Aset = range(0, a)
    Bset = range(a, a + b)
    Cset = range(a + b, n)
    for x in Aset:
        for y in Bset:
            A[x][y] = 1
        for z in Cset:
            A[x][z] = 1
    for y in Bset:
        for z in Cset:
            A[y][z] = 1
    return A


def main():
    max_n = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    cap = int(sys.argv[2]) if len(sys.argv) > 2 else None
    for n in range(2 if cap is None else max_n, max_n + 1):
        best = exhaustive(n, cap)
        K = max(best)
        ex = {}
        run = -1
        for k in range(1, K + 1):
            run = max(run, best.get(k, -1))
            ex[k] = run
        row = []
        for k in range(1, K + 1):
            upper = min(n * (n - 1) // 2, (n * n + 3 * (k - 1) * n) / 4)
            if ex[k] > upper + 1e-9:
                print("FAILURE: Theorem 11.1", n, k)
                sys.exit(1)
            if k <= n - 1:
                lower = (n - k + 1) ** 2 // 4 + (k - 1) * (n - k + 1)
                A = three_layer(n, k)
                C = path_matrix(A)
                if maxentry(C) > k or sum(map(sum, A)) != lower:
                    print("FAILURE: three-layer construction", n, k)
                    sys.exit(1)
                if ex[k] < lower:
                    print("FAILURE: Proposition 11.2", n, k)
                    sys.exit(1)
                row.append((k, ex[k], lower, upper))
        print(f"n = {n}: (k, ex_sf, three-layer lower bound, upper bound of Thm 11.1) =")
        print("   ", [(k, e, l, round(u, 2)) for (k, e, l, u) in row])
        if cap is None:
            print(f"    largest k with ex_sf < n(n-1)/2: {max([k for k in ex if ex[k] < n*(n-1)//2] or [0])}; "
                  f"ex_sf(n, 2^(n-2)) = {ex[2 ** (n - 2)] if 2 ** (n - 2) in ex else None}")
    print("all checks passed")


if __name__ == "__main__":
    main()
