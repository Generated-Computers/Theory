"""Checks of Section 3 on all small digraphs, cyclic ones included.

* Theorem 3.1: for every digraph on n <= 3 vertices without loops (64 graphs) and on n <= 2
  vertices with loops allowed, and for k in {1, 2}, the number of matrices
  C in {0,...,k}^{n x n} with C = I + AC is 1 if the graph is k-strongly unambiguous and 0
  otherwise (exhaustive search over all candidate matrices).
* Theorem 3.3 / Corollary 3.4 (budgeted stabilization): for every digraph on n <= 4 vertices
  (loops allowed for n <= 3), every root s, and budget vectors kappa (constant 1, 2, 3 and
  60 random vectors per graph), N(s,v) <= kappa(v) for all v iff x^(B) <= kappa, where
  B = sum(kappa) and x^(d)_v counts walks s -> v of length <= d; in that case
  x^(B) = x^(B+1) = ... = N(s, .).
Usage: python3 check_fixedpoint.py [seed=2026]
"""
import itertools
import random
import sys

from sfcommon import reach_sets


def all_digraphs(n, loops):
    cells = [(i, j) for i in range(n) for j in range(n) if loops or i != j]
    for mask in range(1 << len(cells)):
        A = [[0] * n for _ in range(n)]
        for b, (i, j) in enumerate(cells):
            if mask >> b & 1:
                A[i][j] = 1
        yield A


def walk_counts(A):
    """N[u][v] in N u {inf}: exact walk counts, with inf when a cycle lies on a u-v walk."""
    n = len(A)
    R = reach_sets(A)
    cyclic = [any(A[v][w] and v in R[w] for w in range(n)) for v in range(n)]
    N = [[0] * n for _ in range(n)]
    for u in range(n):
        x = bounded(A, u, n)  # walks of length <= n; enough when the interval is acyclic
        for v in range(n):
            if any(cyclic[c] and c in R[u] and v in R[c] for c in range(n)):
                N[u][v] = float("inf")
            else:
                N[u][v] = x[v]
    return N


def bounded(A, s, d):
    """x^(d): number of walks from s of length <= d ending at each vertex."""
    n = len(A)
    x = [int(v == s) for v in range(n)]
    for _ in range(d):
        nx = [int(v == s) for v in range(n)]
        for u in range(n):
            if x[u]:
                for v in range(n):
                    if A[u][v]:
                        nx[v] += x[u] * A[u][v]
        x = nx
    return x


def strongly_unambiguous(N, k):
    return all(N[u][v] <= k for u in range(len(N)) for v in range(len(N)))


def check_fixed_point_uniqueness():
    total = 0
    for (n, loops) in [(1, True), (2, True), (3, False)]:
        for A in all_digraphs(n, loops):
            N = walk_counts(A)
            for k in (1, 2):
                sols = 0
                for vals in itertools.product(range(k + 1), repeat=n * n):
                    C = [list(vals[i * n:(i + 1) * n]) for i in range(n)]
                    ok = True
                    for u in range(n):
                        for v in range(n):
                            if C[u][v] != int(u == v) + sum(A[u][w] * C[w][v] for w in range(n)):
                                ok = False
                                break
                        if not ok:
                            break
                    if ok:
                        sols += 1
                        if C != N:
                            print("FAILURE: bounded fixed point differs from walk counts", A)
                            sys.exit(1)
                expected = 1 if strongly_unambiguous(N, k) else 0
                if sols != expected:
                    print("FAILURE: Theorem 3.1", A, k, sols)
                    sys.exit(1)
                total += 1
    print(f"Theorem 3.1: {total} (graph, k) pairs checked by exhaustive search over C")


def check_budget(rng):
    cases = 0
    accepted = 0
    for (n, loops) in [(1, True), (2, True), (3, True), (4, False)]:
        for A in all_digraphs(n, loops):
            N = walk_counts(A)
            for k in (1, 2, 3):
                # all-pairs form (Corollary 3.4): G is k-SU iff every root passes with kappa = k
                allpass = all(max(bounded(A, s, n * k)) <= k for s in range(n))
                if allpass != strongly_unambiguous(N, k):
                    print("FAILURE: Corollary 3.4", A, k)
                    sys.exit(1)
            for s in range(n):
                budgets = [[c] * n for c in (1, 2, 3)]
                budgets += [[rng.randint(0, 4) for _ in range(n)] for _ in range(60)]
                for kappa in budgets:
                    B = sum(kappa)
                    xB = bounded(A, s, B)
                    within = all(xB[v] <= kappa[v] for v in range(n))
                    truth = all(N[s][v] <= kappa[v] for v in range(n))
                    if within != truth:
                        print("FAILURE: Theorem 3.3", A, s, kappa)
                        sys.exit(1)
                    if within:
                        accepted += 1
                        for extra in (1, 2, 7):
                            if bounded(A, s, B + extra) != xB:
                                print("FAILURE: no stabilization", A, s, kappa)
                                sys.exit(1)
                        if [N[s][v] for v in range(n)] != xB:
                            print("FAILURE: stable vector is not N(s, .)", A, s, kappa)
                            sys.exit(1)
                    cases += 1
    print(f"Theorem 3.3 / Corollary 3.4: {cases} (graph, root, budget) cases, {accepted} within budget")


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 2026
    rng = random.Random(seed)
    check_fixed_point_uniqueness()
    check_budget(rng)
    print("all checks passed")


if __name__ == "__main__":
    main()
