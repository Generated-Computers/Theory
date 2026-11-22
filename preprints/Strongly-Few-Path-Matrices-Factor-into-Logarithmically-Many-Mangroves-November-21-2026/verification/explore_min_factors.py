"""Least number of mangrove factors of the path-count matrix, for small graphs (Remark 6.6).

Every factor M of a factorization C = M_1 ... M_f satisfies I <= M <= C entrywise, so it is
the path-count matrix of a mangrove whose edges join pairs (u, v) with C[u][v] >= 1.  The
script lists all such mangrove factors and searches breadth-first over the residuals
R = (M_1 ... M_j)^(-1) C, which must be nonnegative.  Every factorization found is multiplied
back and compared with C.
Usage: python3 explore_min_factors.py
"""
import sys
import time

from sfcommon import path_matrix, matmul

def mangroves_below(C):
    n = len(C)
    pairs = [(u, v) for u in range(n) for v in range(n) if u != v and C[u][v]]
    out = {}
    def rec(i, B):
        if i == len(pairs):
            M = path_matrix(B)
            out[tuple(map(tuple, M))] = [row[:] for row in B]
            return
        rec(i + 1, B)
        u, v = pairs[i]
        B[u][v] = 1
        if max(map(max, path_matrix(B))) <= 1:
            rec(i + 1, B)
        B[u][v] = 0
    rec(0, [[0] * n for _ in range(n)])
    return out

def lsolve(M, R):
    n = len(M)
    X = [[0] * n for _ in range(n)]
    for i in range(n - 1, -1, -1):
        Mi = M[i]
        for j in range(n):
            X[i][j] = R[i][j] - sum(Mi[k] * X[k][j] for k in range(i + 1, n))
    return X

def search(C, fmax):
    n = len(C)
    S = mangroves_below(C)
    Ms = list(S)
    print(f"  {len(Ms)} mangrove factors below C", flush=True)
    # BFS over residuals: level f holds residuals R with C = (product of f factors) R
    frontier = {tuple(map(tuple, C)): []}
    for f in range(1, fmax + 1):
        for R, hist in frontier.items():
            if R in S:
                return f, hist + [S[R]]
        if f == fmax:
            break
        new = {}
        for R, hist in frontier.items():
            for M in Ms:
                if any(M[i][j] > R[i][j] for i in range(n) for j in range(n)):
                    continue
                X = lsolve(M, R)
                if min(map(min, X)) < 0:
                    continue
                key = tuple(map(tuple, X))
                if key not in new:
                    new[key] = hist + [S[M]]
        frontier = new
        print(f"  residuals after {f} factors: {len(frontier)}", flush=True)
    return None, None

def T(n):
    A = [[int(i < j) for j in range(n)] for i in range(n)]
    return A

def D(r):
    n = 3 * r + 1
    A = [[0] * n for _ in range(n)]
    # order: z0, a1, b1, z1, a2, b2, z2, ...
    for i in range(1, r + 1):
        z0, a, b, z1 = 3 * (i - 1), 3 * i - 2, 3 * i - 1, 3 * i
        A[z0][a] = A[z0][b] = A[a][z1] = A[b][z1] = 1
    return A

cases = [("T4", T(4), 3), ("T5", T(5), 4), ("D2", D(2), 3)]
for name, A, fmax in cases:
    t = time.time()
    C = path_matrix(A)
    print(name, "k =", max(map(max, C)), flush=True)
    f, hist = search(C, fmax)
    print(f"{name}: minimum number of mangrove factors = {f}  ({time.time()-t:.1f}s)", flush=True)
    if hist:
        P = [[int(i == j) for j in range(len(C))] for i in range(len(C))]
        for B in hist:
            P = matmul(P, path_matrix(B))
        assert P == C
        for B in hist:
            print("   factor edges:", [(u, v) for u in range(len(B)) for v in range(len(B)) if B[u][v]])
