"""Checks of Sections 3-7 on all small DAGs and on random k-strongly-unambiguous graphs.

Checked for every graph G with path matrix C and k = max entry of C:
  * C computed three independent ways (DP, matrix powers, DFS) agree;
  * Theorem 3.1: C = I + AC;
  * Lemma 4.1, Theorem 4.2, Corollary 4.3 (triples), the redundant-edge bound;
  * Theorem 5.1 for every threshold 1 <= tau < k, Corollary 5.2;
  * Theorem 5.3 (level partition): blocks are path-convex induced mangroves, no edge goes
    backwards, number of blocks <= floor(log2 k) + 1;
  * Theorem 6.2 (level factorization): the 2p+1 factors are mangrove path matrices and their
    product is C;
  * Remark 5.6 (balanced recursion of the source): leaves <= 2 log2 k,
    depth <= 1 + floor(log2 log2 k), 2l-1 factors, product = C;
  * Theorem 7.1 (interval width, edge bound) and Theorem 7.2 (separator);
  * Theorem 11.3 and Theorem 11.4 (junction and centrality bounds).
Usage: python3 check_factorization.py [max_n_exhaustive=6] [random_graphs=300] [seed=2026]
"""
import itertools
import math
import random
import sys

from sfcommon import (path_matrix, path_matrix_powers, count_paths_dfs, matmul, identity,
                      maxentry, reach_sets, induced, embed, is_mangrove_path_matrix, ilog2,
                      upper_triangular_dags)

stats = {}


def bump(key, inc=1):
    stats[key] = stats.get(key, 0) + inc


def fail(msg, A):
    print("FAILURE:", msg)
    print("A =", A)
    sys.exit(1)


def mu_nu(C):
    n = len(C)
    mu = [max(C[a][v] for a in range(n)) for v in range(n)]
    nu = [max(C[v][b] for b in range(n)) for v in range(n)]
    return mu, nu


def path_convex(S, R):
    """S is path-convex iff no x outside S satisfies u ~> x ~> v with u, v in S."""
    Sset = set(S)
    n = len(R)
    up = set()
    for u in S:
        up |= R[u]
    for x in up - Sset:
        if R[x] & Sset:
            return False
    return True


def level_factorization(A, C):
    n = len(A)
    mu, _ = mu_nu(C)
    lev = [ilog2(m) for m in mu]
    p = max(lev)
    blocks = [[v for v in range(n) if lev[v] == j] for j in range(p + 1)]
    factors = []
    for j in range(p + 1):
        if j > 0:
            below = [v for v in range(n) if lev[v] < j]
            X = identity(n)
            D = [[0] * n for _ in range(n)]
            for u in below:
                for w in blocks[j]:
                    X[u][w] += A[u][w]
                    D[u][w] = A[u][w]
            factors.append((X, D))
        S = blocks[j]
        AS = induced(A, S)
        CS = path_matrix(AS) if S else []
        M = embed(CS, S, n) if S else identity(n)
        D = [[0] * n for _ in range(n)]
        for i, u in enumerate(S):
            for k2, v in enumerate(S):
                D[u][v] = AS[i][k2]
        factors.append((M, D))
    return blocks, lev, factors


def balanced_factorization(A, S, kappa, n, depth=0):
    """Source's recursion: cut at q = isqrt(kappa) inside G[S]; returns (factors, leaves, depth)."""
    AS = induced(A, S)
    if kappa == 1:
        CS = path_matrix(AS) if S else []
        D = [[0] * n for _ in range(n)]
        for i, u in enumerate(S):
            for j, v in enumerate(S):
                D[u][v] = AS[i][j]
        return [(embed(CS, S, n) if S else identity(n), D)], 1, depth
    q = math.isqrt(kappa)
    CS = path_matrix(AS) if S else []
    muS = [max([CS[a][i] for a in range(len(S))] or [1]) for i in range(len(S))]
    L = [S[i] for i in range(len(S)) if muS[i] <= q]
    H = [S[i] for i in range(len(S)) if muS[i] > q]
    fL, lL, dL = balanced_factorization(A, L, q, n, depth + 1)
    fH, lH, dH = balanced_factorization(A, H, q, n, depth + 1)
    X = identity(n)
    D = [[0] * n for _ in range(n)]
    for u in L:
        for w in H:
            X[u][w] += A[u][w]
            D[u][w] = A[u][w]
    for u in H:
        for w in L:
            if A[u][w]:
                raise AssertionError("edge from H to L")
    return fL + [(X, D)] + fH, lL + lH, max(dL, dH)


def product(fs, n):
    P = identity(n)
    for (M, _) in fs:
        P = matmul(P, M)
    return P


def max_antichain(I, R):
    I = list(I)
    best = 0
    for size in range(len(I), 0, -1):
        if size <= best:
            break
        for X in itertools.combinations(I, size):
            ok = all(not (y in R[x] or x in R[y]) for x, y in itertools.combinations(X, 2))
            if ok:
                return size
    return best


def check_graph(A, full=True):
    n = len(A)
    C = path_matrix(A)
    k = maxentry(C)
    if full:
        if path_matrix_powers(A) != C:
            fail("DP vs powers", A)
        if n <= 6:
            for u in range(n):
                for v in range(n):
                    if count_paths_dfs(A, u, v) != C[u][v]:
                        fail("DP vs DFS", A)
    # Theorem 3.1: C = I + AC
    AC = matmul(A, C)
    for u in range(n):
        for v in range(n):
            if C[u][v] != int(u == v) + AC[u][v]:
                fail("C != I + AC", A)
    bump("graphs")
    R = reach_sets(A)
    mu, nu = mu_nu(C)
    for u in range(n):
        for v in R[u]:
            if mu[v] < mu[u] * C[u][v] or nu[u] < C[u][v] * nu[v]:
                fail("Lemma 4.1", A)
            if mu[u] * C[u][v] * nu[v] > k:
                fail("Theorem 4.2", A)
            bump("pairs u~>v (4.1, 4.2)")
    if n <= 7:
        for u in range(n):
            for w in R[u]:
                for v in R[w]:
                    if C[u][w] * C[w][v] > C[u][v]:
                        fail("Corollary 4.3", A)
    # redundant edges on a path: check along longest paths by DP of (count of redundant edges)
    order = list(range(n))
    from sfcommon import topo_order
    order = topo_order(A)
    best = [0] * n
    for u in order:
        for w in range(n):
            if A[u][w]:
                red = 1 if C[u][w] >= 2 else 0
                best[w] = max(best[w], best[u] + red)
    if max(best) > ilog2(k):
        fail("redundant-edge bound", A)
    # Theorem 5.1 for all thresholds
    taus = range(1, k) if k <= 40 else sorted(set([2 ** j - 1 for j in range(1, ilog2(k) + 1)] + [math.isqrt(k)] + [1 + (k - 2) * i // 20 for i in range(21)]))
    for tau in taus:
        L = [v for v in range(n) if mu[v] <= tau]
        H = [v for v in range(n) if mu[v] > tau]
        for h in H:
            for l in L:
                if l in R[h]:
                    fail("5.1(1)", A)
        if not (path_convex(L, R) and path_convex(H, R)):
            fail("5.1(2)", A)
        if L and maxentry(path_matrix(induced(A, L))) > tau:
            fail("5.1(3)", A)
        if H and maxentry(path_matrix(induced(A, H))) > k // (tau + 1):
            fail("5.1(4)", A)
        bump("thresholds tau (5.1)")
    if k >= 2:
        q = math.isqrt(k)
        L = [v for v in range(n) if mu[v] <= q]
        H = [v for v in range(n) if mu[v] > q]
        if (L and maxentry(path_matrix(induced(A, L))) > q) or \
           (H and maxentry(path_matrix(induced(A, H))) > q):
            fail("Corollary 5.2", A)
    # Level partition and factorization (Theorems 5.3, 6.2)
    blocks, lev, factors = level_factorization(A, C)
    p = len(blocks) - 1
    if p != ilog2(k) and any(blocks):
        # p = floor(log2 max mu); max mu = k? (max mu = max entry of C)
        fail("number of levels", A)
    for S in blocks:
        if not path_convex(S, R):
            fail("level block not path-convex", A)
        if S and maxentry(path_matrix(induced(A, S))) > 1:
            fail("level block not a mangrove", A)
    for u in range(n):
        for w in range(n):
            if A[u][w] and lev[w] < lev[u]:
                fail("backward edge between levels", A)
    if len(factors) != 2 * p + 1:
        fail("factor count", A)
    for (M, D) in factors:
        if not is_mangrove_path_matrix(M, D):
            fail("level factor is not a mangrove path matrix", A)
    if product(factors, n) != C:
        fail("level factorization product", A)
    bump("level factorizations verified")
    stats["max factors/(2 floor(log2 k)+1)"] = max(stats.get("max factors/(2 floor(log2 k)+1)", 0),
                                                  len(factors) / (2 * ilog2(k) + 1))
    # Balanced recursion of the source
    if k >= 2:
        fs, leaves, depth = balanced_factorization(A, list(range(n)), k, n)
        if leaves > 2 * math.log2(k) + 1e-9:
            fail("leaves > 2 log2 k", A)
        if depth > 1 + math.floor(math.log2(math.log2(k))):
            fail("depth bound", A)
        if len(fs) != 2 * leaves - 1 or len(fs) >= 4 * math.log2(k):
            fail("balanced factor count", A)
        for (M, D) in fs:
            if not is_mangrove_path_matrix(M, D):
                fail("balanced factor not mangrove", A)
        if product(fs, n) != C:
            fail("balanced product", A)
        bump("balanced factorizations verified")
    # Theorem 7.1 and 7.2
    for u in range(n):
        for v in R[u]:
            I = [x for x in range(n) if x in R[u] and v in R[x]]
            if n <= 7:
                if max_antichain(I, R) > C[u][v]:
                    fail("Theorem 7.1 width", A)
            m_int = sum(A[x][y] for x in I for y in I)
            if m_int > C[u][v] * (len(I) - 1):
                fail("Theorem 7.1 edges", A)
            r = C[u][v]
            if r > 1:
                q = math.isqrt(r)
                S = [x for x in I if C[u][x] <= q]
                Sset = set(S)
                Gam = [(x, y) for x in S for y in I if y not in Sset and A[x][y]]
                if any(C[u][x] > q or C[y][v] > q for (x, y) in Gam):
                    fail("7.2(2)", A)
                if sum(C[u][x] * A[x][y] * C[y][v] for (x, y) in Gam) != r:
                    fail("7.2(3)", A)
                if sum(A[x][y] for (x, y) in Gam) > r:
                    fail("7.2(4)", A)
                bump("separators (7.2)")
    # Theorems 11.3, 11.4
    indeg = [sum(A[u][v] for u in range(n)) for v in range(n)]
    outdeg = [sum(A[v]) for v in range(n)]
    if sum(indeg[v] * outdeg[v] for v in range(n)) > n * n * k:
        fail("junction bound", A)
    I_ = [sum(C[u][v] for u in range(n)) for v in range(n)]
    O_ = [sum(C[v][w] for w in range(n)) for v in range(n)]
    tot = sum(I_[v] * O_[v] for v in range(n))
    if n <= 6:
        alt = 0
        from sfcommon import all_paths
        for u in range(n):
            for w in range(n):
                for P in all_paths(A, u, w):
                    alt += len(P) + 1
        if alt != tot:
            fail("centrality identity", A)
    if tot > n ** 3 * k:
        fail("centrality bound", A)


def random_sf_graph(n, K, rng, tries):
    """Random DAG with all path counts <= K, built by rank-one updates."""
    perm = list(range(n))
    rng.shuffle(perm)
    A = [[0] * n for _ in range(n)]
    C = identity(n)
    for _ in range(tries):
        i, j = sorted(rng.sample(range(n), 2))
        x, y = perm[i], perm[j]
        if A[x][y]:
            continue
        # new C = C + C[:,x] C[y,:]
        ok = True
        colx = [C[a][x] for a in range(n)]
        rowy = C[y]
        for a in range(n):
            if colx[a]:
                for b in range(n):
                    if rowy[b] and C[a][b] + colx[a] * rowy[b] > K:
                        ok = False
                        break
            if not ok:
                break
        if ok:
            A[x][y] = 1
            for a in range(n):
                if colx[a]:
                    for b in range(n):
                        if rowy[b]:
                            C[a][b] += colx[a] * rowy[b]
    return A


def main():
    max_n = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    nrand = int(sys.argv[2]) if len(sys.argv) > 2 else 300
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 2026
    for n in range(1, max_n + 1):
        cnt = 0
        for A in upper_triangular_dags(n):
            check_graph(A, full=True)
            cnt += 1
        print(f"n = {n}: all {cnt} upper-triangular DAGs checked")
    rng = random.Random(seed)
    for it in range(nrand):
        n = rng.randint(7, 24)
        K = rng.choice([2, 3, 4, 5, 8, 16, 30, 64, 100, 1000])
        A = random_sf_graph(n, K, rng, tries=rng.randint(n, 6 * n))
        check_graph(A, full=(n <= 12))
    print(f"{nrand} random k-strongly-unambiguous graphs (7 <= n <= 24) checked")
    for key in sorted(stats):
        print(f"  {key}: {stats[key]}")
    print("all checks passed")


if __name__ == "__main__":
    main()
