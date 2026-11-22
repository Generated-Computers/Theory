"""Checks for Sections 9, 10 and 11 of the paper.

  Thm 9.1   recurrence (W) = direct count of paths with interior in S_i,
            Schur complement identity, bound by k, for every elimination order
  Cor 9.2   mass as one final fill coefficient of G_bot
  Prop 9.3  all orders bounded by k  <=>  k-strongly unambiguous (DAGs)
  Prop 9.4  diamond chains: Boolean displayed fills, 2^r terminal paths
  Thm 9.6   BFW -> MASS via the induced graph and the terminal chain
  Thm 10.1  cumulative-power characterization (all digraphs, multigraphs)
  Lem 10.2  single-power identity
  Thm 10.3  single-power totalization on all inputs, and tightness of n*k+1
  Thm 10.5, 10.6, 10.8, Rem 10.10   no-growth powering, mass as one entry,
            NGPower <-> COUNT, subdivision of multigraphs
  Prop 10.12 sparse midpoint census (counts and number of queries)
  Thm 11.2  chain trick on rooted reach-unambiguous graphs

Run:  python3 check_elimination_powers.py   (a few minutes)
"""
import itertools
import math
import random
import sys
from fractions import Fraction

from common import (INF, all_digraphs, all_labelled_dags, upper_dags, walk_counts, dag_counts,
                    max_count, is_acyclic, add_universal_sink, add_terminal_chain, induced,
                    matmul, identity, matpow, topological_order, solve_fraction)

random.seed(2026)
FAIL = []


def check(cond, msg):
    if not cond:
        FAIL.append(msg)
        if len(FAIL) < 10:
            print("FAIL:", msg)


# ------------------------------------------------------------------ Section 9
def w_direct(A, S, u, v):
    """Number of nonempty u-v paths whose interior vertices all lie in S (u != v)."""
    if u == v:
        return 0
    n = len(A)
    cnt = 0
    stack = [u]
    while stack:
        x = stack.pop()
        for y in range(n):
            if A[x][y]:
                for _ in range(A[x][y]):
                    if y == v:
                        cnt += 1
                    elif y in S:
                        stack.append(y)
    return cnt


def fills(A, order):
    """W_0, W_1, ... by recurrence (W); W_i is a dict on ordered pairs of R_i."""
    n = len(A)
    W = {(u, v): (A[u][v] if u != v else 0) for u in range(n) for v in range(n)}
    seq = [dict(W)]
    R = set(range(n))
    for x in order:
        R.discard(x)
        W = {(u, v): (0 if u == v else W[(u, v)] + W[(u, x)] * W[(x, v)])
             for u in R for v in R}
        seq.append(dict(W))
    return seq


def schur(A, S):
    n = len(A)
    R = [v for v in range(n) if v not in S]
    S = list(S)
    M = [[(1 if i == j else 0) - A[i][j] for j in range(n)] for i in range(n)]
    out = {}
    if not S:
        return {(u, v): Fraction(M[u][v]) for u in R for v in R}
    MSS = [[M[a][b] for b in S] for a in S]
    for v in R:
        col = solve_fraction(MSS, [M[a][v] for a in S])   # M_SS^{-1} M_Sv
        for u in R:
            out[(u, v)] = M[u][v] - sum(M[u][S[i]] * col[i] for i in range(len(S)))
    return out


def section9():
    tested = 0
    for n in range(1, 6):
        fam = list(all_labelled_dags(n)) if n <= 4 else list(upper_dags(5))
        for A in fam:
            N = walk_counts(A) if n <= 4 else dag_counts(A)
            koff = max([N[u][v] for u in range(n) for v in range(n) if u != v] or [0])
            orders = list(itertools.permutations(range(n)))
            if n == 5:
                orders = random.sample(orders, 8)
            maxfill = 0
            for order in orders:
                tested += 1
                seq = fills(A, order)
                for i in range(n + 1):
                    S = set(order[:i])
                    for (u, v), w in seq[i].items():
                        check(w == w_direct(A, S, u, v), "recurrence (W) = direct count")
                        check(0 <= w <= koff, "fill bounded by k")
                        maxfill = max(maxfill, w)
                    if n <= 4:
                        sc = schur(A, S)
                        for (u, v), val in sc.items():
                            check(val == (1 if u == v else 0) - seq[i][(u, v)],
                                  "Schur complement = I - W_i")
            if n <= 4:
                check(maxfill == koff, "max over all orders = max_{u!=v} N(u,v)")
            topo = topological_order(A)
            for order in (topo, topo[::-1]):
                for Wi in fills(A, order):
                    check(all(w == A[u][v] for (u, v), w in Wi.items() if u != v),
                          "topological orders display only A")
            # Corollary 9.2
            k = max(1, max_count(N))
            Gb = add_universal_sink(A)
            for v in range(n):
                order = [x for x in range(n) if x != v] + [v, n]
                seq = fills(Gb, order)
                check(seq[n - 1][(v, n)] == sum(N[v]), "mass as final fill")
                check(all(w <= n * k for Wi in seq for w in Wi.values()), "fills <= nk")
            # Theorem 9.6: BFW -> MASS
            if n <= 4:
                order = list(range(n))
                random.shuffle(order)
                seq = fills(A, order)
                for i in range(n + 1):
                    S = order[:i]
                    for (u, v), w in seq[i].items():
                        if u == v:
                            continue
                        verts = sorted(set(S) | {u, v})
                        H = induced(A, verts)
                        hu, hv = verts.index(u), verts.index(v)
                        kk = max(1, max_count(dag_counts(H)))
                        Bq = len(verts) * kk + 1
                        HH = add_terminal_chain(H, hv, Bq)
                        check(sum(dag_counts(HH)[hu]) // Bq == w, "BFW via one mass query")
    # Proposition 9.4: diamond chains
    for r in range(1, 7):
        n = 3 * r + 1
        A = [[0] * n for _ in range(n)]
        for i in range(r):
            z, a, b, z2 = 3 * i, 3 * i + 1, 3 * i + 2, 3 * i + 3
            A[z][a] = A[z][b] = A[a][z2] = A[b][z2] = 1
        N = dag_counts(A)
        check(N[0][n - 1] == 2 ** r, "diamond chain count")
        for order in (list(range(n)), list(range(n))[::-1]):
            check(all(w <= 1 for Wi in fills(A, order) for w in Wi.values()),
                  "diamond chain: Boolean displayed fills")
    print("Section 9: %d (DAG, order) pairs, diamond chains r<=6" % tested)


# ------------------------------------------------------------------ Section 10
def block_power(A, r):
    """B_G^r computed as a full 2n x 2n matrix power."""
    n = len(A)
    B = [[0] * (2 * n) for _ in range(2 * n)]
    for i in range(n):
        for j in range(n):
            B[i][j] = A[i][j]
        B[i][n + i] = 1
        B[n + i][n + i] = 1
    return matpow(B, r)


def section10():
    tested = 0
    # exhaustive: all digraphs n<=3 with multiplicities <=2, all simple digraphs n=4
    fams = [(n, 2) for n in (1, 2, 3)] + [(4, 1)]
    for (n, mm) in fams:
        for A in all_digraphs(n, loops=True, maxmult=mm):
            tested += 1
            N = walk_counts(A)
            powers = [identity(n)]
            for _ in range(3 * n + 1):
                powers.append(matmul(powers[-1], A))
            for k in range(0, 4):
                ksu = max_count(N) <= k
                L = n * k
                S = [[sum(powers[i][u][v] for i in range(L + 1)) for v in range(n)]
                     for u in range(n)]
                if k >= 1:
                    check(ksu == (max_count(S) <= k), "cumulative-power characterization")
                # single-power totalization, via Lemma 10.2's block form
                UL = powers[L + 1]
                allk = (max_count(UL) <= k and max_count(S) <= k and 1 <= k)
                for s in range(n):
                    for t in range(n):
                        lhs = ksu and N[s][t] >= 1
                        rhs = allk and S[s][t] >= 1
                        check(lhs == rhs, "single-power totalization")
    # Lemma 10.2 on a sample, against full block powers
    sample = [A for A in all_digraphs(3, loops=True, maxmult=2)]
    for A in random.sample(sample, 1500):
        n = len(A)
        P = identity(n)
        S = [[0] * n for _ in range(n)]
        for r in range(1, 3 * n + 2):
            S = [[S[i][j] + P[i][j] for j in range(n)] for i in range(n)]
            P = matmul(P, A)
            Br = block_power(A, r)
            ok = all(Br[i][j] == P[i][j] and Br[i][n + j] == S[i][j] and Br[n + i][j] == 0
                     and Br[n + i][n + j] == (1 if i == j else 0)
                     for i in range(n) for j in range(n))
            check(ok, "single-power identity")
    # tightness: the n-cycle passes the test at exponent nk but is cyclic
    for n in range(2, 7):
        A = [[1 if v == (u + 1) % n else 0 for v in range(n)] for u in range(n)]
        for k in range(1, 5):
            Bnk = block_power(A, n * k)
            check(max_count(Bnk) <= k and Bnk[0][n + 0] >= 1, "n-cycle passes at nk")
            Bnk1 = block_power(A, n * k + 1)
            check(max_count(Bnk1) > k, "n-cycle fails at nk+1")
    # Theorems 10.5, 10.6 and COUNT -> NGPower on labelled DAGs n <= 4
    for n in range(1, 5):
        for A in all_labelled_dags(n):
            N = walk_counts(A)
            k = max_count(N)
            for r in range(1, n * k + 2):
                check(max_count(block_power(A, r)) <= k, "no-growth powering")
            Bn = block_power(A, n)
            check(all(Bn[s][n + t] == N[s][t] for s in range(n) for t in range(n)),
                  "COUNT -> NGPower entry")
            H = [row[:] + [1] for row in A] + [[0] * n + [1]]
            for r in range(1, n + 3):
                Hr = matpow(H, r)
                check(max_count(Hr) <= n * k, "entries of H^r <= nk")
            Hn = matpow(H, n)
            check(all(Hn[v][n] == sum(N[v]) for v in range(n)), "mass as one power entry")
    # NGPower -> COUNT via the layered graph
    for _ in range(400):
        d = random.randint(1, 5)
        T = random.randint(0, 6)
        p = random.choice([0.2, 0.35, 0.5])
        C = [[1 if random.random() < p else 0 for _ in range(d)] for _ in range(d)]
        K = max(max_count(matpow(C, r)) for r in range(T + 1))
        V = d * (T + 1)
        Lg = [[0] * V for _ in range(V)]
        for r in range(T):
            for x in range(d):
                for y in range(d):
                    if C[x][y]:
                        Lg[r * d + x][(r + 1) * d + y] = 1
        NL = dag_counts(Lg)
        check(max_count(NL) <= K, "layered graph is K-strongly unambiguous")
        CT = matpow(C, T)
        check(all(NL[i][T * d + j] == CT[i][j] for i in range(d) for j in range(d)),
              "NGPower -> COUNT")
    # Remark 10.10: subdivision of edge occurrences
    for n in (2, 3):
        for A in upper_dags(n, maxmult=2):
            occ = [(u, v) for u in range(n) for v in range(n) for _ in range(A[u][v])]
            V = n + len(occ)
            S = [[0] * V for _ in range(V)]
            for i, (u, v) in enumerate(occ):
                S[u][n + i] = 1
                S[n + i][v] = 1
            NS, NA = dag_counts(S), dag_counts(A)
            check(all(NS[u][v] == NA[u][v] for u in range(n) for v in range(n)),
                  "subdivision preserves counts")
            check(max_count(NS) <= max(1, max_count(NA)), "subdivision preserves k")
    print("Section 10: %d digraphs/multigraphs exhaustively (k=0..3), cycles n<=6, 400 NGPower instances"
          % tested)


def midpoint_census(A, s, t, Vm, count_oracle):
    """Interval-tree census; returns (list of (x, multiplicity), number of queries)."""
    n = len(A)
    queries = [0]

    def q(X):
        queries[0] += 1
        keep = [v for v in range(n) if v not in Vm or v in X]
        H = induced(A, keep)
        return count_oracle(H, keep.index(s), keep.index(t))

    out = []

    def visit(lo, hi, val):
        if val == 0:
            return
        if hi - lo == 1:
            out.append((Vm[lo], val))
            return
        mid = (lo + hi) // 2
        visit(lo, mid, q(set(Vm[lo:mid])))
        visit(mid, hi, q(set(Vm[mid:hi])))

    visit(0, len(Vm), q(set(Vm)))
    return out, queries[0]


def section10_census():
    done = 0
    while done < 300:
        h = random.randint(2, 5)
        widths = [random.randint(1, 5) for _ in range(h + 1)]
        layers = []
        idx = 0
        for w in widths:
            layers.append(list(range(idx, idx + w)))
            idx += w
        n = idx
        A = [[0] * n for _ in range(n)]
        p = random.choice([0.3, 0.5, 0.7])
        for i in range(h):
            for x in layers[i]:
                for y in layers[i + 1]:
                    if random.random() < p:
                        A[x][y] = 1
        N = dag_counts(A)
        k = max_count(N)
        if k > 6:
            continue
        m = random.randint(1, h - 1) if h >= 2 else 1
        s = random.choice([v for L in layers[:m] for v in L])
        t = random.choice([v for L in layers[m + 1:] for v in L])
        Vm = layers[m]
        res, nq = midpoint_census(A, s, t, Vm, lambda H, a, b: dag_counts(H)[a][b])
        truth = [(x, N[s][x] * N[x][t]) for x in Vm if N[s][x] * N[x][t] > 0]
        check(sorted(res) == sorted(truth), "midpoint census output")
        bound = 1 + 2 * k * math.ceil(math.log2(len(Vm))) if len(Vm) > 1 else 1
        check(nq <= bound, "midpoint census query bound")
        done += 1
    print("Proposition 10.12: %d random layered strongly-few DAGs" % done)


# ------------------------------------------------------------------ Section 11
def section11():
    done = 0
    while done < 400:
        n = random.randint(2, 7)
        A = [[1 if (u != v or random.random() < 0.1) and random.random() < 0.3 else 0
              for v in range(n)] for u in range(n)]
        r = random.randrange(n)
        N = walk_counts(A)
        if max(N[r]) > 1:
            continue
        for t in range(n):
            H = add_terminal_chain(A, t, n + 1)
            NH = walk_counts(H)
            check(max(NH[r]) <= 1, "chain preserves rooted unambiguity")
            check(sum(NH[r]) // (n + 1) == N[r][t], "rooted chain trick")
        done += 1
    print("Theorem 11.2: %d random rooted reach-unambiguous graphs (cycles allowed off the cone)"
          % done)


if __name__ == "__main__":
    section9()
    section10()
    section10_census()
    section11()
    print("TOTAL FAILURES:", len(FAIL))
    sys.exit(1 if FAIL else 0)
