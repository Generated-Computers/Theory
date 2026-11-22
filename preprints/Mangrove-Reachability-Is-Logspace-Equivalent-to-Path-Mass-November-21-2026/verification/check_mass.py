"""Checks for Sections 3, 4, 5.1, 7 and 8 of the paper.

  Thm 3.1  path-mass fixed point (PM), and no nonnegative solution on cyclic graphs
  Cor 3.2  1 <= M(v) <= (n-1)k+1
  Prop 3.3 least nonnegative supersolution; none on cyclic graphs
  Thm 4.2  universal sink;  Thm 4.3 terminal chain;  quotient / remainder
  Thm 5.1  arithmetic coding: rank formula = preorder index, stackless unranking
  Thm 7.1  annotated verifier accepts exactly (valid instance, true mass vector)
  Thm 8.1-8.3  hidden diagonal scaling, stochastic similarity, determinant formula

Run:  python3 check_mass.py   (about one to two minutes)
"""
import itertools
import random
import sys
from fractions import Fraction

from common import (INF, all_digraphs, all_labelled_dags, upper_dags, walk_counts,
                    dag_counts, matrix_path_counts, masses, max_count, is_acyclic,
                    add_universal_sink, add_terminal_chain, walks_from_preorder,
                    rank_formula, unrank_stackless, out_edges, det_fraction,
                    solve_fraction, identity)

random.seed(2026)
FAIL = []


def check(cond, msg):
    if not cond:
        FAIL.append(msg)
        if len(FAIL) < 10:
            print("FAIL:", msg)


def satisfies_pm(A, m):
    n = len(A)
    return all(m[v] == 1 + sum(A[v][u] * m[u] for u in range(n)) for v in range(n))


def is_super(A, x):
    n = len(A)
    return all(x[v] >= 1 + sum(A[v][u] * x[u] for u in range(n)) for v in range(n))


# ---------------------------------------------------------------- Section 3
def section3():
    cnt = {"dag": 0, "cyc": 0, "super_dag": 0, "super_cyc": 0}
    for n in range(1, 5):
        for A in all_digraphs(n, loops=True):
            N = walk_counts(A)
            acyc = is_acyclic(A)
            check(acyc == (max_count(N) < INF), "acyclic iff finite counts")
            if acyc:
                cnt["dag"] += 1
                M = masses(A, N)
                check(satisfies_pm(A, M), "PM holds")
                sol = solve_fraction([[(1 if i == j else 0) - A[i][j] for j in range(n)]
                                      for i in range(n)], [1] * n)
                check(sol is not None and [int(x) for x in sol] == M, "unique PM solution")
                k = max_count(N)
                check(all(1 <= M[v] <= (n - 1) * k + 1 <= n * k for v in range(n)),
                      "mass range")
                if n <= 4:
                    # least supersolution inside the box x_v <= M(v)+1
                    boxes = [range(0, M[v] + 2) for v in range(n)]
                    sup = [x for x in itertools.product(*boxes) if is_super(A, x)]
                    check(tuple(M) in sup, "M is a supersolution")
                    check(all(all(x[v] >= M[v] for v in range(n)) for x in sup),
                          "every supersolution dominates M")
                    cnt["super_dag"] += 1
            else:
                cnt["cyc"] += 1
                if n <= 3:
                    box = range(0, 9)
                    for x in itertools.product(box, repeat=n):
                        check(not satisfies_pm(A, x), "no nonnegative PM solution, cyclic")
                        check(not is_super(A, x), "no nonnegative supersolution, cyclic")
                    cnt["super_cyc"] += 1
                sol = solve_fraction([[(1 if i == j else 0) - A[i][j] for j in range(n)]
                                      for i in range(n)], [1] * n)
                if sol is not None:
                    check(any(x < 0 for x in sol), "cyclic: rational PM solution not >= 0")
    print("Section 3: digraphs n<=4: %d DAGs, %d cyclic; supersolution boxes: %d DAGs, %d cyclic (n<=3)"
          % (cnt["dag"], cnt["cyc"], cnt["super_dag"], cnt["super_cyc"]))


# ---------------------------------------------------------------- Section 4 and 5.1
def dag_families():
    for n in range(1, 5):
        for A in all_labelled_dags(n):
            yield A
    for A in upper_dags(5):
        yield A
    for n in range(2, 4):
        for A in upper_dags(n, maxmult=2):   # multigraphs
            yield A


def section4_5():
    graphs = 0
    pairs = 0
    walks = 0
    for A in dag_families():
        n = len(A)
        graphs += 1
        N = walk_counts(A) if n <= 4 else dag_counts(A)
        check(N == matrix_path_counts(A), "N = I + A + ... + A^(n-1)")
        M = [sum(r) for r in N]
        k = max(1, max_count(N))
        # universal sink
        Gb = add_universal_sink(A)
        Nb = dag_counts(Gb)
        check(all(Nb[v][n] == M[v] for v in range(n)), "universal sink mass")
        check(max_count(Nb) <= n * k, "G_bot is nk-strongly unambiguous")
        # terminal chain (all pairs for n <= 4, a sample for larger graphs)
        B = n * k + 1
        prs = [(s, t) for s in range(n) for t in range(n)]
        if n >= 5:
            prs = random.sample(prs, 3)
        for (s, t) in prs:
            pairs += 1
            H = add_terminal_chain(A, t, B)
            NH = dag_counts(H)
            check(max_count(NH) <= k, "terminal chain preserves k")
            MH = sum(NH[s])
            check(MH == M[s] + B * N[s][t], "terminal-chain mass identity")
            check(MH // B == N[s][t] and MH % B == M[s], "quotient and remainder")
        # arithmetic coding
        for v in range(n):
            W = walks_from_preorder(A, v)
            check(len(W) == M[v], "number of walks from v is M(v)")
            for idx, w in enumerate(W):
                walks += 1
                check(rank_formula(A, M, v, w) == idx + 1, "rank = preorder index")
                check(unrank_stackless(A, lambda u: M[u], v, idx + 1) == w, "unranking")
    print("Sections 4-5.1: %d DAGs (incl. multigraphs), %d terminal-chain pairs, %d walks ranked/unranked"
          % (graphs, pairs, walks))


# ---------------------------------------------------------------- Section 7
def in_stcon_sf(N, s, t, k):
    return max_count(N) <= k and N[s][t] >= 1


def verifier(A, s, t, k, m):
    """The annotated verifier of Theorem 7.1, written as in the proof."""
    n = len(A)
    for v in range(n):
        if not (1 <= m[v] <= n * k):
            return False
    for v in range(n):
        if m[v] != 1 + sum(A[v][u] * m[u] for u in range(n)):
            return False
    count = [[0] * n for _ in range(n)]
    for a in range(n):
        for r in range(1, m[a] + 1):
            w = unrank_stackless(A, lambda u: m[u], a, r)
            b = w[-1][1] if w else a
            count[a][b] += 1
            if count[a][b] > k:
                return False
    return count[s][t] >= 1


def section7():
    calls = 0
    acc = 0
    for n in range(1, 4):
        for A in all_digraphs(n, loops=True):
            N = walk_counts(A)
            Mtrue = [sum(r) for r in N]
            cands = set(itertools.product(range(0, 5), repeat=n))
            if max(Mtrue) < INF:
                cands.add(tuple(Mtrue))
            for k in range(0, 4):
                for s in range(n):
                    for t in range(n):
                        good = in_stcon_sf(N, s, t, k)
                        for m in cands:
                            calls += 1
                            res = verifier(A, s, t, k, list(m))
                            acc += res
                            check(res == (good and list(m) == Mtrue), "verifier n<=3")
    # n = 4: every digraph, random (s,t), true mass and its one-coordinate perturbations
    for A in all_digraphs(4, loops=True):
        N = walk_counts(A)
        Mtrue = [sum(r) for r in N]
        fin = max(Mtrue) < INF
        base = Mtrue if fin else [1, 1, 1, 1]
        cands = [base] + [[base[j] + (d if j == i else 0) for j in range(4)]
                          for i in range(4) for d in (-1, 1)]
        for k in (1, 2, 3):
            s, t = random.randrange(4), random.randrange(4)
            good = in_stcon_sf(N, s, t, k)
            for m in cands:
                calls += 1
                res = verifier(A, s, t, k, m)
                acc += res
                check(res == (good and m == Mtrue), "verifier n=4")
    print("Section 7: %d verifier calls, %d accepted, all as predicted" % (calls, acc))


# ---------------------------------------------------------------- Section 8
def section8():
    graphs = 0
    for n in range(1, 5):
        for A in all_labelled_dags(n):
            graphs += 1
            N = walk_counts(A)
            m = [sum(r) for r in N]
            k = max_count(N)
            # Theorem 8.1
            for v in range(n):
                P = [Fraction(A[v][u] * m[u], m[v]) for u in range(n)]
                check(sum(P) == 1 - Fraction(1, m[v]), "row sum of P")
                check(P[v] == 0, "diagonal of I-P is one")
                margin = 1 - sum(abs(P[u]) for u in range(n) if u != v)
                check(margin == Fraction(1, m[v]) and margin >= Fraction(1, n * k), "margin")
            # Theorem 8.2: row stochastic and every complete path has probability 1/m(v)
            for v in range(n):
                row = sum(Fraction(A[v][u] * m[u], m[v]) for u in range(n)) + Fraction(1, m[v])
                check(row == 1, "stochastic row")
                total = Fraction(0)
                for w in walks_from_preorder(A, v):
                    p = Fraction(1)
                    x = v
                    for (a, b, c) in w:
                        p *= Fraction(m[b], m[a])
                        x = b
                    p *= Fraction(1, m[x])
                    check(p == Fraction(1, m[v]), "path probability")
                    total += p
                check(total == 1, "probabilities sum to one")
            # Theorem 8.3
            I = identity(n)
            for s in range(n):
                Mat = [[I[i][j] - A[i][j] + (1 if j == s else 0) for j in range(n)]
                       for i in range(n)]
                check(det_fraction(Mat) - 1 == m[s], "determinant formula")
            check(det_fraction([[I[i][j] - A[i][j] for j in range(n)] for i in range(n)]) == 1,
                  "det(I-A)=1")
    print("Section 8: %d labelled DAGs (n<=4)" % graphs)


if __name__ == "__main__":
    section3()
    section4_5()
    section7()
    section8()
    print("TOTAL FAILURES:", len(FAIL))
    sys.exit(1 if FAIL else 0)
