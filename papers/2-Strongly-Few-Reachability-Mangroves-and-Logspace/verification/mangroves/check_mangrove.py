"""Checks for Sections 5 and 6 (mangroves) and Corollary 7.4.

  Thm 5.3  hidden two-tree normal form
  Lem 5.4  subtree sizes = masses, rank order = preorder of the hidden out-tree
  Thm 6.2  every reduction of the equivalence theorem (Lemmas 6.3-6.5), run with promise-checking
           oracles: an oracle raises an error if a query violates its promise
  Cor 7.4  (b) the total mangrove language is decided correctly from an arbitrary
           "promise reachability algorithm" through the annotated verifier;
           (a) STCON_sf is decided from a promise mass algorithm, and N(s,t) is
           recovered from a total STCON_sf decider via the s-t interval (Lemma 7.3)

Run:  python3 check_mangrove.py   (about one minute)
"""
import itertools
import random
import sys

from common import (all_digraphs, all_labelled_dags, upper_dags, walk_counts, dag_counts,
                    max_count, is_acyclic, add_terminal_chain, induced, reach_closure)
from check_mass import verifier

random.seed(2026)
FAIL = []
STATS = {"queries": 0}


def check(cond, msg):
    if not cond:
        FAIL.append(msg)
        if len(FAIL) < 10:
            print("FAIL:", msg)


class PromiseViolation(Exception):
    pass


def is_mangrove(A):
    return is_acyclic(A) and max_count(dag_counts(A)) <= 1


def require(cond):
    if not cond:
        raise PromiseViolation()


# ------------------------------------------------------------ promise-checking oracles
def REACH(A, s, t):
    STATS["queries"] += 1
    require(is_mangrove(A))
    return dag_counts(A)[s][t]          # in {0,1}


def MASS(A, s):
    STATS["queries"] += 1
    require(is_mangrove(A))
    return sum(dag_counts(A)[s])


def PARENT(A, s, v):
    STATS["queries"] += 1
    require(is_mangrove(A))
    N = dag_counts(A)
    require(v != s and N[s][v] == 1)
    ps = [u for u in range(len(A)) if A[u][v] and N[s][u]]
    assert len(ps) == 1
    return ps[0]


def preorder_cone(A, s):
    """Ground truth: preorder of the hidden out-tree, children by increasing index."""
    out = []

    def rec(x):
        out.append(x)
        for y in range(len(A)):
            if A[x][y]:
                rec(y)
    rec(s)
    return out


def path_to(A, s, v):
    """The unique s-v path in a mangrove, as a vertex list."""
    N = dag_counts(A)
    path = [v]
    while path[-1] != s:
        x = path[-1]
        path.append([u for u in range(len(A)) if A[u][x] and N[s][u]][0])
    return path[::-1]


def CONE(A, s):
    STATS["queries"] += 1
    require(is_mangrove(A))
    return preorder_cone(A, s)


def RANK(A, s, P):
    STATS["queries"] += 1
    require(is_mangrove(A))
    require(P[0] == s and all(A[P[i]][P[i + 1]] for i in range(len(P) - 1)))
    return preorder_cone(A, s).index(P[-1]) + 1


def UNRANK(A, s, r):
    STATS["queries"] += 1
    require(is_mangrove(A))
    cone = preorder_cone(A, s)
    require(1 <= r <= len(cone))
    return path_to(A, s, cone[r - 1])


# ------------------------------------------------------------ the reductions of Theorem 6.1
def reach_via_mass(A, s, t):
    n = len(A)
    return MASS(add_terminal_chain(A, t, n + 1), s) // (n + 1)


def mass_via_reach(A, s, reach=REACH):
    return sum(reach(A, s, x) for x in range(len(A)))


def parent_via_reach(A, s, v):
    for u in range(len(A)):
        if A[u][v] and REACH(A, s, u):
            return u
    return None


def cone_via_parent(A, s, parent=PARENT):
    """Stackless Euler tour; state = (current vertex, previous vertex or None)."""
    n = len(A)
    out = [s]
    cur, prev = s, None            # prev is None: we just arrived from the parent
    while True:
        start = 0 if prev is None else prev + 1
        c = next((y for y in range(start, n) if A[cur][y]), None)
        if c is not None:
            out.append(c)
            cur, prev = c, None
        else:
            if cur == s:
                return out
            cur, prev = parent(A, s, cur), cur


def reach_via_parent(A, s, t):
    return int(t in cone_via_parent(A, s))


def reach_via_cone(A, s, t):
    return int(t in CONE(A, s))


def mass_via_cone(A, s):
    return len(CONE(A, s))


def rank_via_mass(A, s, P, mass=MASS):
    r = 1
    for i in range(len(P) - 1):
        x, y = P[i], P[i + 1]
        r += 1 + sum(mass(A, u) for u in range(y) if A[x][u])
    return r


def unrank_via_mass(A, s, r, mass=MASS):
    P = [s]
    x = s
    while r != 1:
        r -= 1
        for u in range(len(A)):
            if A[x][u]:
                mu = mass(A, u)
                if r <= mu:
                    P.append(u)
                    x = u
                    break
                r -= mu
    return P


def sentinel(A, s):
    """G' = G plus a root r (index n) and a sink z (index n+1), edges r->s, r->z."""
    n = len(A)
    B = [row[:] + [0, 0] for row in A] + [[0] * (n + 2), [0] * (n + 2)]
    B[n][s] = 1
    B[n][n + 1] = 1
    return B, n, n + 1


def mass_via_rank(A, s):
    B, r, z = sentinel(A, s)
    return RANK(B, r, [r, z]) - 2


def mass_via_unrank(A, s):
    B, r, z = sentinel(A, s)
    j = 1
    while True:
        if UNRANK(B, r, j) == [r, z]:
            return j - 2
        j += 1


def reach_via_rank(A, s, t):
    n = len(A)
    return mass_via_rank(add_terminal_chain(A, t, n + 1), s) // (n + 1)


# ------------------------------------------------------------ mangrove families
def relabel(A, perm):
    n = len(A)
    B = [[0] * n for _ in range(n)]
    for u in range(n):
        for v in range(n):
            B[perm[u]][perm[v]] = A[u][v]
    return B


def random_mangrove(n):
    A = [[0] * n for _ in range(n)]
    pairs = [(u, v) for u in range(n) for v in range(n) if u != v]
    random.shuffle(pairs)
    for (u, v) in pairs:
        A[u][v] = 1
        if not is_mangrove(A):
            A[u][v] = 0
    return A


def mangroves():
    for n in range(1, 6):
        for A in all_labelled_dags(n):
            if is_mangrove(A):
                yield A
    for A in upper_dags(6):
        if is_mangrove(A):
            yield relabel(A, random.sample(range(6), 6))
    for _ in range(300):
        yield random_mangrove(random.randint(7, 12))


def check_mangrove(A):
    n = len(A)
    N = dag_counts(A)
    for s in range(n):
        F = [v for v in range(n) if N[s][v]]
        # Theorem 5.2 (1): G[F_s] is an out-arborescence rooted at s
        check(all(v in F for x in F for v in range(n) if A[x][v]), "F_s closed")
        check(sum(1 for u in F if A[u][s]) == 0, "root has no in-edge in F_s")
        check(all(sum(1 for u in F if A[u][v]) == 1 for v in F if v != s),
              "unique in-neighbour inside F_s")
        # Lemma 5.3
        cone = preorder_cone(A, s)
        check(sorted(cone) == F, "preorder visits F_s once each")
        for u in F:
            sub = preorder_cone(A, u)
            check(set(sub) <= set(F) and len(sub) == sum(N[u]), "subtree = F_u, size = M(u)")
        for t in range(n):
            Bt = [v for v in range(n) if N[v][t]]
            if s == 0:  # Theorem 5.2 (2), checked once per t
                check(all(sum(1 for w in Bt if A[v][w]) == 1 for v in Bt if v != t),
                      "unique out-neighbour inside B_t")
            inter = sorted(set(F) & set(Bt))
            if N[s][t]:
                check(inter == sorted(path_to(A, s, t)), "F_s cap B_t = path")
            else:
                check(inter == [], "F_s cap B_t empty")
        # Theorem 6.1: the reductions
        M = sum(N[s])
        for t in range(n):
            check(reach_via_mass(A, s, t) == N[s][t], "REACH <= MASS")
            check(reach_via_parent(A, s, t) == N[s][t], "REACH <= PARENT")
            check(reach_via_cone(A, s, t) == N[s][t], "REACH <= CONE")
            check(reach_via_rank(A, s, t) == N[s][t], "REACH <= RANK (one query)")
        check(mass_via_reach(A, s) == M, "MASS <= REACH")
        check(mass_via_cone(A, s) == M, "MASS <= CONE")
        check(mass_via_rank(A, s) == M, "MASS <= RANK")
        check(mass_via_unrank(A, s) == M, "MASS <= UNRANK")
        for v in F:
            if v != s:
                check(parent_via_reach(A, s, v) == PARENT(A, s, v), "PARENT <= REACH")
        check(cone_via_parent(A, s) == cone, "CONE <= PARENT (preorder)")
        check(cone_via_parent(A, s, parent=lambda B, r, v: parent_via_reach(B, r, v)) == cone,
              "CONE <= REACH by composition")
        for j, v in enumerate(cone):
            P = path_to(A, s, v)
            check(rank_via_mass(A, s, P) == j + 1, "RANK <= MASS")
            check(unrank_via_mass(A, s, j + 1) == P, "UNRANK <= MASS")


def section6():
    count = 0
    try:
        for A in mangroves():
            count += 1
            check_mangrove(A)
    except PromiseViolation:
        check(False, "an oracle query violated its promise")
    print("Theorem 6.2: %d mangroves, %d oracle queries, no promise violation" %
          (count, STATS["queries"]))


# ------------------------------------------------------------ Corollary 7.4
def true_reach(A, s, t):
    return int(reach_closure(A)[s][t])


def make_garbage_reach(seed):
    def g(A, s, t):
        if is_mangrove(A):
            return true_reach(A, s, t)
        h = hash((seed, tuple(map(tuple, A)), s, t))
        return h & 1
    return g


def section7_total():
    algs = [true_reach] + [make_garbage_reach(i) for i in range(3)]
    tested = 0
    for n in range(1, 5):
        for A in all_digraphs(n, loops=True):
            mg = is_mangrove(A)
            R = reach_closure(A)
            for alg in algs:
                m = [mass_via_reach(A, v, reach=alg) for v in range(n)]
                for s in range(n):
                    for t in range(n):
                        tested += 1
                        got = verifier(A, s, t, 1, m)
                        check(got == (mg and R[s][t]), "total mangrove decider")
    print("Corollary 7.4(b): %d (graph, algorithm, s, t) cases, all correct" % tested)

    # Corollary 7.4(a), first implication: a mass procedure that is correct only on
    # k-strongly unambiguous inputs, fed to the verifier, decides STCON_sf exactly.
    def make_mass_alg(seed):
        def T(A, v, k):
            N = walk_counts(A)
            if max_count(N) <= k:
                return sum(N[v])                      # correct under the promise
            h = hash((seed, tuple(map(tuple, A)), v, k))
            if seed == 0:                             # true mass when finite, else junk
                tot = sum(N[v])
                return tot if tot != float("inf") else h % 7
            return h % (len(A) * k + 2)               # junk in the plausible range
        return T
    tested = 0
    for n in range(1, 4):
        for A in all_digraphs(n, loops=True):
            N = walk_counts(A)
            for seed in range(3):
                T = make_mass_alg(seed)
                for k in (1, 2, 3):
                    m = [T(A, v, k) for v in range(n)]
                    for s in range(n):
                        for t in range(n):
                            tested += 1
                            good = max_count(N) <= k and N[s][t] >= 1
                            check(verifier(A, s, t, k, m) == good, "STCON_sf from promise mass")
    print("Corollary 7.4(a), mass -> STCON_sf: %d cases, all correct" % tested)

    cases = 0
    fams = [A for n in range(1, 5) for A in all_labelled_dags(n)] + list(upper_dags(5))
    for A in fams:
        n = len(A)
        N = walk_counts(A) if n <= 4 else dag_counts(A)
        k = max_count(N)

        def stcon_sf(B, s, t, kk):          # a total decider used as a black box
            NB = walk_counts(B)
            return max_count(NB) <= kk and NB[s][t] >= 1

        for s in range(n):
            for t in range(n):
                cases += 1
                if not stcon_sf(A, s, t, k):
                    got = 0
                else:
                    I = [x for x in range(n) if stcon_sf(A, s, x, k) and stcon_sf(A, x, t, k)]
                    H = induced(A, I)
                    si, ti = I.index(s), I.index(t)
                    got = next(j for j in range(1, k + 1) if stcon_sf(H, si, ti, j))
                    NH = walk_counts(H)
                    check(max_count(NH) == NH[si][ti] == N[s][t], "interval maximum")
                check(got == N[s][t], "count from total decider")
    print("Corollary 7.4(a), STCON_sf -> COUNT via the interval: %d (DAG, s, t) cases, all correct" % cases)


if __name__ == "__main__":
    section6()
    section7_total()
    print("TOTAL FAILURES:", len(FAIL))
    sys.exit(1 if FAIL else 0)
