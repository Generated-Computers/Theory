"""Checks for the StrongFewL-hardness construction (Section 4).

  python3 strongfew_hardness.py

A toy "configuration multigraph" is a random acyclic multigraph (parallel edges
model distinct transitions with the same successor) with an initial configuration
and a set of accepting configurations.  Let P be its maximum all-pairs walk count
and |C| its number of configurations.  The construction subdivides every
transition occurrence by a private midpoint and adds a collector t with an edge
from each accepting configuration.  Checked on 2000 random instances: the output
is a simple DAG; every ordered pair has at most |C| * P walks (the threshold of
Theorem 4.1); walk counts between original configurations are preserved; and
N(s, t) >= 1 iff some accepting configuration is reachable from s.
"""
import random

from walks import add_edge, add_vertex, dag_all_pairs, is_simple


def main():
    rng = random.Random(2026)
    tests = bad = 0
    for _ in range(2000):
        n = rng.randrange(1, 8)
        conf = [dict() for _ in range(n)]
        for u in range(n):
            for v in range(u + 1, n):
                if rng.random() < 0.35:
                    conf[u][v] = rng.randrange(1, 3)
        perm = list(range(n))
        rng.shuffle(perm)  # hide the topological order
        M = [dict() for _ in range(n)]
        for u in range(n):
            for v, m in conf[u].items():
                M[perm[u]][perm[v]] = m
        s = rng.randrange(n)
        acc = [v for v in range(n) if rng.random() < 0.3]
        NM = dag_all_pairs(M)
        P = max(NM[u][v] for u in range(n) for v in range(n))
        G = [dict() for _ in range(n)]
        for u in range(n):
            for v, m in M[u].items():
                for _ in range(m):
                    w = add_vertex(G)
                    add_edge(G, u, w)
                    add_edge(G, w, v)
        t = add_vertex(G)
        for a in acc:
            add_edge(G, a, t)
        ok = is_simple(G)
        NG = dag_all_pairs(G)
        q = n * P
        ok = ok and all(NG[u][v] <= q for u in range(len(G)) for v in range(len(G)))
        ok = ok and all(NG[u][v] == NM[u][v] for u in range(n) for v in range(n))
        ok = ok and ((NG[s][t] >= 1) == any(NM[s][a] >= 1 for a in acc))
        tests += 1
        bad += not ok
    print("StrongFewL construction: %d instances, %d failures" % (tests, bad))


if __name__ == "__main__":
    main()
