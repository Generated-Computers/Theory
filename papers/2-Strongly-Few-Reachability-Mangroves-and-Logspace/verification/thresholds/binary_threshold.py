"""Checks for Section 5 (binary thresholds and the one-pair cap).

  python3 binary_threshold.py

(H) Hardness gadget of Theorem 5.1.  A toy "machine" is a time-layered DAG with
    layers 0..T in which every vertex of a layer t < T has exactly two distinct
    successors in layer t+1 (the coin is recorded in the configuration).  Layers may
    contain configurations unreachable from the start.  A set of final
    configurations is "rejecting".  We build H: a -> start, rejecting -> b, and a
    chain of T+1 diamonds from a to b, K = 2^{T+1} + 2^{T-1} - 1, and check on all
    pairs: H is a DAG, N(a,b) = 2^{T+1} + R, every other pair has at most 2^T walks,
    and H is valid for K iff R <= 2^{T-1} - 1 iff A > 2^{T-1}.  For full binary trees
    every value R = 0..2^T is realized.  The source's complement version (accepting
    sink, K = 2^{T+1} + 2^{T-1}) is valid iff A <= 2^{T-1}.
(M) Membership: the MSB-first comparison machine has exactly K+1 accepting branches,
    for all K <= 600 and padded bit lengths; and the logspace conjunctive truth-table
    condition (acyclicity by "no walk of length n", reachability, (K+1) - f_uv > 0
    with f_uv = walks of length <= n-1) agrees with membership in BIN-STCON_sf on all
    digraphs with n <= 3 vertices, all s, t and K = 0..5.
(P) One-pair cap (Theorem 5.4): N(s,t) >= k+1 iff N^{<=(k+2)n}(s,t) >= k+1;
    N(s,t) < INF iff no s-t walk has length in [n, 2n]; the (k+1)-fold prefix maps
    s~>t to N >= k+1 and non-reachability to N = 0.  All digraphs n <= 3, k = 1..3.
"""
import random

from walks import (INF, add_edge, add_vertex, bounded_counts_from, copy_graph,
                   dag_all_pairs, exact_counts, from_matrix, is_simple)


def toy_machine(T, width, rng, full_tree=False):
    """Return (adj, start, finals) for a layered machine DAG with T >= 1."""
    adj, layers = [], []
    if full_tree:
        for t in range(T + 1):
            layers.append([add_vertex(adj) for _ in range(2 ** t)])
        for t in range(T):
            for i, u in enumerate(layers[t]):
                add_edge(adj, u, layers[t + 1][2 * i])
                add_edge(adj, u, layers[t + 1][2 * i + 1])
        # unreachable garbage configurations with two successors each
        for t in range(T):
            g = add_vertex(adj)
            succ = rng.sample(layers[t + 1], 2) if len(layers[t + 1]) >= 2 else None
            if succ:
                add_edge(adj, g, succ[0])
                add_edge(adj, g, succ[1])
        return adj, layers[0][0], layers[T]
    for t in range(T + 1):
        layers.append([add_vertex(adj) for _ in range(width if t else max(1, width // 2))])
    for t in range(T):
        for u in layers[t]:
            a, b = rng.sample(layers[t + 1], 2)
            add_edge(adj, u, a)
            add_edge(adj, u, b)
    return adj, layers[0][0], layers[T]


def build_H(mach, start, finals, rej, T, sink_set):
    H = copy_graph(mach)
    a = add_vertex(H)
    b = add_vertex(H)
    add_edge(H, a, start)
    for f in sink_set:
        add_edge(H, f, b)
    d = a
    for i in range(T + 1):  # T+1 diamonds
        x, y = add_vertex(H), add_vertex(H)
        nxt = b if i == T else add_vertex(H)
        add_edge(H, d, x)
        add_edge(H, d, y)
        add_edge(H, x, nxt)
        add_edge(H, y, nxt)
        d = nxt
    return H, a, b


def check_gadget(T, mach, start, finals, rej, stats):
    acc = [f for f in finals if f not in rej]
    Nm = dag_all_pairs(mach)
    total = sum(Nm[start][f] for f in finals)
    assert total == 2 ** T, (total, T)
    R = sum(Nm[start][f] for f in rej)
    A = total - R
    # direct reduction (rejecting sink)
    H, a, b = build_H(mach, start, finals, rej, T, rej)
    assert is_simple(H)
    N = dag_all_pairs(H)  # raises if cyclic
    C = 2 ** (T + 1)
    K = C + 2 ** (T - 1) - 1
    other = max(N[u][v] for u in range(len(H)) for v in range(len(H)) if (u, v) != (a, b))
    ok = N[a][b] == C + R and other <= 2 ** T and N[a][b] >= 1
    valid = all(N[u][v] <= K for u in range(len(H)) for v in range(len(H)))
    ok = ok and (valid == (R <= 2 ** (T - 1) - 1) == (A > 2 ** (T - 1)))
    # source's complement version (accepting sink)
    H2, a2, b2 = build_H(mach, start, finals, rej, T, acc)
    N2 = dag_all_pairs(H2)
    K2 = C + 2 ** (T - 1)
    valid2 = all(N2[u][v] <= K2 for u in range(len(H2)) for v in range(len(H2)))
    ok = ok and N2[a2][b2] == C + A and (valid2 == (A <= 2 ** (T - 1)))
    stats["gadget"] += 1
    stats["gadget_bad"] += not ok
    stats["R_values"].add((T, R))


def comparison_machine_count(K, ell):
    bits = [(K >> (ell - 1 - j)) & 1 for j in range(ell)]
    count = 0
    for g in range(1 << ell):
        state = "eq"
        for j in range(ell):
            gb = (g >> (ell - 1 - j)) & 1
            if state == "eq":
                if gb > bits[j]:
                    state = "rej"
                    break
                if gb < bits[j]:
                    state = "lt"
        count += state in ("eq", "lt")
    return count


def walks_exact_length(adj, L):
    n = len(adj)
    total = 0
    for u in range(n):
        cur = [0] * n
        cur[u] = 1
        for _ in range(L):
            nxt = [0] * n
            for x in range(n):
                if cur[x]:
                    for y, m in adj[x].items():
                        nxt[y] += cur[x] * m
            cur = nxt
        total += sum(cur)
    return total


def main():
    rng = random.Random(2026)
    stats = dict(gadget=0, gadget_bad=0, R_values=set())
    # (H) full binary trees: all rejecting counts R
    for T in range(1, 6):
        for _ in range(1):
            mach, start, finals = toy_machine(T, 0, rng, full_tree=True)
            for R in range(2 ** T + 1):
                rej = set(rng.sample(finals, R))
                check_gadget(T, mach, start, finals, rej, stats)
    # (H) random merging layered machines
    for _ in range(400):
        T = rng.randrange(1, 7)
        width = rng.randrange(2, 7)
        mach, start, finals = toy_machine(T, width, rng)
        rej = set(f for f in finals if rng.random() < 0.5)
        check_gadget(T, mach, start, finals, rej, stats)
    allR = all((T, R) in stats["R_values"] for T in range(1, 6) for R in range(2 ** T + 1))
    print("(H) gadget instances: %d, failures: %d, all R in [0,2^T] realized for T<=5: %s"
          % (stats["gadget"], stats["gadget_bad"], allR))
    # (M) comparison machine
    bad = 0
    for K in range(0, 601):
        L0 = max(1, K.bit_length())
        for ell in (L0, L0 + 1, L0 + 2):
            bad += comparison_machine_count(K, ell) != K + 1
    print("(M) comparison machine: K = 0..600, 3 bit lengths each, failures: %d" % bad)
    # (M) ctt condition versus membership
    tests = bad = 0
    for n in range(1, 4):
        for bits in range(1 << (n * n)):
            adj = from_matrix(bits, n)
            N = exact_counts(adj)
            acyclic = walks_exact_length(adj, n) == 0
            f = [bounded_counts_from(adj, u, n - 1) for u in range(n)]
            for s in range(n):
                for t in range(n):
                    for K in range(6):
                        member = all(N[u][v] <= K for u in range(n) for v in range(n)) and N[s][t] >= 1
                        cond = acyclic and f[s][t] > 0 and all(
                            (K + 1) - f[u][v] > 0 for u in range(n) for v in range(n))
                        tests += 1
                        bad += member != cond
    print("(M) GapL conjunction vs BIN-STCON_sf: %d instances, %d failures" % (tests, bad))
    # (P) one-pair cap
    tests = bad = 0
    for n in range(1, 4):
        for bits in range(1 << (n * n)):
            adj = from_matrix(bits, n)
            N = exact_counts(adj)
            for s in range(n):
                for k in (1, 2, 3):
                    bc = bounded_counts_from(adj, s, (k + 2) * n)
                    for t in range(n):
                        tests += 1
                        bad += (N[s][t] >= k + 1) != (bc[t] >= k + 1)
                bn1 = bounded_counts_from(adj, s, n - 1)
                b2n = bounded_counts_from(adj, s, 2 * n)
                for t in range(n):
                    tests += 1
                    bad += (N[s][t] < INF) != (b2n[t] - bn1[t] == 0)
                for k in (1, 2, 3):
                    H = copy_graph(adj)
                    r = add_vertex(H)
                    for _ in range(k + 1):
                        x = add_vertex(H)
                        add_edge(H, r, x)
                        add_edge(H, x, s)
                    NH = exact_counts(H)
                    for t in range(n):
                        tests += 1
                        exp_ok = (NH[r][t] == 0) if N[s][t] == 0 else (NH[r][t] >= k + 1)
                        bad += not exp_ok
    print("(P) one-pair cap checks: %d, failures: %d" % (tests, bad))


if __name__ == "__main__":
    main()
