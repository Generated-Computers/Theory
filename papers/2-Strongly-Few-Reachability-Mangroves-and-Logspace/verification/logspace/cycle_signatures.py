"""Checks for Sections 5 and 6: cycle-space signatures and blocks.

1. Signature counting (Theorem 5.4): for a connected sub-multigraph with a
   spanning tree, the number of z in GF(2)^c with Q + sum z_j Z_j a directed
   x-y path equals the number of directed simple x-y paths.  Checked against
   DFS enumeration of simple paths on all digraphs with loops on n <= 3, all
   loopless digraphs on n = 4 (cyclic ones included; antiparallel arcs are
   parallel undirected edges) and random digraphs on 5..8 vertices.
2. Signature cycle detection (Theorem 5.4) against a topological sort.
3. Block membership by the Menger test (Lemma 6.1) against Tarjan's
   algorithm on all undirected graphs with n <= 5 and random ones.
4. Route and product formula (Lemma 6.2): the number of directed simple u-v
   paths is the product of the blockwise signature counts along the route of
   separating vertices, on all oriented graphs with n <= 5 and random ones.
5. The total decider of Theorem 6.3 against brute force, k = 1..4, and the
   largest number of signature bits used against bcw(G).
Usage: python3 cycle_signatures.py [seed]
"""
import sys
import random
import itertools
from common import (all_digraphs, all_oriented, random_digraph, random_dag, cycle_rank_max,
                    und_edges, components, simple_path_counts, is_acyclic,
                    blocks_tarjan, walk_counts, INF)


# ------------------------------------------------------------ signatures
def spanning_tree(n, arcs):
    """Canonical spanning forest of the underlying multigraph of `arcs`
    (list of (tail, head)): scan in order, keep an arc iff it joins two
    different components of the arcs kept so far."""
    parent = list(range(n))

    def find(x):
        while parent[x] != x:
            x = parent[x]
        return x
    tree, chords = [], []
    for i, (x, y) in enumerate(arcs):
        rx, ry = find(x), find(y)
        if rx == ry:
            chords.append(i)
        else:
            parent[rx] = ry
            tree.append(i)
    return tree, chords


def tree_path(n, arcs, tree, x, y):
    """Bitmask (over arc indices) of the tree path between x and y."""
    nbr = [[] for _ in range(n)]
    for i in tree:
        a, b = arcs[i]
        nbr[a].append((b, i))
        nbr[b].append((a, i))
    prev = {x: None}
    stack = [x]
    while stack:
        a = stack.pop()
        for (b, i) in nbr[a]:
            if b not in prev:
                prev[b] = (a, i)
                stack.append(b)
    if y not in prev:
        return None
    mask, cur = 0, y
    while prev[cur] is not None:
        a, i = prev[cur]
        mask |= 1 << i
        cur = a
    return mask


def fundamental(n, arcs):
    tree, chords = spanning_tree(n, arcs)
    Z = []
    for i in chords:
        a, b = arcs[i]
        Z.append((1 << i) | (tree_path(n, arcs, tree, a, b) if a != b else 0))
    return tree, chords, Z


def is_directed_path(n, arcs, mask, x, y):
    sel = [arcs[i] for i in range(len(arcs)) if mask >> i & 1]
    outd = [0] * n
    ind = [0] * n
    out = [None] * n
    for (a, b) in sel:
        outd[a] += 1
        ind[b] += 1
        out[a] = b
    for v in range(n):
        want = (0, 1) if v == x else (1, 0) if v == y else None
        if want is not None:
            if (ind[v], outd[v]) != want:
                return False
        elif (ind[v], outd[v]) not in ((0, 0), (1, 1)):
            return False
    steps, v = 0, x                       # follow the unique out-arcs from x
    while v != y:
        v = out[v]
        steps += 1
        if steps > n:
            return False
    return steps == len(sel)


def is_directed_cycle(n, arcs, mask):
    sel = [arcs[i] for i in range(len(arcs)) if mask >> i & 1]
    if not sel:
        return False
    outd = [0] * n
    ind = [0] * n
    out = [None] * n
    for (a, b) in sel:
        outd[a] += 1
        ind[b] += 1
        out[a] = b
    if any((ind[v], outd[v]) not in ((0, 0), (1, 1)) for v in range(n)):
        return False
    start = sel[0][0]
    steps, v = 0, start
    while True:
        v = out[v]
        steps += 1
        if v == start:
            break
    return steps == len(sel)


def signature_count(n, arcs, x, y, stats=None):
    """Number of directed simple x-y paths in the connected multigraph `arcs`
    (x != y), by enumerating GF(2)^c."""
    tree, chords, Z = fundamental(n, arcs)
    Q = tree_path(n, arcs, tree, x, y)
    if Q is None:
        return 0
    c = len(chords)
    if stats is not None:
        stats["bits"] = max(stats.get("bits", 0), c)
    count = 0
    for z in range(1 << c):
        mask = Q
        for j in range(c):
            if z >> j & 1:
                mask ^= Z[j]
        if is_directed_path(n, arcs, mask, x, y):
            count += 1
    return count


def signature_has_cycle(n, arcs):
    tree, chords, Z = fundamental(n, arcs)
    c = len(chords)
    for y in range(1, 1 << c):
        mask = 0
        for j in range(c):
            if y >> j & 1:
                mask ^= Z[j]
        if is_directed_cycle(n, arcs, mask):
            return True
    return False


def arcs_of(adj):
    n = len(adj)
    return [(u, v) for u in range(n) for v in range(n) if adj[u][v]]


def check_signatures(adj, tally):
    n = len(adj)
    arcs = arcs_of(adj)
    comp = components(n, arcs)
    P = simple_path_counts(adj)
    for x in range(n):
        for y in range(n):
            if x == y:
                continue
            if comp[x] != comp[y]:
                got = 0
            else:
                sub = [a for a in arcs if comp[a[0]] == comp[x]]
                got = signature_count(n, sub, x, y)
            tally["sig"] += 1
            if got != P[x][y]:
                tally["errors"] += 1
                print("SIGNATURE COUNT MISMATCH", adj, x, y, got, P[x][y])
    cyc = any(signature_has_cycle(n, [a for a in arcs if comp[a[0]] == c])
              for c in set(comp))
    tally["cyc"] += 1
    if cyc == is_acyclic(adj):
        tally["errors"] += 1
        print("CYCLE DETECTION MISMATCH", adj)


# ------------------------------------------------------------------ blocks
def menger_same_block(n, edges, e, f):
    """Edges e != f of a simple graph lie on a common simple cycle iff the
    subdivision vertices p_e, p_f are connected and stay connected after
    deleting any single original vertex."""
    pe, pf = n, n + 1
    E2 = [ed for i, ed in enumerate(edges) if i not in (e, f)]
    a, b = edges[e]
    c, d = edges[f]
    E2 += [(a, pe), (pe, b), (c, pf), (pf, d)]
    if components(n + 2, E2)[pe] != components(n + 2, E2)[pf]:
        return False
    for x in range(n):
        comp = components(n + 2, E2, frozenset([x]))
        if comp[pe] != comp[pf]:
            return False
    return True


def blocks_menger(n, edges):
    m = len(edges)
    label = list(range(m))
    for e in range(m):
        for f in range(e):
            if menger_same_block(n, edges, e, f):
                label[e] = min(label[e], label[f])
    groups = {}
    for e in range(m):
        groups.setdefault(label[e], set()).add(e)
    return [frozenset(g) for g in groups.values()]


def simple_und_edges(adj):
    n = len(adj)
    return [(u, v) for u in range(n) for v in range(u + 1, n) if adj[u][v] or adj[v][u]]


# ------------------------------------------------------- route and product
def route(n, edges, blocks, u, v, compx):
    """Separators of u,v in route order, then the route blocks."""
    sep = [x for x in range(n) if x not in (u, v) and compx[x][u] != compx[x][v]]
    # w precedes w' iff w separates u from w'
    order = sorted(sep, key=lambda w: sum(1 for w2 in sep if w2 != w and compx[w2][u] != compx[w2][w]))
    for i, w in enumerate(order):     # the relation must be a linear order
        assert sum(1 for w2 in sep if w2 != w and compx[w2][u] != compx[w2][w]) == i
    seq = [u] + order + [v]
    route_blocks = []
    for i in range(len(seq) - 1):
        x, y = seq[i], seq[i + 1]
        cand = [B for B in blocks
                if any(x in edges[j] for j in B) and any(y in edges[j] for j in B)]
        assert len(cand) == 1, "consecutive route vertices share exactly one block"
        route_blocks.append((x, y, cand[0]))
    return route_blocks


def block_counts(adj, stats):
    """Simple-path counts of all pairs by the blockwise product (Lemma 6.2)."""
    n = len(adj)
    edges = simple_und_edges(adj)
    blocks = blocks_tarjan(n, edges)
    comp = components(n, edges)
    compx = [components(n, edges, frozenset([x])) for x in range(n)]
    C = [[0] * n for _ in range(n)]
    for u in range(n):
        for v in range(n):
            if u == v:
                C[u][v] = 1
                continue
            if comp[u] != comp[v]:
                continue
            prod = 1
            for (x, y, B) in route(n, edges, blocks, u, v, compx):
                arcs = []
                for j in sorted(B):
                    a, b = edges[j]
                    arcs.append((a, b) if adj[a][b] else (b, a))
                prod *= signature_count(n, arcs, x, y, stats)
            C[u][v] = prod
    return C


def decide_C(adj, s, t, ks, stats):
    """Total decider of Theorem 6.3 (saturation at k+1), run for each k in ks
    (the counts do not depend on k, so they are computed once)."""
    n = len(adj)
    no = {k: False for k in ks}
    for u in range(n):
        if adj[u][u]:
            return no
        for v in range(u + 1, n):
            if adj[u][v] and adj[v][u]:
                return no
    edges = simple_und_edges(adj)
    blocks = blocks_tarjan(n, edges)
    for B in blocks:                     # blockwise cycle detection
        arcs = []
        for j in sorted(B):
            a, b = edges[j]
            arcs.append((a, b) if adj[a][b] else (b, a))
        if signature_has_cycle(n, arcs):
            return no
    C = block_counts(adj, stats)
    out = {}
    for k in ks:
        if k == 0 or any(min(C[u][v], k + 1) > k for u in range(n) for v in range(n)):
            out[k] = False
        else:
            out[k] = C[s][t] >= 1
    return out


def bcw(adj):
    n = len(adj)
    edges = simple_und_edges(adj)
    best = 0
    for B in blocks_tarjan(n, edges):
        vs = {x for j in B for x in edges[j]}
        best = max(best, len(B) - len(vs) + 1)
    return best


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 2026
    rng = random.Random(seed)
    tally = {"sig": 0, "cyc": 0, "blk": 0, "prod": 0, "dec": 0, "errors": 0}
    # 1-2: signatures
    for n in range(1, 4):
        for adj in all_digraphs(n, loops=True):
            check_signatures(adj, tally)
    for adj in all_digraphs(4):
        check_signatures(adj, tally)
    done = 0
    while done < 300:                    # random digraphs with cycle rank <= 9
        n = rng.randint(5, 8)
        adj = random_digraph(n, rng.choice([0.1, 0.15, 0.2, 0.25]), rng)
        if cycle_rank_max(adj) <= 9:
            check_signatures(adj, tally)
            done += 1
    print(f"signature counts checked: {tally['sig']} pairs; "
          f"signature cycle detection checked: {tally['cyc']} graphs")
    # 3: blocks
    for n in range(1, 6):
        pairs = [(u, v) for u in range(n) for v in range(u + 1, n)]
        for mask in range(1 << len(pairs)):
            edges = [pairs[i] for i in range(len(pairs)) if mask >> i & 1]
            tally["blk"] += 1
            if set(blocks_menger(n, edges)) != set(blocks_tarjan(n, edges)):
                tally["errors"] += 1
                print("BLOCK MISMATCH", n, edges)
    for _ in range(300):
        n = rng.randint(6, 9)
        pairs = [(u, v) for u in range(n) for v in range(u + 1, n)]
        edges = [p for p in pairs if rng.random() < 0.3]
        tally["blk"] += 1
        if set(blocks_menger(n, edges)) != set(blocks_tarjan(n, edges)):
            tally["errors"] += 1
            print("BLOCK MISMATCH", n, edges)
    print(f"Menger block test vs Tarjan: {tally['blk']} undirected graphs")
    # 4-5: product formula and decider
    stats = {"bits": 0}
    maxbits_over_bcw = 0
    graphs = [adj for n in range(1, 6) for adj in all_oriented(n)]
    n_exh = len(graphs)
    while len(graphs) < n_exh + 400:     # then 400 random graphs with bcw <= 8
        n = rng.randint(6, 10)
        adj = random_dag(n, rng.choice([0.2, 0.3, 0.4]), rng)
        if rng.random() < 0.3:          # add a few backward arcs
            for _ in range(2):
                u, v = rng.sample(range(n), 2)
                if not adj[v][u]:
                    adj[u][v] = 1
        if bcw(adj) <= 8:
            graphs.append(adj)
    for adj in graphs:
        n = len(adj)
        st = {"bits": 0}
        C = block_counts(adj, st)
        P = simple_path_counts(adj)
        tally["prod"] += 1
        if C != P:
            tally["errors"] += 1
            print("PRODUCT FORMULA FAILS", adj)
        b = bcw(adj)
        if st["bits"] > b:
            tally["errors"] += 1
            print("BITS EXCEED BCW", adj)
        stats["bits"] = max(stats["bits"], st["bits"])
        N = walk_counts(adj)
        got = decide_C(adj, 0, n - 1, range(0, 5), {})
        for k in range(0, 5):
            want = all(N[u][v] <= k for u in range(n) for v in range(n)) and N[0][n - 1] >= 1
            tally["dec"] += 1
            if got[k] != want:
                tally["errors"] += 1
                print("DECIDER C MISMATCH", adj, k)
    print(f"product formula checked on {tally['prod']} graphs (all pairs); "
          f"decider runs: {tally['dec']}; largest signature length used: {stats['bits']} "
          f"(never above bcw)")
    print(f"errors: {tally['errors']}")


if __name__ == "__main__":
    main()
