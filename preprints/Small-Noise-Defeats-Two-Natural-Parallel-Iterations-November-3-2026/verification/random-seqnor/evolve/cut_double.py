# Cut-map doubling with BDDs (NOTE.md §5j). Cuts at multiples of a leaf length L0. Level 0: for each
# leaf block, the exact map from the live set at its first cut to the live set at its next cut, by
# symbolic forward simulation (BDDs, larger positions on top). Level t: compose adjacent maps (vector
# composition), so after log2(n/L0) levels the map from the start to every dyadic cut is known; the
# start state is x_0 = 1, so a top-down pass gives the exact state at every cut, and each leaf block
# is then evaluated from its cut state. Parallel time: L0 + 2 log2(n/L0) map operations; work is
# governed by the largest map, which this script reports. Every value is checked against the trace.
# usage: python3 -I cut_double.py file.bin L0 [node_cap]
import os, struct, sys
sys.setrecursionlimit(100000)
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bdd_probe import BDD, load, live_sets

def vector_compose(B, f, sub, memo):
    """f over variables (levels); sub: level -> BDD over earlier variables (or variable itself)"""
    if f <= 1: return f
    r = memo.get(f)
    if r is not None: return r
    v = B.var[f]
    g = sub.get(v)
    if g is None: g = B.mk(v, 0, 1)
    r = B.ite(g, vector_compose(B, B.hi[f], sub, memo), vector_compose(B, B.lo[f], sub, memo))
    memo[f] = r
    return r

def run(n, j, L0, node_cap):
    last = live_sets(n, j)
    x = [1] + [0] * n
    for i in range(1, n + 1): x[i] = int(not (x[i - 1] or x[j[i]]))
    cuts = list(range(1, n + 2, L0))
    if cuts[-1] != n + 1: cuts.append(n + 1)
    live = {c: [p for p in range(c) if last[p] >= c] for c in cuts}   # O(n^2/L0) but fine at test sizes
    B = BDD()
    level = lambda p: -p                          # larger positions nearer the top
    # level 0: leaf maps; map = dict p -> BDD over variables live(c0), for p in live(c1)
    maps = []
    for a, b in zip(cuts, cuts[1:]):
        val = {p: B.mk(level(p), 0, 1) for p in live[a]}
        for i in range(a, b):
            val[i] = B.nor(val[i - 1], val[j[i]])
        maps.append({p: val[p] for p in live[b]})
        if len(B.var) > node_cap: return dict(ok=False, why='node cap at leaves', nodes=len(B.var))
    # doubling: a balanced tree of segment maps; tree[t][k] maps the state at cut start(t,k) to the
    # state at cut end(t,k)
    maxmap = max(B.shared_size(list(m.values()))[0] for m in maps)
    tree = [[(k, k + 1, m) for k, m in enumerate(maps)]]
    while len(tree[-1]) > 1:
        seg, nxt = tree[-1], []
        for t in range(0, len(seg) - 1, 2):
            (a0, a1, m1), (b0, b1, m2) = seg[t], seg[t + 1]
            sub = {level(p): g for p, g in m1.items()}
            memo = {}
            m = {p: vector_compose(B, g, sub, memo) for p, g in m2.items()}
            nxt.append((a0, b1, m))
            maxmap = max(maxmap, B.shared_size(list(m.values()))[0])
            if len(B.var) > node_cap:
                return dict(ok=False, why='node cap at level %d' % len(tree), nodes=len(B.var), maxmap=maxmap)
        if len(seg) % 2: nxt.append(seg[-1])
        tree.append(nxt)
        if len(B.memo) > 3_000_000: B.memo.clear()
    levels = len(tree) - 1
    def evaluate(f, assign):
        while f > 1:
            f = B.hi[f] if assign[-B.var[f]] else B.lo[f]
        return f
    # top-down pass: only x_0 = 1 is given; each level derives the state at the boundary between two
    # children by applying the left child's map to the parent's start state
    state = {0: {0: 1}}                            # cut index -> state (values of the live set)
    for t in range(levels, 0, -1):
        children = tree[t - 1]
        for k, (a0, b1, _) in enumerate(tree[t]):
            if 2 * k + 1 < len(children):
                c0, c1, m = children[2 * k]
                st = state[c0]
                state[c1] = {p: evaluate(g, st) for p, g in m.items()}
    ok = True
    for k in range(len(cuts)):
        for p, v in state.get(k, {}).items():
            if v != x[p]: ok = False
    missing = len(cuts) - 1 - sum(1 for k in range(len(cuts) - 1) if k in state)
    # finally every leaf block is evaluated from its derived cut state (sequential L0 steps per leaf)
    for k, (a, b) in enumerate(zip(cuts, cuts[1:])):
        st = dict(state[k]); vals = dict(st)
        for i in range(a, b):
            vals[i] = int(not (vals[i - 1] or vals[j[i]]))
            if vals[i] != x[i]: ok = False
    return dict(ok=ok, missing=missing, leaves=len(maps), levels=levels, maxmap=maxmap, nodes=len(B.var),
                rounds=2 * L0 + 2 * levels)

if __name__ == '__main__':
    n, j = load(sys.argv[1]); L0 = int(sys.argv[2]); cap = int(sys.argv[3]) if len(sys.argv) > 3 else 6_000_000
    r = run(n, j, L0, cap)
    print('%-26s n=%-6d L0=%-4d %s' % (sys.argv[1].split('/')[-1], n, L0, ' '.join('%s=%s' % kv for kv in r.items())))
