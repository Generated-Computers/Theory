import itertools, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check_core import core, trace, embed  # runs check_core main with default NMAX=7 on import
def dgc(j):
    B, H, delta = core(j); J = [None] + list(j); rank = {b: k+1 for k, b in enumerate(B)}
    arcs = set()
    for b in B:
        for d in (delta[b-1], delta[J[b]]):
            if d[0] == 'v': arcs.add((B[d[1]-1], b))
    return B, arcs
def depth(V, arcs):
    V = sorted(V); dp = {}
    for v in V:
        dp[v] = 1 + max([dp[u] for (u, w) in arcs if w == v and u in dp] or [0])
    return max(dp.values() or [0])
def delta_M(V, arcs, M):
    for k in range(len(V)+1):
        for X in itertools.combinations(V, k):
            Vr = [v for v in V if v not in X]; ar = {(u, w) for (u, w) in arcs if u in Vr and w in Vr}
            if depth(Vr, ar) <= M: return k
for L in range(1, 8):
    j = [0, 1, 1] + sum([[2*t-1, 2*t-1] for t in range(2, L+1)], [])
    B, arcs = dgc(j)
    assert B == list(range(3, 2*L+2, 2)), B
    assert arcs == {(2*t-1, 2*t+1) for t in range(2, L+1)}, arcs
    for M in range(0, L+1): assert delta_M(B, arcs, M) == L // (M+1)
    x = trace(j); assert all(x[2*t+1] == 0 for t in range(2, L+1))
for L in range(2, 9):
    gates = [(('a',1),('a',2)), (('w',1),('a',1))] + [(('w',i-1),('w',i-2)) for i in range(3, L+1)]
    for a in itertools.product((0,1), repeat=2):
        j, Rep = embed(list(a), gates)
        assert len(j) == 5 + 4*L
        B, arcs = dgc(j); W = [Rep[('w',i)] for i in range(1, L+1)]
        assert B == W
        exp = {(W[i-2], W[i-1]) for i in range(2, L+1)} | {(W[i-3], W[i-1]) for i in range(3, L+1)}
        assert arcs == exp
        if L <= 7:
            for M in range(0, 3): assert delta_M(B, arcs, M) >= L // (M+1)
print("006g checks passed")
