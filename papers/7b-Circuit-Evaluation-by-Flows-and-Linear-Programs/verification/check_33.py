# Checks for 003f: Fibonacci LP point and minors; escape switching; Latin contraction over S3.
import random, itertools
from fractions import Fraction as Fr
random.seed(33)
F = [0, 1, 1]
for i in range(3, 80): F.append(F[-1] + F[-2])
for n in range(2, 40):
    delta = Fr(1, 2*(F[n+1]-1))
    x = [Fr(0), Fr(0)] + [delta*(F[i+1]-1) for i in range(2, n+1)]
    assert x[n] == Fr(1, 2)
    for i in range(2, n+1):
        assert 0 <= x[i] <= 1 and x[i] >= x[i-1] and x[i] >= x[i-2]
        assert x[i] - (x[i-1] + x[i-2]) == delta
print("Fibonacci point verified for n = 2..39")

def det(M):
    M = [[Fr(v) for v in row] for row in M]; k = len(M); d = Fr(1)
    for c in range(k):
        p = next((r for r in range(c, k) if M[r][c] != 0), None)
        if p is None: return Fr(0)
        if p != c: M[c], M[p] = M[p], M[c]; d = -d
        d *= M[c][c]
        for r in range(c+1, k):
            f = M[r][c] / M[c][c]
            M[r] = [a - f*b for a, b in zip(M[r], M[c])]
    return d
for m in range(2, 30):
    T = [[1 if i == j else (-1 if 1 <= i-j <= 2 else 0) for j in range(m)] for i in range(m)]
    assert det(T) == 1
    minor = [row[:m-1] for row in T[1:]]   # delete row 1 and column m
    assert abs(det(minor)) == F[m], (m, det(minor), F[m])
print("minor |det| = F_m verified for m = 2..29")

# escape switching on random monotone circuits
def run(n_in, gates, inputs, init):
    n = n_in + len(gates)
    val = list(inputs)
    for (t, a, b) in gates: val.append(val[a] & val[b] if t == 'A' else val[a] | val[b])
    sel = dict(init)
    rounds = 0; prevL = None; switched_count = {}
    while True:
        rounds += 1
        # L = vertices reaching a false input in strategy graph (children = predecessors)
        L = [False]*n
        for v in range(n):
            if v < n_in: L[v] = (inputs[v] == 0)
            else:
                t, a, b = gates[v-n_in]
                L[v] = (L[a] or L[b]) if t == 'A' else L[sel[v]]
        if prevL is not None: assert all(not L[v] or prevL[v] for v in range(n)), "not nested"
        for v in range(n):
            if not L[v]: assert val[v] == 1
        out = n - 1
        esc = [v for v in range(n_in, n) if gates[v-n_in][0] == 'O' and L[v]
               and any(not L[c] for c in gates[v-n_in][1:] if c != sel[v])]
        if not L[out]: return rounds, 1, val[out]
        if not esc: return rounds, 0, val[out]
        for v in esc:
            t, a, b = gates[v-n_in]
            sel[v] = a if (sel[v] == b and not L[a]) else b
            switched_count[v] = switched_count.get(v, 0) + 1
            assert switched_count[v] == 1
        prevL = L

worst = 0; trials = 0
for trial in range(3000):
    n_in = random.randint(1, 4); g = random.randint(1, 25)
    inputs = [random.randint(0, 1) for _ in range(n_in)]
    gates = []
    for v in range(n_in, n_in + g):
        a = random.randrange(v); b = random.randrange(v) if random.random() < 0.3 else max(0, v - 1 - random.randrange(min(v, 3)))
        gates.append((random.choice('AO'), a, b))
    n = n_in + g
    rk = [0]*n
    for v in range(n_in, n):
        t, a, b = gates[v-n_in]
        if a == b: rk[v] = rk[a]
        else: rk[v] = max(rk[a], rk[b]) if rk[a] != rk[b] else rk[a] + 1
    init = {}
    for v in range(n_in, n):
        t, a, b = gates[v-n_in]
        if t == 'O': init[v] = a if rk[a] >= rk[b] else b
    rounds, ans, truth = run(n_in, gates, inputs, init)
    assert ans == truth
    r = max(rk)
    assert rounds <= r + 1, (rounds, r)
    worst = max(worst, rounds - (r+1)); trials += 1
    # arbitrary initial strategy: correctness and at most one switch per gate
    init2 = {v: random.choice(gates[v-n_in][1:]) for v in init}
    rounds2, ans2, _ = run(n_in, gates, inputs, init2)
    assert ans2 == truth
print("escape switching: trials", trials, "max (rounds - (r+1)) =", worst)

# rank sets by reachability: R_{k+1} = vertices reaching a gate whose two distinct predecessors are in R_k
for trial in range(500):
    n_in = random.randint(1, 3); g = random.randint(1, 20); gates = []
    for v in range(n_in, n_in + g):
        gates.append(('A', random.randrange(v), random.randrange(v)))
    n = n_in + g; rk = [0]*n
    for v in range(n_in, n):
        _, a, b = gates[v-n_in]
        rk[v] = rk[a] if a == b else (max(rk[a], rk[b]) if rk[a] != rk[b] else rk[a]+1)
    R = set(range(n)); k = 0
    while R:
        assert R == {v for v in range(n) if rk[v] >= k}
        base = {v for v in range(n_in, n) if gates[v-n_in][1] != gates[v-n_in][2]
                and gates[v-n_in][1] in R and gates[v-n_in][2] in R}
        reach = set()
        for v in range(n):
            if v in base or (v >= n_in and any(c in reach for c in gates[v-n_in][1:])): reach.add(v)
        R = reach; k += 1
print("rank layers by reachability verified")

# Latin contraction over S3: compare D_K with brute force on small components
S3 = list(itertools.permutations(range(3)))
mul = {(a, b): tuple(a[b[i]] for i in range(3)) for a in S3 for b in S3}
inv = {a: next(b for b in S3 if mul[(a, b)] == (0, 1, 2)) for a in S3}
checked = 0
for trial in range(300):
    k = random.randint(2, 5)  # unassigned variables 0..k-1 ; edges q_v = phi(q_u) from one-anchor gates
    edges = []
    for _ in range(random.randint(k-1, k+2)):
        u, v = random.sample(range(k), 2); c = random.choice(S3); typ = random.randint(0, 2)
        if typ == 0: phi = {a: mul[(c, a)] for a in S3}        # z = c*y
        elif typ == 1: phi = {a: mul[(a, c)] for a in S3}      # z = x*c
        else: phi = {a: mul[(inv[a], c)] for a in S3}          # y = x^{-1} c
        edges.append((u, v, phi))
    unary = {v: set(random.sample(S3, random.randint(1, 6))) for v in range(k) if random.random() < 0.3}
    # connectivity
    adj = {v: [] for v in range(k)}
    for i, (u, v, phi) in enumerate(edges): adj[u].append(i); adj[v].append(i)
    seen = {0: {a: a for a in S3}}; stack = [0]; tree = set()
    while stack:
        u = stack.pop()
        for i in adj[u]:
            a_, b_, phi = edges[i]
            if a_ == u and b_ not in seen:
                seen[b_] = {r: phi[seen[u][r]] for r in S3}; tree.add(i); stack.append(b_)
            elif b_ == u and a_ not in seen:
                phinv = {phi[x]: x for x in S3}
                seen[a_] = {r: phinv[seen[u][r]] for r in S3}; tree.add(i); stack.append(a_)
    K = sorted(seen)
    DK = {r for r in S3 if all(seen[v][r] == edges[i][2][seen[edges[i][0]][r]] for i in range(len(edges))
                              if edges[i][0] in seen and edges[i][1] in seen for v in [edges[i][1]])
          and all(seen[v][r] in unary[v] for v in K if v in unary)}
    brute = set()
    for asg in itertools.product(S3, repeat=len(K)):
        q = dict(zip(K, asg))
        if all(q[v] == phi[q[u]] for (u, v, phi) in edges if u in q and v in q) and all(q[v] in unary[v] for v in K if v in unary):
            brute.add(q[0])
    assert brute == DK
    checked += 1
print("Latin contraction root domains verified:", checked)
