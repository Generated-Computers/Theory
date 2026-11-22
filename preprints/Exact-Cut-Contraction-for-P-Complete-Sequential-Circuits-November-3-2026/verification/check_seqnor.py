# Checks for manuscript 011b
import random, itertools
random.seed(2)

def seqnor(j):  # j[i] for i=1..n, j[0] unused
    n = len(j) - 1
    x = [1] + [0]*n
    for i in range(1, n+1): x[i] = 1 - (x[i-1] | x[j[i]])
    return x

def greedy_mis(j):
    n = len(j) - 1
    adj = {i: set() for i in range(n+1)}
    for i in range(1, n+1):
        for u in (i-1, j[i]): adj[i].add(u); adj[u].add(i)
    sel = set()
    for v in range(n+1):
        if not (adj[v] & sel): sel.add(v)
    return [1 if v in sel else 0 for v in range(n+1)]

def jump_rule(j):
    n = len(j) - 1
    S = [0]
    while True:
        cand = [t for t in range(S[-1]+2, n+1) if j[t] not in S]
        if not cand: break
        S.append(min(cand))
    return [1 if v in S else 0 for v in range(n+1)]

cnt = 0
for n in range(1, 9):
    for js in itertools.product(*[range(i) for i in range(1, n+1)]):
        j = [None] + list(js)
        x = seqnor(j)
        assert greedy_mis(j) == x
        assert jump_rule(j) == x
        cnt += 1
print("9.1 / 9.2: exhaustive over all parent arrays, n <= 8 (%d instances) OK" % cnt)

# ---- Thm 10.1 exact cut externalization ----
def evalc(x0, G, pi):  # G[i] = 4-bit table index (u,v)->G[i][2u+v]
    n = len(pi) - 1
    x = [x0] + [0]*n
    for i in range(1, n+1): x[i] = G[i][2*x[i-1] + x[pi[i]]]
    return x

ID, NOT, ZERO, ONE = (0, 1), (1, 0), (0, 0), (1, 1)   # unary maps as (f(0), f(1))
def comp(f, g):  # f after g
    return (f[g[0]], f[g[1]])

def externalize(x, G, pi, b):
    n = len(pi) - 1
    internal = [i for i in range(b+1, n+1) if pi[i] > b]
    h = [b] + internal
    q = len(internal)
    rank = {}  # rank of internal position
    for r, p in enumerate(h): rank[p] = r
    # prefix compositions Phi[i] for external i>b: map from x_{last internal <= i-1} (or b) to x_i
    Phi = {}
    cur = ID; last = b
    lastint = {}
    for i in range(b+1, n+1):
        if pi[i] > b:   # internal
            cur = ID; last = i
            Phi[i] = ID
        else:
            psi = (G[i][0*2 + x[pi[i]]], G[i][1*2 + x[pi[i]]])
            cur = comp(psi, cur)
            Phi[i] = cur
        lastint[i] = last
    lastint[b] = b; Phi[b] = ID
    Gp = [None]; pip = [None]
    for r in range(1, q+1):
        hr = h[r]
        A = Phi[hr - 1] if hr - 1 > b and pi[hr-1] <= b else ID
        # A maps y_{r-1} to x_{hr-1}
        p = pi[hr]
        s = rank[lastint[p]] if p > b else None
        assert p > b
        Bm = Phi[p] if pi[p] <= b and p != lastint[p] else ID
        # if p is internal, Phi[p]=ID anyway
        Bm = Phi[p]
        tab = [G[hr][2*A[u] + Bm[v]] for u in (0, 1) for v in (0, 1)]
        Gp.append(tab); pip.append(s)
    return x[b], Gp, pip, h, Phi, lastint

trials = 0
for trial in range(3000):
    n = random.randint(1, 30)
    pi = [None] + [random.randrange(i) for i in range(1, n+1)]
    if random.random() < 0.3:   # local-ish
        pi = [None] + [max(0, i - 1 - random.randrange(3)) for i in range(1, n+1)]
    G = [None] + [[random.randint(0, 1) for _ in range(4)] for _ in range(n)]
    x0 = random.randint(0, 1)
    x = evalc(x0, G, pi)
    for b in range(0, n):
        y0, Gp, pip, h, Phi, lastint = externalize(x, G, pi, b)
        q = len(Gp) - 1
        assert q == sum(1 for i in range(b+1, n+1) if pi[i] > b)
        assert all(0 <= pip[r] < r for r in range(1, q+1))
        y = evalc(y0, Gp, pip) if q > 0 else [y0]
        assert all(y[r] == x[h[r]] for r in range(q+1))
        # reconstruction of every suffix gate
        rk = {p: r for r, p in enumerate(h)}
        for i in range(b+1, n+1):
            m = Phi[i]; base = y[rk[lastint[i]]]
            assert m[base] == x[i]
        trials += 1
print("10.1 residual + reconstruction: %d (instance, cut) pairs OK" % trials)

# ---- crossing-area identity and the counterexample to the 'EP regime' claim ----
for trial in range(2000):
    n = random.randint(1, 40)
    pi = [None] + [random.randrange(i) for i in range(1, n+1)]
    c = [sum(1 for i in range(b+1, n+1) if pi[i] <= b) for b in range(n)]
    assert sum(c) == sum(i - pi[i] for i in range(1, n+1))
print("10.4 crossing-area identity: 2000 trials OK")

for m in [10, 50, 200]:
    n = 2*m
    pi = [None] + [i-1 for i in range(1, m+1)] + [0]*(n - m)   # chain prefix, then gates reading x_0
    span = sum(i - pi[i] for i in range(1, n+1))
    assert span >= n*n/4
    qb = lambda b, P, N: sum(1 for i in range(b+1, N+1) if P[i] > b)
    assert qb(m, pi, n) == 0
    # the prefix (a chain) has no cut with alpha^g+beta^g<=1-eta for gamma=1/2
    pre = pi[:m+1]
    best = min((b/m)**0.5 + (qb(b, pre, m)/m)**0.5 for b in range(m))
    print("counterexample m=%d: span/n^2=%.3f, q(m)=0, best prefix cut norm (gamma=1/2)=%.3f" % (m, span/n/n, best))
