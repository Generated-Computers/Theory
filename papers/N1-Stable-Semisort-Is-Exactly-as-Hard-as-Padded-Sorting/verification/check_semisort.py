# Checks for manuscript 011a (stable semisort reductions, PAE identity, anchors)
import random, itertools, math
from fractions import Fraction
random.seed(1)

def is_stable_semisort(A, keyf, out):
    # out is a list of indices (a permutation of range(n))
    n = len(A)
    if sorted(out) != list(range(n)): return False
    # contiguity
    seen = set(); prev = None
    for idx in out:
        k = keyf(A[idx])
        if k != prev:
            if k in seen: return False
            seen.add(k); prev = k
    # stability
    last = {}
    for idx in out:
        k = keyf(A[idx])
        if k in last and last[k] > idx: return False
        last[k] = idx
    return True

def usemi_adversarial(T, keyf):
    # unstable semisort: groups contiguous, arbitrary group order, arbitrary order inside
    groups = {}
    for t in T: groups.setdefault(keyf(t), []).append(t)
    gl = list(groups.values()); random.shuffle(gl)
    out = []
    for g in gl:
        g = g[:]; random.shuffle(g); out += g
    return out

def padded_sort(X, c=3):
    # X: list of (z, payload) with distinct z; return array of c*n slots, increasing z, gaps allowed
    n = len(X)
    Xs = sorted(X)
    slots = [None]*(c*n)
    pos = sorted(random.sample(range(c*n), n))
    for p, x in zip(pos, Xs): slots[p] = x
    return slots

def closure(A, keyf):
    n = len(A)
    T = [(keyf(A[i]), i) for i in range(n)]
    T = usemi_adversarial(T, lambda t: t[0])
    s = [1 if j == 0 or T[j][0] != T[j-1][0] else 0 for j in range(n)]
    g = []; acc = 0
    for j in range(n): acc += s[j]; g.append(acc-1)  # inclusive-1 = exclusive of starts
    gid = [None]*n
    for j in range(n): gid[T[j][1]] = g[j]
    z = [(n+1)*gid[i] + i for i in range(n)]
    assert len(set(z)) == n and max(z) < (n+1)**2
    P = padded_sort([(z[i], i) for i in range(n)])
    out = [p[1] for p in P if p is not None]
    return out

for trial in range(2000):
    n = random.randint(1, 40)
    K = random.randint(1, n)
    A = [random.choice(['k%d' % random.randint(0, K) for _ in range(3)]) for _ in range(n)]
    assert is_stable_semisort(A, lambda a: a, closure(A, lambda a: a))
print("Thm 3.3 closure: 2000 adversarial trials OK")

# ---- K.1 reductions ----
def stable_int_sort(keys):
    # IS oracle: returns permutation of indices sorted stably by key in [0,n]
    return sorted(range(len(keys)), key=lambda i: (keys[i], i))

def DS_via_IS(zs):
    n = len(zs)
    q = [z // (n+1) for z in zs]; r = [z % (n+1) for z in zs]
    assert all(0 <= v <= n for v in q + r)
    p1 = stable_int_sort(r)
    p2 = stable_int_sort([q[i] for i in p1])
    return [p1[j] for j in p2]

def IS_via_DS(a):
    n = len(a)
    z = [(n+1)*a[i] + i for i in range(n)]
    assert len(set(z)) == n and max(z) < (n+1)**2
    return sorted(range(n), key=lambda i: z[i])  # DS oracle (any correct sort of distinct keys)

def SS_oracle(A, keyf):
    # stable semisort oracle with adversarial group order
    order = []
    groups = {}
    for i, a in enumerate(A): groups.setdefault(keyf(a), []).append(i)
    gl = list(groups.values()); random.shuffle(gl)
    for g in gl: order += g
    return order

def IS_via_SS(a):
    n = len(a)
    o = SS_oracle(a, lambda x: x)
    # descriptors: (key, start, length)
    D = [None]*(n+1)
    j = 0
    while j < n:
        k = a[o[j]]; s = j
        while j < n and a[o[j]] == k: j += 1
        assert D[k] is None
        D[k] = (s, j - s)   # direct addressing: distinct keys, no conflicts
    B = [0]*(n+2)
    for k in range(n+1): B[k+1] = B[k] + (D[k][1] if D[k] else 0)
    out = [None]*n
    for p in range(n):
        i = o[p]; k = a[i]; s = D[k][0]
        out[B[k] + (p - s)] = i
    return out

def CPR(a):
    n = len(a); cnt = {}; rho = []
    for x in a: rho.append(cnt.get(x, 0)); cnt[x] = cnt.get(x, 0) + 1
    f = [cnt.get(x, 0) for x in range(n+1)]
    return rho, f

def IS_via_CPR(a):
    n = len(a); rho, f = CPR(a)
    B = [0]*(n+2)
    for x in range(n+1): B[x+1] = B[x] + f[x]
    out = [None]*n
    for i in range(n): out[B[a[i]] + rho[i]] = i
    return out

def CPR_via_IS(a):
    n = len(a); p = stable_int_sort(a)
    rho = [None]*n; f = [0]*(n+1)
    j = 0
    while j < n:
        x = a[p[j]]; s = j
        while j < n and a[p[j]] == x: rho[p[j]] = j - s; j += 1
        f[x] = j - s
    return rho, f

for trial in range(3000):
    n = random.randint(1, 30)
    a = [random.randint(0, random.randint(0, n)) for _ in range(n)]
    ref = stable_int_sort(a)
    assert IS_via_SS(a) == ref
    assert IS_via_CPR(a) == ref
    assert IS_via_DS(a) == ref
    assert CPR_via_IS(a) == CPR(a)
    zs = random.sample(range((n+1)**2), n)
    assert [zs[i] for i in DS_via_IS(zs)] == sorted(zs)
print("K.1 reductions (IS<-SS, IS<-CPR, IS<-DS, CPR<-IS, DS<-IS): 3000 trials OK")

# ---- M.1 PAE identity ----
def pae(y, p):
    n = len(y)
    return sum(1 for i in range(n) for j in range(n) if y[j] > y[i] and p[j] <= p[i])

for trial in range(3000):
    n = random.randint(1, 25)
    G = random.randint(1, n)
    g = [random.randrange(G) for _ in range(n)]
    # compactify ids
    ids = sorted(set(g)); mp = {v: k for k, v in enumerate(ids)}; g = [mp[v] for v in g]
    G = len(ids)
    f = [g.count(h) for h in range(G)]
    B = [sum(f[:h]) for h in range(G)]
    q = [None]*n
    for h in range(G):
        pos = [i for i in range(n) if g[i] == h]
        labs = sorted(random.randint(0, f[h]-1) for _ in pos)
        for i, l in zip(pos, labs): q[i] = l
    y = [(g[i], i) for i in range(n)]
    p = [B[g[i]] + q[i] for i in range(n)]
    cells = {}
    for i in range(n): cells[(g[i], q[i])] = cells.get((g[i], q[i]), 0) + 1
    assert pae(y, p) == sum(c*(c-1)//2 for c in cells.values())
print("M.1 PAE = collision energy: 3000 trials OK")

# ---- N.1 expected energy exact for one group of frequency f ----
for fr in range(1, 12):
    tot = Fraction(0)
    for X in itertools.product([0, 1], repeat=fr):
        q = [sum(X[:r]) for r in range(fr)]
        cnt = {}
        for v in q: cnt[v] = cnt.get(v, 0) + 1
        tot += sum(c*(c-1)//2 for c in cnt.values())
    E = tot / 2**fr
    assert E == fr - 2 + Fraction(2, 2**fr), (fr, E)
    assert E < fr
print("N.1 E[energy] = f - 2 + 2^(1-f) exactly for f <= 11: OK")

# energy equals sum of run lengths R
for trial in range(2000):
    fr = random.randint(1, 30)
    X = [random.randint(0, 1) for _ in range(fr)]
    q = [sum(X[:r]) for r in range(fr)]
    cnt = {}
    for v in q: cnt[v] = cnt.get(v, 0) + 1
    E = sum(c*(c-1)//2 for c in cnt.values())
    R = 0
    for r in range(fr):
        d = 0
        while r + d + 1 <= fr - 1 and X[r + d] == 0: d += 1
        R += d
    assert E == R
print("N.1 energy = sum of capped zero-runs: OK")

# Monte Carlo: E <= 3n on adversarial sequences (one big group, many small)
worst = 0
for trial in range(200):
    n = random.choice([1000, 5000, 20000])
    mode = trial % 3
    if mode == 0: g = [0]*n
    elif mode == 1: g = [random.randrange(3) for _ in range(n)]
    else: g = [i % 50 for i in range(n)]
    cnt = {}; E = 0
    q = {}
    cellcount = {}
    for i in range(n):
        h = g[i]
        lab = q.get(h, 0)
        key = (h, lab)
        E += cellcount.get(key, 0)
        cellcount[key] = cellcount.get(key, 0) + 1
        q[h] = lab + random.randint(0, 1)
    worst = max(worst, E / n)
print("N.1 Monte Carlo: max E/n over 200 runs = %.3f (< 3)" % worst)

# ---- N.2 anchor-density bound: exhaustive over compositions ----
def compositions(f, parts):
    if parts == 1:
        yield (f,); return
    for c in range(f+1):
        for rest in compositions(f - c, parts - 1): yield (c,) + rest
for fr in range(1, 13):
    for k in range(0, 6):
        mn = min(sum(c*(c-1)//2 for c in comp) for comp in compositions(fr, k+1))
        assert Fraction(mn) >= Fraction(1, 2)*(Fraction(fr*fr, k+1) - fr), (fr, k, mn)
print("N.2 E >= (f^2/(k+1) - f)/2: exhaustive for f <= 12, k <= 5 OK")
