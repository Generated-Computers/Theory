import itertools, math, random, sys

def trace(j):
    n = len(j)
    x = [1]
    for i in range(1, n+1):
        a, b = x[i-1], x[j[i-1]]
        x.append(1 if (a == 0 and b == 0) else 0)
    return x

def core(j):
    n = len(j); J = [None] + list(j)
    B = [i for i in range(1, n+1) if 1 <= J[i] <= i-2 and J[i-1] != 0]
    H = [h for h in range(1, n) if J[h] != 0 and 1 <= J[h+1] <= h-1]
    assert [b-1 for b in B] == H
    rank = {b: k+1 for k, b in enumerate(B)}
    # pointer doubling
    P = list(range(n+1)); par = [0]*(n+1); lab = [None]*(n+1)
    lab[0] = ('c', 1)
    for q in range(1, n+1):
        if J[q] == 0: lab[q] = ('c', 0)
        elif q in rank: lab[q] = ('v', rank[q])
        elif J[q] == q-1: P[q] = q-1; par[q] = 1
        else:
            assert J[q-1] == 0 and 1 <= J[q] <= q-2
            P[q] = J[q]; par[q] = 1
    T = math.ceil(math.log2(n+1))
    for _ in range(T):
        par = [par[q] ^ par[P[q]] for q in range(n+1)]
        P = [P[P[q]] for q in range(n+1)]
    delta = []
    for q in range(n+1):
        r = P[q]; assert lab[r] is not None
        t, v = lab[r]
        delta.append(('c', v ^ par[q]) if t == 'c' else ('v', v, par[q]))
    return B, H, delta

def ev(d, z):
    return d[1] if d[0] == 'c' else z[d[1]-1] ^ d[2]

def nor(a, b): return 1 if a == 0 and b == 0 else 0

def block(B, j, delta, g):
    J = [None] + list(j); m = len(B)
    L = [delta[b-1] for b in B]; R = [delta[J[b]] for b in B]
    for k in range(m):
        for d in (L[k], R[k]):
            if d[0] == 'v': assert d[1] <= k  # earlier index (1-based < k+1)
    r = m; T = math.ceil(r/g) if r > 0 else 0
    beta = [0]*(T*g)
    for s in range(T):
        a = s*g; valid = []
        for alpha in itertools.product((0,1), repeat=g):
            zeta = beta[:a] + list(alpha) + [0]*(len(beta)-a-g)
            ok = True
            for t in range(g):
                k = a+t
                if k < m:
                    if alpha[t] != nor(ev(L[k], zeta), ev(R[k], zeta)): ok = False
                elif alpha[t] != 0: ok = False
            if ok: valid.append(alpha)
        assert len(valid) == 1, (j, g, s, valid)
        beta[a:a+g] = list(valid[0])
    return beta[:m]

def residual_block(j, g):
    # 006e: residual evaluator with gamma on H, deferred equations at H
    n = len(j); J = [None] + list(j)
    H = [h for h in range(1, n) if J[h] != 0 and 1 <= J[h+1] <= h-1]
    b = len(H); Hr = {h: k for k, h in enumerate(H)}
    def Y(gam):
        y = [1]
        for q in range(1, n+1):
            if q in Hr: y.append(gam[Hr[q]])
            else: y.append(nor(y[q-1], y[J[q]]))
        return y
    T = math.ceil(b/g) if b > 0 else 0
    beta = [0]*(T*g)
    for s in range(T):
        a = s*g; valid = []
        for alpha in itertools.product((0,1), repeat=g):
            gam = beta[:a] + list(alpha) + [0]*(len(beta)-a-g)
            y = Y(gam[:b] + [0]*0)
            ok = True
            for t in range(g):
                k = a+t
                if k < b:
                    h = H[k]
                    if alpha[t] != nor(y[h-1], y[J[h]]): ok = False
                elif alpha[t] != 0: ok = False
            if ok: valid.append(alpha)
        assert len(valid) == 1
        beta[a:a+g] = list(valid[0])
    return Y(beta[:b])

NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 7
count = 0
for n in range(1, NMAX+1):
    for j in itertools.product(*[range(i) for i in range(1, n+1)]):
        x = trace(j); B, H, delta = core(j)
        z = [x[b] for b in B]
        for q in range(n+1): assert ev(delta[q], z) == x[q]
        gs = sorted(set([1, 2, 3, math.ceil(math.log2(n+1)), n]))
        for g in gs:
            assert block(B, j, delta, g) == z
            assert residual_block(j, g) == x
        count += 1
print("parent arrays checked:", count)

# universality embedding
def embed(inputs, gates):
    t = len(inputs); J = {1: 0}; Rep = {}
    for i, a in enumerate(inputs, start=1):
        s, r = 2*i, 2*i+1; J[s] = 0; J[r] = 1 if a else 0; Rep[('a', i)] = r
    for i, (u, v) in enumerate(gates, start=1):
        s = 2*t + 4*i - 2
        J[s] = 0; J[s+1] = Rep[u]; J[s+2] = s+1; J[s+3] = Rep[v]; Rep[('w', i)] = s+3
    n = 1 + 2*t + 4*len(gates)
    return [J[i] for i in range(1, n+1)], Rep

random.seed(1)
trials = 0
for _ in range(3000):
    t = random.randint(1, 5); G = random.randint(1, 12)
    inputs = [random.randint(0, 1) for _ in range(t)]
    gates = []
    for i in range(1, G+1):
        pool = [('a', k) for k in range(1, t+1)] + [('w', k) for k in range(1, i)]
        gates.append((random.choice(pool), random.choice(pool)))
    val = {('a', k): inputs[k-1] for k in range(1, t+1)}
    for i, (u, v) in enumerate(gates, start=1): val[('w', i)] = nor(val[u], val[v])
    j, Rep = embed(inputs, gates)
    assert len(j) == 1 + 2*t + 4*G
    x = trace(j)
    for key, q in Rep.items(): assert x[q] == val[key]
    B, H, delta = core(j)
    assert B == [Rep[('w', i)] for i in range(1, G+1)]
    J = [None] + j
    def dsc(key):
        return ('c', inputs[key[1]-1]) if key[0] == 'a' else ('v', key[1], 0)
    for i, (u, v) in enumerate(gates, start=1):
        b = B[i-1]
        assert delta[b-1] == dsc(u) and delta[J[b]] == dsc(v)
    trials += 1
print("random circuits embedded:", trials)
