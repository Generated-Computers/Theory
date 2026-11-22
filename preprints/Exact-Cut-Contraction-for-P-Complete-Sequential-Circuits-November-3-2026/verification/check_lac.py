# Checks for Section on trace-resolved RSM -> LAC -> indexed recurrence, and elimination rounds
import random
random.seed(3)
M = 10**9 + 7

# ---- LAC -> indexed recurrence (2 stages per gate) ----
for trial in range(2000):
    N = random.randint(1, 40)
    # z_0 = 0 (constant gate), z_i = a z_f + b z_h + c
    gates = [None] + [(random.randrange(M), random.randrange(i), random.randrange(M), random.randrange(i), random.randrange(M)) for i in range(1, N+1)]
    z = [0]*(N+1)
    for i in range(1, N+1):
        a, f, b, h, c = gates[i]; z[i] = (a*z[f] + b*z[h] + c) % M
    # indexed: y_0 = z_0 = 0; phi(j) = 2j
    y = [0]*(2*N+1)
    for i in range(1, N+1):
        a, f, b, h, c = gates[i]
        # y_{2i-1} = 0*y_{2i-2} + a*y_{2f} + c ; y_{2i} = 1*y_{2i-1} + b*y_{2h} + 0
        assert 2*f < 2*i - 1 and 2*h < 2*i
        y[2*i-1] = (0*y[2*i-2] + a*y[2*f] + c) % M
        y[2*i] = (1*y[2*i-1] + b*y[2*h]) % M
    assert all(y[2*i] == z[i] for i in range(N+1))
print("LAC -> indexed recurrence: 2000 trials OK")

# ---- trace-resolved RSM -> LAC ----
# registers r0..r(c); step: push old r2; if read: r0 := s[r1] (else r0 unchanged);
# r_i (i>=1) := const | r_a + r_b | r_a - r_b | r_a (copy) of OLD registers (as chosen by control state)
def run_rsm(c, inp, prog, steps):
    R = [0]*(c+1); stack = list(inp); trace = []
    hist = [R[:]]
    q = 0
    for t in range(steps):
        assign, nxt = prog[q]
        old = R[:]
        stack.append(old[2])
        new = old[:]
        if old[1] >= 0 and old[1] < len(stack) - 1:  # read an existing cell (not the one just pushed)
            new[0] = stack[old[1]]; addr = old[1]
        else:
            addr = None
        for i in range(1, c+1):
            kind, x, y = assign[i]
            if kind == 'const': new[i] = x
            elif kind == 'add': new[i] = old[x] + old[y]
            elif kind == 'sub': new[i] = old[x] - old[y]
            else: new[i] = old[x]
        q = nxt[1 if old[3] <= 0 else 0]
        trace.append((assign, addr))
        R = new; hist.append(R[:])
    return hist, trace

def lac_from_trace(c, inp, trace):
    # build scalar LAC with gates (a, f, b, h, cst) over Z; gate ids: coordinate (t,i)
    gates = [(0, 0, 0, 0, 0)]  # gate 0 = constant 0
    gid = {}
    for i in range(c+1):   # initial registers = 0
        gates.append((0, 0, 0, 0, 0)); gid[(0, i)] = len(gates)-1
    k = len(inp)
    for t, (assign, addr) in enumerate(trace, start=1):
        for i in range(c+1):
            if i == 0:
                if addr is None: g = (1, gid[(t-1, 0)], 0, 0, 0)
                elif addr < k: g = (0, 0, 0, 0, inp[addr])          # input cell: known constant
                else:
                    u = addr - k + 1    # cell pushed at step u holds r2 before step u = X_{u-1}[2]
                    g = (1, gid[(u-1, 2)], 0, 0, 0)
            else:
                kind, x, y = assign[i]
                if kind == 'const': g = (0, 0, 0, 0, x)
                elif kind == 'add': g = (1, gid[(t-1, x)], 1, gid[(t-1, y)], 0)
                elif kind == 'sub': g = (1, gid[(t-1, x)], -1, gid[(t-1, y)], 0)
                else: g = (1, gid[(t-1, x)], 0, 0, 0)
            gates.append(g); gid[(t, i)] = len(gates)-1
    z = [0]*len(gates)
    for j in range(1, len(gates)):
        a, f, b, h, cs = gates[j]
        assert f < j and h < j
        z[j] = a*z[f] + b*z[h] + cs
    return z, gid, len(gates)

for trial in range(500):
    c = random.randint(3, 5)
    nq = random.randint(1, 5)
    prog = []
    for _ in range(nq):
        assign = [None] + [random.choice([('const', random.randint(-3, 5), 0), ('add', random.randint(0, c), random.randint(0, c)),
                                           ('sub', random.randint(0, c), random.randint(0, c)), ('copy', random.randint(0, c), 0)]) for _ in range(c)]
        prog.append((assign, (random.randrange(nq), random.randrange(nq))))
    inp = [random.randint(-5, 5) for _ in range(random.randint(1, 6))]
    steps = random.randint(1, 30)
    hist, trace = run_rsm(c, inp, prog, steps)
    z, gid, size = lac_from_trace(c, inp, trace)
    assert all(z[gid[(t, i)]] == hist[t][i] for t in range(steps+1) for i in range(c+1))
    assert size <= 1 + (c+1)*(steps+1)
print("trace-resolved RSM -> LAC (exact over Z): 500 random programs OK")

# ---- nilpotent inverse identity: (I-A) prod (I + A^{2^j}) = I ----
def matmul(X, Y, n):
    return [[sum(X[i][k]*Y[k][j] for k in range(n)) % M for j in range(n)] for i in range(n)]
for trial in range(50):
    n = random.randint(1, 9)
    A = [[random.randrange(M) if j < i else 0 for j in range(n)] for i in range(n)]
    I = [[1 if i == j else 0 for j in range(n)] for i in range(n)]
    P = I; Ap = A; k = 0
    while (1 << k) < n:
        P = matmul(P, [[(I[i][j] + Ap[i][j]) % M for j in range(n)] for i in range(n)], n)
        Ap = matmul(Ap, Ap, n); k += 1
    ImA = [[(I[i][j] - A[i][j]) % M for j in range(n)] for i in range(n)]
    assert matmul(ImA, P, n) == I
print("(I-A)^{-1} = prod (I + A^{2^j}) for strictly lower-triangular A: OK")

# ---- elimination rounds ----
for trial in range(1000):
    n = random.randint(1, 25)
    cst = [random.randrange(M) for _ in range(n)]
    In = [[(random.randrange(v), random.randrange(M)) for _ in range(random.randint(0, min(3, v)))] for v in range(n)]
    x = [0]*n
    for v in range(n): x[v] = (cst[v] + sum(a*x[u] for u, a in In[v])) % M
    V = set(range(n)); inn = {v: list(In[v]) for v in V}; cc = {v: cst[v] for v in V}
    records = []
    rounds = 0
    while any(inn[v] for v in V):
        out = {v: [] for v in V}
        for w in V:
            for u, a in inn[w]: out[u].append(w)
        # random independent set among vertices with edges
        order = list(V); random.shuffle(order); S = set()
        for v in order:
            nb = {u for u, _ in inn[v]} | set(out[v])
            if not (nb & S) and v not in nb: S.add(v)
        rec = {v: (cc[v], list(inn[v])) for v in S}
        records.append(rec)
        newinn = {}; newc = {}
        for w in V - S:
            lst = []; cw = cc[w]
            for u, a in inn[w]:
                if u in S:
                    cw = (cw + a*cc[u]) % M
                    lst += [(u2, a*a2 % M) for u2, a2 in inn[u]]
                else: lst.append((u, a))
            newinn[w] = lst; newc[w] = cw
        V = V - S; inn = newinn; cc = newc; rounds += 1
        assert all(u in V for w in V for u, _ in inn[w])
    val = {v: cc[v] for v in V}
    for rec in reversed(records):
        for v, (c0, lst) in rec.items():
            val[v] = (c0 + sum(a*val[u] for u, a in lst)) % M
    assert all(val[v] == x[v] for v in range(n))
print("elimination rounds (forward fill / reverse reconstruction): 1000 trials OK")
