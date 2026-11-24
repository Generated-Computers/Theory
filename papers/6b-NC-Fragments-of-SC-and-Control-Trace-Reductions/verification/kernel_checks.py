"""Checks for 005f: (1) balanced ladders D_{r,w}; (2) control-observability closure and
payload erasure on a toy affine history kernel over GF(p)."""
import random
P = 101

# ---------- (1) ladders ----------
def ladder_ranks(r, w):
    rank = {(0, j): 0 for j in range(w)}
    edges = 0
    for k in range(1, r+1):
        for j in range(w):
            a, b = rank[(k-1, j)], rank[(k-1, (j+1) % w)]
            rank[(k, j)] = max(a, b) if a != b else a + 1
            edges += 2
    return rank, edges
for r in range(1, 12):
    for w in range(2, 9):
        rank, edges = ladder_ranks(r, w)
        assert edges == 2*r*w and len(rank) == (r+1)*w
        assert all(rank[(k, j)] == k for k in range(r+1) for j in range(w))
print("ladders: (r+1)w vertices, 2rw edges, level k has rank k: OK")

# ---------- (2) kernel ----------
def matvec(A, x): return [sum(a*b for a, b in zip(row, x)) % P for row in A]
def dot(c, x): return sum(a*b for a, b in zip(c, x)) % P
def rowmat(l, A):  # row vector times matrix
    d = len(A); return [sum(l[i]*A[i][j] for i in range(d)) % P for j in range(d)]

def rref(rows, d):
    rows = [r[:] for r in rows if any(x % P for x in r)]; out = []; col = 0
    rows = [list(r) for r in rows]
    piv_cols = []
    rk = 0
    for c in range(d):
        piv = next((i for i in range(rk, len(rows)) if rows[i][c] % P), None)
        if piv is None: continue
        rows[rk], rows[piv] = rows[piv], rows[rk]
        iv = pow(rows[rk][c], P-2, P); rows[rk] = [(x*iv) % P for x in rows[rk]]
        for i in range(len(rows)):
            if i != rk and rows[i][c]:
                f = rows[i][c]; rows[i] = [(a-f*b) % P for a, b in zip(rows[i], rows[rk])]
        piv_cols.append(c); rk += 1
    return rows[:rk], piv_cols

def nullspace(rows, d):
    R, piv = rref(rows, d)
    free = [c for c in range(d) if c not in piv]
    basis = []
    for fcol in free:
        v = [0]*d; v[fcol] = 1
        for i, pc in enumerate(piv): v[pc] = (-R[i][fcol]) % P
        basis.append(v)
    return basis

class Kernel:
    def __init__(s, d, nq):
        s.d, s.nq = d, nq
        rnd = lambda: [random.randrange(P) for _ in range(d)]
        s.cp, s.cz, s.cw = rnd(), rnd(), rnd()
        s.u = rnd()
        s.A = {(q, b): [rnd() for _ in range(d)] for q in range(nq) for b in (0, 1)}
        # make some A sparse so that closures are proper subspaces
        for key in s.A:
            for i in range(d):
                for j in range(d):
                    if random.random() < 0.5: s.A[key][i][j] = 0
        s.a = {(q, b): rnd() for q in range(nq) for b in (0, 1)}
        s.delta = {(q, b): random.randrange(nq) for q in range(nq) for b in (0, 1)}
    def run(s, q0, x0, H0, t0, t1, trace=None):
        """run steps t0+1..t1; H0 dict addr->word with addresses < m+t0+1"""
        q, x, H = q0, x0[:], dict(H0); tr = []
        for t in range(t0+1, t1+1):
            p = dot(s.cp, x) % (s.m + t)
            b = 1 if dot(s.cz, x) < P // 2 else 0
            h = H[p]
            H[s.m + t] = dot(s.cw, x)
            A, a = s.A[(q, b)], s.a[(q, b)]
            xn = [(v + s.u[i]*h + a[i]) % P for i, v in enumerate(matvec(A, x))]
            tr.append((p, b, q)); q = s.delta[(q, b)]; x = xn
        return tr, q, x, H

random.seed(11)
tests = 0; neg_diff = 0
for trial in range(400):
    d = random.randint(2, 4)
    K = Kernel(d, random.randint(1, 3)); K.m = random.randint(1, 4)
    N = random.randint(6, 30)
    H0 = {i: random.randrange(P) for i in range(K.m + 1)}
    x0 = [random.randrange(P) for _ in range(d)]
    # full run, recording states
    states = [(0, x0[:], dict(H0))]
    q, x, H = 0, x0[:], dict(H0)
    full = []
    for t in range(1, N+1):
        tr, q, x, H = K.run(q, x, H, t-1, t)
        full += tr; states.append((q, x[:], dict(H)))
    a = random.randint(0, N-2); b = N
    # least closure on I=(a,b] for the exact trace
    L = {b: []}
    demanded = set()
    for t in range(b, a, -1):
        p_t, b_t, q_tm1 = full[t-1]
        A = K.A[(q_tm1, b_t)]
        rows = [K.cp, K.cz] + [rowmat(l, A) for l in L[t]]
        # is cell written at step t demanded?  reads t' in (t,b] with p_{t'} = m+t and L_{t'} u != 0
        for tp in range(t+1, b+1):
            if full[tp-1][0] == K.m + t and any(dot(l, K.u) for l in L[tp]):
                rows.append(K.cw); demanded.add(t); break
        L[t-1], _ = rref(rows, d)
    # pick a time t0 in [a, b) and build X'
    t0 = random.randint(a, b-1)
    q0, xt0, Ht0 = states[t0]
    ker = nullspace(L[t0], d) if L[t0] else [[1 if i == j else 0 for i in range(d)] for j in range(d)]
    w = [0]*d
    for v in ker:
        c = random.randrange(P); w = [(wi + c*vi) % P for wi, vi in zip(w, v)]
    x1 = [(xi + wi) % P for xi, wi in zip(xt0, w)]
    H1 = dict(Ht0)
    for s in range(a+1, t0+1):  # internal cells written in (a, t0]
        live = any(full[tp-1][0] == K.m + s and any(dot(l, K.u) for l in L[tp]) for tp in range(t0+1, b+1))
        if not live: H1[K.m + s] = random.randrange(P)
    tr0, *_ = K.run(q0, xt0, Ht0, t0, b)
    tr1, *_ = K.run(q0, x1, H1, t0, b)
    assert tr0 == tr1, trial
    tests += 1
    # negative control: perturb outside the kernel
    if L[t0]:
        x2 = [(xi + random.randrange(1, P)) % P for xi in xt0]
        tr2, *_ = K.run(q0, x2, Ht0, t0, b)
        if tr2 != tr0: neg_diff += 1
print("payload erasure: identical address/branch/control traces in", tests, "random tests")
print("negative control (perturbation outside kernel changed the trace):", neg_diff, "cases")
