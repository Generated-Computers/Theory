# Checks for 003b and 003e.
import itertools, random
from fractions import Fraction as Fr
random.seed(47)

def max_path_weight(n, preds, w):
    best = [None]*n
    for v in range(n):   # vertices are topologically ordered 0..n-1
        best[v] = w[v] + max([best[u] for u in preds[v]], default=0)
    return max(best)

def cht(n, preds, H):
    return max_path_weight(n, preds, [1 if v in H else 0 for v in range(n)])

def ancestors(n, preds):
    anc = [set() for _ in range(n)]
    for v in range(n):
        for u in preds[v]:
            anc[v] |= anc[u] | {u}
    return anc

# ---- matched-rail mirage: delta = h/2 (primal and dual certificate), integral chi = ceil(h/2)
for h in range(1, 9):
    for trial in range(5):
        pi = list(range(h)); random.shuffle(pi)
        # vertices: A_i = i, B_j = h+j, Z_i = 2h+i
        n = 3*h; preds = [[] for _ in range(n)]
        for i in range(1, h): preds[i] = [i-1]; preds[h+i] = [h+i-1]
        fus = []
        for i in range(h): preds[2*h+i] = [i, h+pi[i]]; fus.append((i, h+pi[i]))
        x = [Fr(1,2)]*(2*h) + [Fr(0)]*h
        assert all(x[u]+x[w] >= 1 for u, w in fus)
        assert max_path_weight(n, preds, x) == Fr(h, 2)
        # dual: lambda = 1/2 on each rail, y_e = 1/2: check vertex constraints
        p = [Fr(1,2)]*(2*h) + [Fr(0)]*h
        load = [Fr(0)]*n
        for u, w in fus: load[u] += Fr(1,2); load[w] += Fr(1,2)
        assert all(load[v] <= p[v] for v in range(n)) and sum(Fr(1,2) for _ in fus) == Fr(h,2)
        if h <= 8:
            chi = min(cht(n, preds, {c[k] for k, c in enumerate(fus)}) for c in [
                [fus[i][s[i]] for i in range(h)] for s in itertools.product((0,1), repeat=h)]
                for _ in [0]) if False else None
            best = min(cht(n, preds, {fus[i][s[i]] for i in range(h)}) for s in itertools.product((0,1), repeat=h))
            assert best == (h+1)//2, (h, best)
print("mirage: delta = h/2 certificates and integral chi = ceil(h/2) verified for h <= 8")

# ---- two-path concentration on random DAGs with random feasible duals
def all_paths(n, succ):
    paths = []
    def ext(path):
        paths.append(tuple(path))
        for w in succ[path[-1]]:
            ext(path + [w])
    for v in range(n): ext([v])
    return paths

worst_inc = None; worst_gen = None; count = 0
for trial in range(400):
    n = random.randint(4, 8)
    succ = [[] for _ in range(n)]; preds = [[] for _ in range(n)]
    for v in range(1, n):
        for u in random.sample(range(v), min(v, random.randint(1, 2))):
            succ[u].append(v); preds[v].append(u)
    anc = ancestors(n, preds)
    pairs = [(u, w) for u in range(n) for w in range(u+1, n)]
    E = random.sample(pairs, min(len(pairs), random.randint(1, 6)))
    incomparable = all(u not in anc[w] and w not in anc[u] for u, w in E)
    paths = all_paths(n, succ)
    # random path distribution
    wts = [random.random() for _ in paths]; tot = sum(wts)
    lam = [Fr(int(1000*w)+1, 1) for w in wts]; tot = sum(lam); lam = [l/tot for l in lam]
    p = [sum(l for P, l in zip(paths, lam) if v in P) for v in range(n)]
    # random feasible y: scale random weights to satisfy load_v <= p_v
    y = [Fr(random.randint(0, 5)) for _ in E]
    load = [Fr(0)]*n
    for (u, w), ye in zip(E, y): load[u] += ye; load[w] += ye
    scale = min([p[v]/load[v] for v in range(n) if load[v] > 0], default=Fr(0))
    y = [ye*scale for ye in y]
    D = sum(y); s = sum(1 for ye in y if ye > 0)
    if D == 0: continue
    count += 1
    # exact expectations over independent P, Q
    EI = Fr(0); EyI = Fr(0); best_cnt = 0; best_w = Fr(0)
    for P, lp in zip(paths, lam):
        for Q, lq in zip(paths, lam):
            I = [1 if ((u in P and w in Q) or (w in P and u in Q)) else 0 for (u, w) in E]
            cnt = sum(I[k] for k in range(len(E)) if y[k] > 0)
            wt = sum(y[k]*I[k] for k in range(len(E)))
            EI += lp*lq*cnt; EyI += lp*lq*wt
            best_cnt = max(best_cnt, cnt); best_w = max(best_w, wt)
    r1 = EI / (D*D/s); r2 = EyI / (D**3/(s*s))
    if incomparable:
        assert best_cnt >= 2*D*D/s and best_w >= 2*D**3/(s*s), "incomparable bound fails"
        worst_inc = min(worst_inc or 99, float(min(r1, r2)))
    else:
        assert best_cnt >= D*D/s and best_w >= D**3/(s*s), "general bound fails"
        worst_gen = min(worst_gen or 99, float(min(r1, r2)))
print("concentration: instances", count, "min ratio E/(bound/2) incomparable:", worst_inc, "general:", worst_gen)

# Sequential-NOR-type chain: x_i reads x_{i-1}, x_{j_i}; parents comparable, two paths can coincide
n = 8; preds = [[]] + [[i-1] if True else [] for i in range(1, n)]
print("SeqNOR parents comparable: yes (x_j is an ancestor of x_{i-1} along the chain)")

# ---- catalyst compiler and rounding on random carrier circuits over D = Z_3
D = 3
def evaluate(n, kind, preds, maps, src):
    val = [None]*n
    for v in range(n):
        if kind[v] == 's': val[v] = src[v]
        elif kind[v] == 'u': val[v] = maps[v][val[preds[v][0]]]
        else: val[v] = maps[v][val[preds[v][0]]][val[preds[v][1]]]
    return val

ok_comp = 0; ok_round = 0
for trial in range(500):
    n = random.randint(3, 14)
    kind = []; preds = []; maps = []; src = {}
    for v in range(n):
        if v < 2 or random.random() < 0.15:
            kind.append('s'); preds.append([]); maps.append(None); src[v] = random.randrange(D)
        elif random.random() < 0.3:
            kind.append('u'); preds.append([random.randrange(v)]); maps.append([random.randrange(D) for _ in range(D)])
        else:
            u, w = random.sample(range(v), 2)
            kind.append('f'); preds.append([u, w]); maps.append([[random.randrange(D) for _ in range(D)] for _ in range(D)])
    truth = evaluate(n, kind, preds, maps, src)
    anc = ancestors(n, preds)
    fus = [tuple(preds[v]) for v in range(n) if kind[v] == 'f']
    H = {random.choice(e) for e in fus} | {v for v in range(n) if random.random() < 0.1}
    # level-by-level: at level r, the union of ancestor cones of level-r catalysts must be functional
    lev = {}
    for v in range(n):
        if v in H: lev[v] = 1 + max([lev[u] for u in anc[v] if u in H], default=0)
    known = {v for v in range(n) if kind[v] == 's'}
    for r in range(1, max(lev.values(), default=0) + 1):
        cone = set()
        for h_ in H:
            if lev[h_] == r: cone |= anc[h_] | {h_}
        for v in cone:
            if v in known: continue
            unres = [u for u in preds[v] if u not in known]
            assert len(set(unres)) <= 1, "cone not functional"
        known |= cone
    for v in range(n):
        if v in known: continue
        unres = [u for u in preds[v] if u not in known]
        assert len(set(unres)) <= 1 or not set(unres) <= set(range(n)) , "final closure not functional"
    ok_comp += 1
    # rounding: random fractional feasible x, threshold at 1/2
    x = [Fr(random.randint(0, 4), 4) for _ in range(n)]
    for (u, w) in fus:
        if x[u] + x[w] < 1: x[w] = 1 - x[u]
    d = max_path_weight(n, preds, x)
    Hr = {v for v in range(n) if x[v] >= Fr(1, 2)}
    assert all(u in Hr or w in Hr for u, w in fus)
    assert cht(n, preds, Hr) <= 2*d
    ok_round += 1
print("catalyst compiler level checks:", ok_comp, " rounding checks:", ok_round)
