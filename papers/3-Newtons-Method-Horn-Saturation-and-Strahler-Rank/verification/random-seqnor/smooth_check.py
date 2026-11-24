# Machine checks for the smoothed-instance section (paper Section 9, NOTE.md §5c).
# 1. The gadgets N(a,b) and M(a,b,c) compute NOR and MAJ for every incoming chain value.
# 2. The constants of Theorem 9.5: q_0..q_3 at beta = 1/10, eps = 1/1000, and 10 e q3 < 0.38.
# 3. An unsmoothed embedding is exact (eps = 0) on random NOR circuits.
# 4. Remark 9.12: 0.0034 passes the old tail criterion with tolerance 1/6, depth 8 (see section 6 for the sup).
# 5. The layout-dependent 6-gate MAJ gadget (a, a, c, k+1, b, k), valid when c = k-1.
# 6. Lemma 9.6, Theorem 9.7 and Corollary 9.9 (noise 1/64): gadget densities, constants at theta = 1/6, depth 10,
#    m >= 130 log2 s; exactness of the post-order compiler with 6-gate MAJ nodes; noisy runs at 1/64
#    with the majority readout; and the limits quoted in Remark 9.12.
# usage: python3 -I smooth_check.py
import itertools, math, random

def run_gadget(ptrs, k, ext):          # ext: dict position -> value (0,1 and inputs); k = first gadget index
    vals = dict(ext); y = vals[k - 1]
    for off, p in enumerate(ptrs):
        y = int(not (y or vals[p])); vals[k + off] = y
    return y

K = 100                                 # first gadget gate; inputs at 10,11,12; chain value at K-1
for g, a, b, c in itertools.product((0, 1), repeat=4):
    ext = {0: 1, 1: 0, 10: a, 11: b, 12: c, K - 1: g}
    assert run_gadget([0, 10, 1, 11], K, ext) == int(not (a or b))
    assert run_gadget([0, 10, 1, 11, 11, K + 1, 12, K + 3], K, ext) == int(a + b + c >= 2)
print("gadgets N and M verified for all 16 (garbage, a, b, c)")

phi = lambda q: 3 * q * q - 2 * q ** 3
eps, beta = 1 / 1000, 1 / 10
q = 1 - (1 - eps) ** 4 * (1 - beta) ** 2; qs = [q]
for _ in range(3):
    q = 1 - (1 - eps) ** 8 * (1 - phi(q)); qs.append(q)
ub = [4 * eps + 2 * beta]
for _ in range(3): ub.append(8 * eps + phi(ub[-1]))
print("exact q_l:", ["%.6f" % v for v in qs], " upper bounds used:", ["%.5f" % v for v in ub])
assert all(a <= b + 1e-15 for a, b in zip(qs, ub))
assert ub[0] <= 0.204 + 1e-12 and ub[1] <= 0.11587 and ub[2] <= 0.04517 and ub[3] <= 0.01394
assert 10 * math.e * 0.01394 < 0.38
assert all(phi(x / 1000) <= phi((x + 1) / 1000) for x in range(1000))   # phi increasing on [0,1]
print("q3 <= 0.01394, 10 e q3 = %.4f < 0.38: Theorem 9.5 constants pass" % (10 * math.e * 0.01394))

def compile_and_eval(s, m, h, rng):
    gu, gv, val = [None], [None], [None]
    for t in range(1, s + 1):
        choice = lambda: rng.choice(['c0', 'c1'] + list(range(1, t)))
        gu.append(choice()); gv.append(choice())
        v = lambda u: 0 if u == 'c0' else 1 if u == 'c1' else val[u]
        val.append(int(not (v(gu[t]) or v(gv[t]))))
    j = [None, 0]; out = {}
    def o(u, r): return 1 if u == 'c0' else 0 if u == 'c1' else out[(u, r)]
    def emit(p): j.append(p); return len(j) - 1
    def tree(t, lev):
        if lev == 0:
            a, b = o(gu[t], rng.randrange(m)), o(gv[t], rng.randrange(m))
            for p in (0, a, 1, b): last = emit(p)
            return last
        a, b, c = tree(t, lev - 1), tree(t, lev - 1), tree(t, lev - 1)
        k = len(j)
        for p in (0, a, 1, b, b, k + 1, c, k + 3): last = emit(p)
        return last
    for t in range(1, s + 1):
        for l in range(m): out[(t, l)] = tree(t, h)
    n = len(j) - 1
    assert n == 1 + s * m * (8 * 3 ** h - 4)
    x = [1] + [0] * n
    for i in range(1, n + 1): x[i] = int(not (x[i - 1] or x[j[i]]))
    return all(x[out[(t, l)]] == val[t] for t in range(1, s + 1) for l in range(m)) and x[n] == val[s]
rng = random.Random(1)
assert all(compile_and_eval(rng.randrange(2, 30), rng.randrange(1, 6), rng.randrange(0, 4), rng) for _ in range(200))
print("eps = 0 embedding exact on 200 random NOR circuits (s < 30, m < 6, h < 4)")

def reaches(eps, th, hmax=12):
    q = 2 * th + 4 * eps
    for h in range(1, hmax + 1):
        q = 8 * eps + phi(q)
        if q <= th / (2 * math.e): return h
    return None
assert reaches(0.0034, 1 / 6, 12) is not None and reaches(1 / 1000, 1 / 10, 3) == 3
print("Remark 9.12: eps = 0.0034 passes with theta = 1/6, h =", reaches(0.0034, 1 / 6, 12))
for a, b, c in itertools.product((0, 1), repeat=3):
    ext = {0: 1, 1: 0, 10: a, 11: b, K - 1: c}
    assert run_gadget([10, 10, K - 1, K + 1, 11, K], K, ext) == int(a + b + c >= 2)
print("6-gate MAJ with c = k-1 verified")

# 6. Lemma 9.6 / Theorem 9.7: noise 1/64.
KL = lambda a, b: a * math.log(a / b) + (1 - a) * math.log((1 - a) / (1 - b))
for a, b, c in itertools.product((0, 1), repeat=3):          # unhit gadgets are >= 1/4 ones
    ext = {0: 1, 1: 0, 10: a, 11: b, K - 1: c}
    vals = dict(ext); y = c; ones = 0
    for off, pp in enumerate([10, 10, K - 1, K + 1, 11, K]):
        y = int(not (y or vals[pp])); vals[K + off] = y; ones += y
    assert ones >= 2, (a, b, c)
    vals = {0: 1, 1: 0, 10: a, 11: b}; y = c; ones = 0
    for off, pp in enumerate([0, 10, 1, 11]):
        y = int(not (y or vals[pp])); vals[K + off] = y; ones += y
    assert ones >= 1
assert KL(1 / 30, 1 / 64) >= 0.0077 and 400 * 0.0077 >= 3                 # Lemma 9.6 tail
assert all(0.2 * g - 1.9 >= 0.19 * g for g in range(500, 5000))
e, th = 1 / 64, 1 / 6
wN, wM = 3 * 0.81 + 0.501, 6 * 0.81
assert abs(wN - 2.931) < 1e-12 and abs(wM - 4.86) < 1e-12
q = 1 - (1 - wN * e) * (1 - th) ** 2; q6 = [q]
for _ in range(10):
    q = 1 - (1 - wM * e) * (1 - phi(q)); q6.append(q)
print("Thm 9.7 q_l:", ["%.5f" % v for v in q6])
assert q6[-1] <= 0.1161 and KL(th, 0.1161) >= 0.0111 and 130 * 0.0111 / math.log(2) > 2
assert 0.05 - 2 * 0.0011 - 1e-6 >= 0.047 and 1e4 * 0.047 ** 2 / 2 >= 11       # Cor 9.9
assert 4 * 3 ** 10 + 6 * (3 ** 10 - 1) // 2 == 413340
for sm in (256, 2 ** 10, 2 ** 20, 2 ** 40):                                 # padding: n + 1 <= 1e6 s m
    P = math.ceil(100 * math.log(1e7 * sm)) + 125
    assert 1 + 4 * P + 413340 * sm + 1 <= 1e6 * sm and 4 * P >= 400 * math.log(1e7 * sm) + 500
print("Lemma 9.6 / Thm 9.7 / Cor 9.9 constants pass: q_10 <= 0.1161, D(1/6||0.1161) = %.5f" % KL(th, 0.1161))

# Remark 9.12: old tail criterion (linearised Step 3, q_L <= theta/(2e), theta >= 1/10).
def old_ok(eps, th, L):
    q = 4 * eps + 2 * th
    for _ in range(L): q = 8 * eps + phi(q)
    return q <= th / (2 * math.e)
assert old_ok(1 / 250, 1 / 5, 12)
def sup_old(thmax):
    a, b = 0.001, 0.02
    for _ in range(40):
        c = (a + b) / 2
        ok = any(old_ok(c, i / 1000, L) for i in range(100, int(thmax * 1000) + 1, 2) for L in range(1, 30))
        a, b = (c, b) if ok else (a, c)
    return a
so6, so = sup_old(1 / 6), sup_old(0.45)
print("Remark 9.12: old criterion reaches %.5f with theta <= 1/6 and %.5f in general" % (so6, so))
assert 0.0034 < so6 < 0.0036 and 0.0041 < so < 0.0043
def feasible_w(eps, L=60):
    for i in range(1, 450):
        th = i / 1000; q = 1 - (1 - wN * eps) * (1 - th) ** 2
        for _ in range(L): q = 1 - (1 - wM * eps) * (1 - phi(q))
        if q < th: return True
    return False
a, b = 0.01, 0.05
for _ in range(40):
    c = (a + b) / 2; a, b = (c, b) if feasible_w(c) else (a, c)
print("Remark 9.12: harm-weighted analysis with deep cells reaches eps ~ %.4f" % a)
assert 0.0195 < a < 0.021 and KL(1 / 30, 0.021) > 0

def compile6(s, m, h, rng, eps=0.0):
    gu, gv, val = [None], [None], [None]
    for t in range(1, s + 1):
        choice = lambda: rng.choice(['c0', 'c1'] + list(range(1, t)))
        gu.append(choice()); gv.append(choice())
        v = lambda u: 0 if u == 'c0' else 1 if u == 'c1' else val[u]
        val.append(int(not (v(gu[t]) or v(gv[t]))))
    j = [None, 0]; out = {}
    def o(u, r): return 1 if u == 'c0' else 0 if u == 'c1' else out[(u, r)]
    def emit(p): j.append(p); return len(j) - 1
    def tree(t, lev):
        if lev == 0:
            a, b = o(gu[t], rng.randrange(m)), o(gv[t], rng.randrange(m))
            for p in (0, a, 1, b): last = emit(p)
            return last
        a, b, c = tree(t, lev - 1), tree(t, lev - 1), tree(t, lev - 1)
        k = len(j); assert c == k - 1
        for p in (a, a, c, k + 1, b, k): last = emit(p)
        return last
    for t in range(1, s + 1):
        for l in range(m): out[(t, l)] = tree(t, h)
    n = len(j) - 1
    jj = [j[0], 0] + [rng.randrange(i) if rng.random() < eps else j[i] for i in range(2, n + 1)]
    x = [1] + [0] * n
    for i in range(1, n + 1): x[i] = int(not (x[i - 1] or x[jj[i]]))
    bad = [sum(x[out[(t, l)]] != val[t] for l in range(m)) / m for t in range(1, s + 1)]
    return bad, bad[-1] < 0.5
rng = random.Random(2)
assert all(all(b == 0 for b in compile6(rng.randrange(2, 30), rng.randrange(1, 6), rng.randrange(0, 4), rng)[0]) for _ in range(200))
print("eps = 0 post-order compiler with 6-gate MAJ exact on 200 random NOR circuits")
worst, wrong = 0.0, 0
for trial in range(20):
    bad, ok = compile6(40, 24, 4, rng, eps=1 / 64)
    worst = max(worst, max(bad)); wrong += (not ok)
print("eps = 1/64, depth-4 cells, m = 24, 20 random circuits with s = 40: worst bundle fraction bad = %.3f, wrong majorities = %d" % (worst, wrong))

# Remark 9.12: limits when every hit gadget counts as failed (feasible: some theta with q_L < theta).
def feasible(eps, gM, L=60):
    for i in range(1, 500):
        th = i / 1000; q = 1 - (1 - eps) ** 4 * (1 - th) ** 2
        for _ in range(L): q = 1 - (1 - eps) ** gM * (1 - phi(q))
        if q < th: return True
    return False
def limit(gM):
    a, b = 0.001, 0.2
    for _ in range(40):
        c = (a + b) / 2
        a, b = (c, b) if feasible(c, gM) else (a, c)
    return a
l6, l8 = limit(6), limit(8)
print("Remark 9.12: counting every hit, deep cells reach eps ~ %.4f with M' (6 gates) and ~ %.4f with M (8 gates)" % (l6, l8))
assert 0.0165 < l6 < 0.0175 and 0.0125 < l8 < 0.0135
# Remark 9.12: the hits-only fallback at 1/64 (depth 30, tolerance 0.175, m >= 260 log2 s).
q = 1 - (1 - 1 / 64) ** 4 * (1 - 0.175) ** 2
for _ in range(30): q = 1 - (1 - 1 / 64) ** 6 * (1 - phi(q))
print("Remark 9.12: hits-only at 1/64, depth 30: q_30 = %.5f, D(0.175||q) = %.5f" % (q, KL(0.175, q)))
assert q < 0.175 and 260 * KL(0.175, q) / math.log(2) > 2
# Old tail criterion at the supremum needs depth ~20 (Remark 9.12).
assert not any(old_ok(0.0042, i / 1000, 12) for i in range(100, 451)) and any(old_ok(0.0042, i / 1000, L) for i in range(100, 451) for L in range(18, 24))
print("all checks passed")
