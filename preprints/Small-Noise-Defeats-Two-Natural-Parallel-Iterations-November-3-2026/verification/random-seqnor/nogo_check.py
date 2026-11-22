# Machine checks for the lower bound on the two iterations (paper Theorem "no-go", NOTE.md §5i).
# 1. On smoothed random block bases, the true non-deep sets are contained in the over-approximations
#    built from gate types (Lemma "zones" for the relevance-pruned depth D and for the Kleene-prefix
#    depth d), block by block, with the refined killer type of resampled gates.
# 2. The series sum_m N_u(m) = (2-u)/(1-u)^2.
# 3. The invariant boxes: (1/6, 1/22) at eps = 1/10 for D, (4/17, 1/12) at eps = 3/20 for d, with
#    margin at least 1/250 + (correction for delta <= 1/1000), in exact arithmetic.
# 4. The parameters ell, m, B and the failure bound.
# usage: python3 -I nogo_check.py
import math, random
from fractions import Fraction as Fr

def instance(n0, B, M, h0, eps, rng, tail=7):
    """random block base: block 0 = [0, n0), block b >= 1 = [n0+(b-1)B, n0+bB); then smoothing"""
    n = n0 + M * B + tail - 1
    j = [0] * (n + 1); pi = [0] * (n + 1); base = [0] * (n + 1)
    for i in range(1, n + 1):
        if i < n0 or i >= n0 + M * B: base[i] = max(i - 2, 0)
        else:
            b = (i - n0) // B + 1
            s_prev = n0 - B if b == 1 else n0 + (b - 2) * B
            base[i] = s_prev + rng.randint(h0, B - 2)
        if i >= 2 and rng.random() < eps: pi[i] = 1; j[i] = rng.randint(0, i - 1)
        else: j[i] = base[i]
    return n, j, pi, base

def depths(j, n):
    x = [0] * (n + 1); x[0] = 1
    for i in range(1, n + 1): x[i] = int(x[i - 1] == 0 and x[j[i]] == 0)
    D = [0] * (n + 1); d = [0] * (n + 1); D[1] = d[1] = 1
    for i in range(2, n + 1):
        nt = j[i] != i - 1; rel = x[i - 1] == 0; res = nt and x[j[i]] == 1
        c = 1 + d[j[i]]
        d[i] = c if res else (max(d[i - 1], c) if nt else d[i - 1])
        c = 1 + D[j[i]]
        if res and rel: D[i] = c
        elif res: D[i] = min(D[i - 1], c)
        elif rel and nt: D[i] = max(D[i - 1], c)
        else: D[i] = D[i - 1]
    return x, D, d

def no_two_clean(U, lo, hi):            # gates lo..hi (offsets): no two consecutive with U = 0
    return all(U[q] or U[q + 1] for q in range(lo, hi))

def check(n0, B, M, h0, eps, seed):
    rng = random.Random(seed)
    n, j, pi, base = instance(n0, B, M, h0, eps, rng)
    x, D, d = depths(j, n)
    viol = 0
    for kind, depth in (("D", D), ("d", d)):
        Sh, S1h = set(), set()          # block 0: level 0, nothing is non-deep
        for b in range(0, M):           # build block b+1 from block b
            s = n0 + b * B
            U = [0] * B; K = [0] * B
            for o in range(B):
                g = s + o
                if pi[g]:
                    U[o] = 1; K[o] = int(j[g] >= s or x[j[g]] == 1)
                else:
                    U[o] = int(base[g] in Sh); K[o] = int(base[g] in S1h)
            nS, nS1 = set(), set()
            for o in range(h0, B - 1):
                p = s + o
                if kind == "D":
                    Bp = no_two_clean(U, 0, o)
                    A = A1 = False
                    for uo in range(o, -1, -1):
                        if K[uo] and (uo == o or U[uo + 1]) and no_two_clean(U, uo + 1, o):
                            A = True
                            if uo < o: A1 = True; break
                else:
                    Bp = all(U[q] for q in range(0, o + 1))
                    A = A1 = False
                    for uo in range(o, -1, -1):
                        if K[uo] and all(U[q] for q in range(uo + 1, o + 1)):
                            A = True
                            if uo < o: A1 = True; break
                if A or Bp: nS.add(p)
                if U[o] and (A1 or Bp): nS1.add(p)
                t = b                    # level of block b; block b+1 must reach t + 1
                if depth[p] <= t and p not in nS: viol += 1
                if depth[p] <= t and x[p] == 1 and p not in nS1: viol += 1
            Sh, S1h = nS, nS1
    return viol, max(D), max(d)

tot = 0; runs = 0
for seed in range(150):
    for eps in (0.02, 0.05, 0.1, 0.15, 0.3, 0.6):
        v, mD, md = check(150, 40, 30, 5, eps, seed)
        tot += v; runs += 1
assert tot == 0
print("1. inclusions hold for D and d on %d smoothed random block bases (30 blocks of 40)" % runs)

def N(m, u):
    a, b = Fr(1), Fr(0)
    for _ in range(m): a, b = u * (a + b), (1 - u) * a
    return a + b
for u in (Fr(1, 10), Fr(1, 4), Fr(7, 20)):
    partial = sum(N(m, u) for m in range(200))
    closed = (2 - u) / (1 - u) ** 2
    assert closed - partial < Fr(1, 10 ** 30) and partial <= closed
print("2. sum_m N_u(m) = (2-u)/(1-u)^2 checked at u = 1/10, 1/4, 7/20")

def maps(kind, s, s1, eps, delta):
    u = eps + (1 - eps) * s; k = eps * (Fr(1, 2) + delta) + (1 - eps) * s1
    if kind == "D":
        f = 1 + u * (2 - u) / (1 - u) ** 2
        return k * f, k * u * f, u, k
    return k / (1 - u), k * u / (1 - u), u, k
eta, delta = Fr(1, 250), Fr(1, 1000)
for kind, eps, s, s1 in (("D", Fr(1, 10), Fr(1, 6), Fr(1, 22)), ("d", Fr(3, 20), Fr(4, 17), Fr(1, 12))):
    F0, G0, u, k = maps(kind, s, s1, eps, 0)
    F, G, _, _ = maps(kind, s, s1, eps, delta)
    print("3. %s: eps = %s, box (%s, %s), u* = %s, k* = %s + O(delta); margins at delta = 0: %s, %s;"
          " at delta = 1/1000: %.5f, %.5f" % (kind, eps, s, s1, u, k, s - F0, s1 - G0, float(s - F), float(s1 - G)))
    assert F + eta <= s and G + eta <= s1
    # monotone in eps on [0, eps]: check on a grid
    for e in range(0, 101):
        ee = eps * e / 100
        Fe, Ge, _, _ = maps(kind, s, s1, ee, delta)
        assert Fe <= F and Ge <= G
    if kind == "D": assert u == Fr(1, 4) and F0 == Fr(16, 99) and s - F0 == Fr(1, 198) and s1 - G0 == Fr(1, 198)
    else: assert u == Fr(7, 20) and k == Fr(7, 48)

# 4. parameters: ell = 2*ceil(6 ln n), m = ceil(3 ln n / eta^2), B = (ell+1)(m+2)
for u in (Fr(1, 4), Fr(7, 20)):
    q = float(u * (2 - u))
    assert 6 * math.log(1 / q) >= 3          # q^{ceil(6 ln n)} <= n^{-3}
    print("4. u* = %s: u(2-u) = %.4f, exponent 6 ln(1/(u(2-u))) = %.3f >= 3" % (u, q, 6 * math.log(1 / q)))
assert 2 * eta ** 2 * 187500 == 6                 # 2 eta^2 m >= 6 ln n
# bounds used in the proof for n >= 1e13 (ln n >= 29.9; n / ln^2 n is increasing there)
L13 = math.log(1e13)
assert L13 >= 29.9 and 1e13 / L13 ** 2 >= 1e10
assert 2 * (6 * L13 + 1) + 1 <= 12.2 * L13        # ell + 1 <= 12.2 ln n (worst case is the smallest n)
assert 187500 * L13 + 3 <= 187501 * L13           # m + 2 <= 187501 ln n
assert 12.2 * 187501 <= 2.29e6                     # B <= 2.29e6 ln^2 n
assert (2.29e6 + 1) / (1e10 / 2 - 1) <= 1e-3       # delta = (B+1)/n0 <= 1e-3, using n/ln^2 n >= 1e10
assert 1 / (2 * 2.29e6) - 1 / 1e10 >= 1 / 5e6      # n/(2B) - 1 >= n/(5e6 ln^2 n) when n/ln^2 n >= 1e10
for n in (10 ** 13, 10 ** 15, 10 ** 20, 10 ** 30):
    L = math.log(n); ell = 2 * math.ceil(6 * L); m = math.ceil(3 * L / float(eta) ** 2); B = (ell + 1) * (m + 2)
    n0 = n // 2; M = (n + 1 - n0) // B
    fail = M * (B * n ** -3.0 + 2 * (ell + 1) * n ** -6.0)
    print("   n = 1e%d: ell = %d, m = %d, B = %.3e = %.0f ln^2 n, (B+1)/n0 = %.1e, rounds >= M = %.3e, failure <= %.1e"
          % (round(math.log10(n)), ell, m, B, B / L ** 2, (B + 1) / n0, M, fail))
    assert fail <= 1 / n and (B + 1) / n0 <= 1e-3 and M >= n / (5e6 * L ** 2)

# 5. where the proof stops: the least fixed point of (sigma, sigma1) -> (mu, mu1) disappears
def lfp(kind, eps, half):
    s = s1 = 0.0
    for _ in range(20000):
        if eps + (1 - eps) * s >= 0.999: return None
        u = eps + (1 - eps) * s; k = eps * (0.5 if half else 1.0) + (1 - eps) * s1
        if kind == "D": f = 1 + u * (2 - u) / (1 - u) ** 2; a, b = k * f, k * u * f
        else: a, b = k / (1 - u), k * u / (1 - u)
        if a >= 1: return None
        s, s1 = a, b
    return s
def limit(kind, half):
    lo, hi = 0.0, 1.0
    for _ in range(40):
        mid = (lo + hi) / 2
        r = lfp(kind, mid, half)
        if r is None or r > 0.99: hi = mid
        else: lo = mid
    return lo
lims = {(k, h): limit(k, h) for k in ("D", "d") for h in (True, False)}
print("5. limits of the map: D %.4f (%.4f without the factor 1/2), d %.4f (%.4f)"
      % (lims["D", True], lims["D", False], lims["d", True], lims["d", False]))
assert 0.107 < lims["D", True] < 0.109 and 0.160 < lims["d", True] < 0.162
assert 0.065 < lims["D", False] < 0.067 and 0.096 < lims["d", False] < 0.098
print("all checks passed")
