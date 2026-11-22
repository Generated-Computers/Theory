# Checks for 003a: M-exchange of network boundary functions; crossbar; NAND lattice.
import itertools, random
random.seed(44)
INF = float('inf')

def boundary_function(nT, nI, arcs, d):
    """arcs: list of (tail, head, lo, hi, cost). vertices 0..nT-1 terminals, rest internal.
    returns dict b(tuple) -> min cost."""
    n = nT + nI
    phi = {}
    ranges = [range(lo, hi + 1) for (_, _, lo, hi, _) in arcs]
    for f in itertools.product(*ranges):
        div = [0] * n
        cost = 0
        for (t, h, lo, hi, c), fa in zip(arcs, f):
            div[t] += fa; div[h] -= fa; cost += c * fa
        if tuple(div[nT:]) != tuple(d):
            continue
        b = tuple(div[:nT])
        if cost < phi.get(b, INF):
            phi[b] = cost
    return phi

def check_mexchange(phi):
    dom = list(phi)
    for b in dom:
        for bp in dom:
            diff = [x - y for x, y in zip(b, bp)]
            for i in range(len(b)):
                if diff[i] <= 0: continue
                ok = False
                for j in range(len(b)):
                    if diff[j] >= 0: continue
                    b1 = list(b); b1[i] -= 1; b1[j] += 1
                    b2 = list(bp); b2[i] += 1; b2[j] -= 1
                    v = phi.get(tuple(b1), INF) + phi.get(tuple(b2), INF)
                    if phi[b] + phi[bp] >= v:
                        ok = True; break
                if not ok:
                    return False
    return True

def has_comparator(phi):
    # terminals 0=Xin 1=Yin 2=Xout 3=Yout
    def beta(x, y): return (x, y, -x, -y)
    vals = [phi.get(beta(x, y), INF) for x, y in [(0, 0), (1, 0), (0, 1), (1, 1)]]
    if INF in vals: return False
    c = vals[0]
    if not (vals[3] == c and vals[1] == c + 1 and vals[2] == c + 1): return False
    cr1 = phi.get((0, 1, -1, 0), INF); cr2 = phi.get((1, 0, 0, -1), INF)
    return cr1 > c and cr2 > c

viol = 0; comp = 0; tested = 0
for trial in range(1500):
    nT = 4; nI = random.randint(0, 2); n = nT + nI
    m = random.randint(3, 7)
    arcs = []
    for _ in range(m):
        t, h = random.sample(range(n), 2)
        lo = random.choice([0, 0, 0, -1]); hi = lo + random.choice([1, 1, 2])
        arcs.append((t, h, lo, hi, random.randint(-2, 2)))
    d = [random.choice([0, 0, 1, -1]) for _ in range(nI)]
    phi = boundary_function(nT, nI, arcs, d)
    if not phi: continue
    tested += 1
    if not check_mexchange(phi): viol += 1
    if has_comparator(phi): comp += 1
print("random networks tested:", tested, "M-exchange violations:", viol, "comparator signatures:", comp)

# crossbar: Xin->Xout cost1, Yin->Yout cost1, Xin->Yout cost0, Yin->Xout cost0
arcs = [(0, 2, 0, 1, 1), (1, 3, 0, 1, 1), (0, 3, 0, 1, 0), (1, 2, 0, 1, 0)]
phi = boundary_function(4, 0, arcs, [])
table = {(x, y): phi.get((x, y, -x, -y)) for x in (0, 1) for y in (0, 1)}
print("crossbar table |x-y|:", table, "crossed states:", phi.get((0, 1, -1, 0)), phi.get((1, 0, 0, -1)),
      "M-exchange:", check_mexchange(phi))

# NAND relation and coordinate complementations
R = {(x, y, 1 - (x & y)) for x in (0, 1) for y in (0, 1)}
def is_lattice(S):
    return all(tuple(a & b for a, b in zip(s, t)) in S and tuple(a | b for a, b in zip(s, t)) in S for s in S for t in S)
res = []
for flip in itertools.product((0, 1), repeat=3):
    S = {tuple(v ^ f for v, f in zip(s, flip)) for s in R}
    res.append(is_lattice(S))
print("NAND lattice under any of the 8 complementations:", any(res))
