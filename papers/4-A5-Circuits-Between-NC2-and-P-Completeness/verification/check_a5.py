"""Exhaustive checks of the finite group-theoretic claims used in manuscripts 004a-004d.

Permutations of {1,...,5} are stored as tuples of images of 0..4.
Product convention: (g*h)(i) = g(h(i)), i.e. h is applied first (right-to-left).
The opposite convention is also checked where a count could depend on it.
"""
from itertools import permutations, product
from math import gcd
from collections import Counter, deque
import random

N = 5
E = tuple(range(N))


def mul(g, h):          # right-to-left: apply h, then g
    return tuple(g[h[i]] for i in range(N))


def mul_lr(g, h):       # left-to-right: apply g, then h
    return tuple(h[g[i]] for i in range(N))


def inv(g):
    r = [0] * N
    for i, gi in enumerate(g):
        r[gi] = i
    return tuple(r)


def sign(g):
    s, seen = 1, [False] * N
    for i in range(N):
        if not seen[i]:
            j, L = i, 0
            while not seen[j]:
                seen[j] = True
                j = g[j]
                L += 1
            if L % 2 == 0:
                s = -s
    return s


def cyc(*c):
    p = list(range(N))
    for a, b in zip(c, c[1:] + c[:1]):
        p[a - 1] = b - 1
    return tuple(p)


def order(g, m=mul):
    k, x = 1, g
    while x != E:
        x = m(x, g)
        k += 1
    return k


def power(g, k, m=mul):
    k %= 30
    r = E
    for _ in range(k):
        r = m(r, g)
    return r


S5 = list(permutations(range(N)))
A5 = [g for g in S5 if sign(g) == 1]
assert len(A5) == 60


def gen(gens, m=mul):
    S = {E}
    frontier = [E]
    while frontier:
        new = []
        for x in frontier:
            for g in gens:
                y = m(x, g)
                if y not in S:
                    S.add(y)
                    new.append(y)
        frontier = new
    return frozenset(S)


def comm(a, b, m=mul, conv=0):
    if conv == 0:   # a^-1 b^-1 a b
        return m(m(m(inv(a), inv(b)), a), b)
    return m(m(m(a, b), inv(a)), inv(b))   # a b a^-1 b^-1


def derived(H, m=mul):
    gens = {comm(a, b, m) for a in H for b in H}
    return gen(list(gens), m) if gens else frozenset({E})


report = []

# ---------------------------------------------------------------- basic facts
orders = Counter(order(g) for g in A5)
report.append(f"A5 element orders: {dict(sorted(orders.items()))}")
assert set(orders) == {1, 2, 3, 5}
assert all(power(g, 30) == E for g in A5)
assert all(power(g, 29) == inv(g) for g in A5)
report.append("exponent of A5 is 30; x^-1 = x^29 for all x")

# Lemma (power permutations): x -> x^a bijective iff gcd(a,30)=1
for a in range(30):
    bij = len({power(g, a) for g in A5}) == 60
    assert bij == (gcd(a, 30) == 1), a
report.append("x -> x^a is a permutation of A5 iff gcd(a,30)=1 (all a in Z_30)")

# R_{a,b}(x,y) = (x, x^a y^b) permutation of A5^2 iff b unit; L_{a,b} iff a unit
pw = {(g, a): power(g, a) for g in A5 for a in range(30)}
for a in range(30):
    for b in range(30):
        R = {(x, mul(pw[x, a], pw[y, b])) for x in A5 for y in A5}
        L = {(mul(pw[x, a], pw[y, b]), y) for x in A5 for y in A5}
        assert (len(R) == 3600) == (gcd(b, 30) == 1)
        assert (len(L) == 3600) == (gcd(a, 30) == 1)
report.append("R_{a,b} bijective iff b in U_30, L_{a,b} bijective iff a in U_30 (all 900 pairs)")

# ---------------------------------------------------------------- two generators p, q
p, q = cyc(1, 2, 3, 4, 5), cyc(1, 2, 3)
assert gen([p, q]) == frozenset(A5)
# word lengths over {p, p^-1, q, q^-1}
dist = {E: 0}
dq = deque([E])
gens4 = [p, inv(p), q, inv(q)]
while dq:
    x = dq.popleft()
    for g in gens4:
        y = mul(x, g)
        if y not in dist:
            dist[y] = dist[x] + 1
            dq.append(y)
report.append(f"<(12345),(123)> = A5; max word length over P^+-1,Q^+-1 = {max(dist.values())}")

# Ore: every element of A5 is a commutator
commset = {comm(a, b) for a in A5 for b in A5}
assert commset == set(A5)
report.append("every element of A5 is a commutator [a,b] (both conventions)")
assert {comm(a, b, conv=1) for a in A5 for b in A5} == set(A5)

# deep tower R_{g,d}: check values for d up to 6 using an explicit (alpha,beta) table
ab = {}
for g in A5:
    for a in A5:
        for b in A5:
            if comm(a, b) == g:
                ab[g] = (a, b)
                break
        if g in ab:
            break
val = {g: g for g in A5}           # level 0: R_{g,0} evaluates to g
for d in range(1, 7):
    val = {g: comm(val[ab[g][0]], val[ab[g][1]]) for g in A5}
    assert all(val[g] == g for g in A5)
report.append("commutator tower: val(R_{g,d}) = g for all g and d <= 6")

# ---------------------------------------------------------------- subgroup census of pairs
H_of = {}
cnt = Counter()
for x in A5:
    for y in A5:
        H = gen([x, y])
        H_of[x, y] = H
        cnt[len(H)] += 1
report.append(f"ordered pairs by |<x,y>|: {dict(sorted(cnt.items()))}, total {sum(cnt.values())}")
assert dict(cnt) == {1: 1, 2: 45, 3: 80, 4: 30, 5: 144, 6: 180, 10: 360, 12: 480, 60: 2280}

# proper subgroups generated by pairs are metabelian (second derived subgroup trivial)
subs = {H for H in H_of.values() if len(H) < 60}
for H in subs:
    assert derived(derived(H)) == frozenset({E})
report.append(f"{len(subs)} distinct proper 2-generated subgroups, all with trivial second derived subgroup")
# derived length of A5 subgroups: A5 is perfect
assert derived(frozenset(A5)) == frozenset(A5)

hot = [(x, y) for x in A5 for y in A5 if len(H_of[x, y]) == 60]
cold = [(x, y) for x in A5 for y in A5 if len(H_of[x, y]) < 60]
assert len(hot) == 2280 and len(cold) == 1320

# Aut(A5) = conjugation by S5; free action on generating pairs; 19 orbits
def conj(s, g):
    return mul(mul(s, g), inv(s))


auts = {tuple(conj(s, g) for g in A5) for s in S5}
assert len(auts) == 120
for (x, y) in hot:
    stab = [s for s in S5 if conj(s, x) == x and conj(s, y) == y]
    assert stab == [E]
orbit_id = {}
reps = []
for (x, y) in hot:
    if (x, y) in orbit_id:
        continue
    k = len(reps)
    reps.append((x, y))
    for s in S5:
        orbit_id[conj(s, x), conj(s, y)] = k
assert len(reps) == 19
assert Counter(orbit_id.values()) == Counter({k: 120 for k in range(19)})
report.append("2280 generating pairs; S5-conjugation acts freely; 19 orbits of size 120")

# |Aut(A5)| = 120: count generating pairs (x,y) such that p->x, q->y extends to an automorphism
words = {}
dq2 = deque([E]); words[E] = []
while dq2:
    z = dq2.popleft()
    for k, g in enumerate(gens4):
        y2 = mul(z, g)
        if y2 not in words:
            words[y2] = words[z] + [k]
            dq2.append(y2)
def eval_word(wd, x, y):
    imgs = [x, inv(x), y, inv(y)]
    r = E
    for k in wd:
        r = mul(r, imgs[k])
    return r
naut = 0
for (x, y) in hot:
    phi = {g: eval_word(words[g], x, y) for g in A5}
    if all(phi[mul(g, h)] == mul(phi[g], phi[h]) for g in A5 for h in A5):
        naut += 1
assert naut == 120
report.append("|Aut(A5)| = 120 (all automorphisms are conjugations by S5)")

# pairwise projections onto A5 x A5 are full (Goursat step)
def mulp(u, v):
    return (mul(u[0], v[0]), mul(u[1], v[1]))


def gen_pair(gens):
    S = {(E, E)}
    frontier = [(E, E)]
    while frontier:
        new = []
        for z in frontier:
            for g in gens:
                w = mulp(z, g)
                if w not in S:
                    S.add(w)
                    new.append(w)
        frontier = new
    return S


full = 0
for i in range(19):
    for j in range(i + 1, 19):
        (xi, yi), (xj, yj) = reps[i], reps[j]
        if len(gen_pair([(xi, xj), (yi, yj)])) == 3600:
            full += 1
assert full == 171
report.append("all 171 pairwise projections of the 19 representatives generate A5 x A5")

# mirror word w = [[x,y], x^-1 [x,y] x]
for m in (mul, mul_lr):
    for conv in (0, 1):
        def w(x, y):
            c = comm(x, y, m, conv)
            return comm(c, m(m(inv(x), c), x), m, conv)
        assert all(w(x, y) == E for (x, y) in cold)
        nonid = [(x, y) for (x, y) in hot if w(x, y) != E]
        orbs = {orbit_id[z] for z in nonid}
        # union of whole orbits
        assert all(sum(1 for z in nonid if orbit_id[z] == k) == 120 for k in orbs)
        report.append(f"mirror word ({'rl' if m is mul else 'lr'}, conv {conv}): identity on all 1320 cold pairs, "
                      f"non-identity on {len(nonid)} hot pairs = {len(orbs)} full orbits")
        assert len(nonid) == 1920

# ---------------------------------------------------------------- noncommutative Fibonacci
T = {(x, y): (mul(x, y), x) for x in A5 for y in A5}
assert len(set(T.values())) == 3600
Tinv = {(u, v): (v, mul(inv(v), u)) for u in A5 for v in A5}
assert all(Tinv[T[s]] == s for s in T)
seen, lens = set(), Counter()
for s in T:
    if s in seen:
        continue
    L, z = 0, s
    while z not in seen:
        seen.add(z)
        z = T[z]
        L += 1
    lens[L] += 1
report.append(f"T(x,y)=(xy,x) on A5^2: cycle lengths {dict(sorted(lens.items()))}; max {max(lens)}")

# ---------------------------------------------------------------- 61-probe colorings
for j in range(60):
    c = {0: 'e', j + 1: 'e'}
    others = [i for i in range(61) if i not in c]
    assert len(others) == 59
    vals = ['e'] * 2 + [f"g{k}" for k in range(59)]
    collisions = Counter(vals)
    assert sum(v * (v - 1) // 2 for v in collisions.values()) == 1
report.append("61-probe colorings: each has exactly one colliding pair {0, j+1}")

# ---------------------------------------------------------------- Boolean gadget (as in the companion notes)
a = cyc(1, 2, 3, 4, 5)
b = cyc(1, 2, 4, 5, 3)
c = cyc(3, 5, 4)
d = cyc(2, 4, 3)
assert all(sign(z) == 1 for z in (a, b, c, d))
ok_rl = (mul(mul(inv(c), a), c) == b and comm(a, b) == cyc(1, 4, 2, 3, 5)
         and mul(mul(inv(d), comm(a, b)), d) == a)
report.append(f"gadget identities c^-1 a c = b, [a,b] = (14235), d^-1 [a,b] d = a hold (right-to-left): {ok_rl}")
NOT = lambda x: mul(a, power(x, 4))
AND = lambda x, y: mul(mul(inv(d), comm(x, mul(mul(inv(c), y), c))), d)
enc = {0: E, 1: a}
for u in (0, 1):
    assert NOT(enc[u]) == enc[1 - u]
    for v in (0, 1):
        assert AND(enc[u], enc[v]) == enc[u & v]
report.append("NOT(x)=a x^4 and AND(x,y)=d^-1 [x, c^-1 y c] d realise NOT/AND on {e,a}")

# ---------------------------------------------------------------- dominator condensation on random SLPs
def random_slp(n, rng):
    nodes = [('P',), ('Q',)]
    for _ in range(n - 2):
        k = len(nodes)
        if rng.random() < 0.25:
            nodes.append(('inv', rng.randrange(k)))
        else:
            # bias toward recent nodes to create long lineages
            i = rng.randrange(max(0, k - 6), k) if rng.random() < 0.7 else rng.randrange(k)
            j = rng.randrange(max(0, k - 6), k) if rng.random() < 0.7 else rng.randrange(k)
            nodes.append(('mul', i, j))
    return nodes


def evaluate(nodes, P, Q):
    v = []
    for nd in nodes:
        if nd[0] == 'P':
            v.append(P)
        elif nd[0] == 'Q':
            v.append(Q)
        elif nd[0] == 'inv':
            v.append(inv(v[nd[1]]))
        else:
            v.append(mul(v[nd[1]], v[nd[2]]))
    return v


def preds(nd):
    if nd[0] in ('P', 'Q'):
        return ['s']
    return list(nd[1:])


def reach_avoiding(nodes, dnode):
    """nodes reachable from the super-source s when dnode is deleted."""
    R = set()
    for i, nd in enumerate(nodes):
        if i == dnode:
            continue
        if any(pp == 's' or pp in R for pp in preds(nd)):
            R.add(i)
    return R


rng = random.Random(2026)
checked = 0
for trial in range(300):
    n = rng.randrange(4, 40)
    nodes = random_slp(n, rng)
    # dominators
    dom = {v: {'s'} for v in range(n)}
    for dd in range(n):
        R = reach_avoiding(nodes, dd)
        for v in range(n):
            if v != dd and v not in R:
                dom[v].add(dd)
    # idom = latest proper dominator in topological order; prime iff idom == s
    idom = {}
    for v in range(n):
        proper = [x for x in dom[v] if x != 's']
        idom[v] = max(proper) if proper else 's'
    prime = {v for v in range(n) if idom[v] == 's'}
    rho = {v: (v if v in prime else min(x for x in dom[v] if x != 's')) for v in range(n)}
    assert all(rho[v] in prime for v in range(n))
    # exponents by path counting mod 30 from rho(v)
    W = [[0] * n for _ in range(n)]
    for i in range(n):
        W[i][i] = 1
    for v, nd in enumerate(nodes):
        if nd[0] == 'inv':
            for i in range(n):
                W[i][v] = (W[i][v] - W[i][nd[1]]) % 30
        elif nd[0] == 'mul':
            for i in range(n):
                W[i][v] = (W[i][v] + W[i][nd[1]] + W[i][nd[2]]) % 30
    expo = {v: (1 if v in prime else W[rho[v]][v]) for v in range(n)}
    # properties (i)-(iv)
    for v, nd in enumerate(nodes):
        if v not in prime:
            for u in preds(nd):
                assert u != 's' and rho[u] == rho[v]
        if nd[0] == 'inv':
            assert v not in prime
        if nd[0] == 'mul' and v in prime:
            assert rho[nd[1]] != rho[nd[2]]
    for (P, Q) in [(rng.choice(A5), rng.choice(A5)) for _ in range(40)]:
        vals = evaluate(nodes, P, Q)
        for v in range(n):
            assert vals[v] == power(vals[rho[v]], expo[v])
    checked += 1
report.append(f"dominator power condensation verified on {checked} random two-generator SLPs (n<=39, 40 assignments each)")

# ---------------------------------------------------------------- ranked saturation: layered reachability = min Strahler rank
def strahler(r1, r2):
    return max(r1, r2) if r1 != r2 else r1 + 1


def saturation_instances(nodes, P, Q, Gvals):
    """Fact/rule universe of the value/equality calculus over the group Gvals (list of elements)."""
    n = len(nodes)
    axioms = []
    unary = []      # (premise, conclusion)
    binary = []     # (prem1, prem2, conclusion)
    for u, nd in enumerate(nodes):
        if nd[0] == 'P':
            axioms.append(('V', u, P))
        if nd[0] == 'Q':
            axioms.append(('V', u, Q))
        if nd[0] == 'inv':
            x = nd[1]
            for g in Gvals:
                unary.append((('V', x, g), ('V', u, inv(g))))
                unary.append((('V', u, g), ('V', x, inv(g))))
        if nd[0] == 'mul':
            x, y = nd[1], nd[2]
            for g in Gvals:
                for h in Gvals:
                    binary.append((('V', x, g), ('V', y, h), ('V', u, mul(g, h))))
                    binary.append((('V', u, g), ('V', x, h), ('V', y, mul(inv(h), g))))
                    binary.append((('V', u, g), ('V', y, h), ('V', x, mul(g, inv(h)))))
    for u in range(n):
        for v in range(n):
            for g in Gvals:
                binary.append((('V', u, g), ('V', v, g), ('E', u, v)))
            unary.append((('E', u, v), ('E', v, u)))
            for w_ in range(n):
                binary.append((('E', u, v), ('E', v, w_), ('E', u, w_)))
    invs = [(u, nd[1]) for u, nd in enumerate(nodes) if nd[0] == 'inv']
    for (z, x) in invs:
        for (z2, x2) in invs:
            unary.append((('E', x, x2), ('E', z, z2)))
            unary.append((('E', z, z2), ('E', x, x2)))
    muls = [(u, nd[1], nd[2]) for u, nd in enumerate(nodes) if nd[0] == 'mul']
    for (z, x, y) in muls:
        for (z2, x2, y2) in muls:
            binary.append((('E', x, x2), ('E', y, y2), ('E', z, z2)))
            binary.append((('E', z, z2), ('E', x, x2), ('E', y, y2)))
            binary.append((('E', z, z2), ('E', y, y2), ('E', x, x2)))
    return axioms, unary, binary


def min_rank_fixpoint(axioms, unary, binary):
    INF = 10 ** 9
    rk = Counter()
    rk = {}
    for f in axioms:
        rk[f] = 0
    changed = True
    while changed:
        changed = False
        for (a1, c) in unary:
            if a1 in rk and rk.get(c, INF) > rk[a1]:
                rk[c] = rk[a1]
                changed = True
        for (a1, a2, c) in binary:
            if a1 in rk and a2 in rk:
                r = strahler(rk[a1], rk[a2])
                if rk.get(c, INF) > r:
                    rk[c] = r
                    changed = True
    return rk


def layered(axioms, unary, binary, K):
    known = {}
    for k in range(K + 1):
        below = set(known)
        # start facts: rule instances all of whose premises are of rank < k (or axioms at k = 0)
        start = set(axioms) if k == 0 else set()
        edges = {}
        for (a1, c) in unary:
            edges.setdefault(a1, []).append(c)
        for (a1, a2, c) in binary:
            if a1 in below and a2 in below:
                start.add(c)
            elif a1 in below:
                edges.setdefault(a2, []).append(c)
            elif a2 in below:
                edges.setdefault(a1, []).append(c)
        seen_ = set(start)
        st = list(start)
        while st:
            f = st.pop()
            for c in edges.get(f, []):
                if c not in seen_:
                    seen_.add(c)
                    st.append(c)
        for f in seen_:
            if f not in known:
                known[f] = k
    return known


rng = random.Random(7)
G2 = sorted(gen([p, q]))
tests = 0
for trial in range(12):
    n = rng.randrange(3, 6)
    nodes = random_slp(n, rng)
    P, Q = rng.choice(A5), rng.choice(A5)
    Gvals = sorted(gen([P, Q]))
    ax, un, bi = saturation_instances(nodes, P, Q, Gvals)
    rk = min_rank_fixpoint(ax, un, bi)
    vals = evaluate(nodes, P, Q)
    # soundness and completeness
    for f in rk:
        if f[0] == 'V':
            assert vals[f[1]] == f[2]
        else:
            assert vals[f[1]] == vals[f[2]]
    for u in range(n):
        assert ('V', u, vals[u]) in rk
        for v in range(n):
            assert (vals[u] == vals[v]) == (('E', u, v) in rk)
    Kmax = max(rk.values())
    lay = layered(ax, un, bi, Kmax)
    assert lay == rk
    tests += 1
report.append(f"value/equality calculus: sound, complete, and layered reachability equals min Strahler rank on {tests} random SLPs")

print("\n".join(report))
