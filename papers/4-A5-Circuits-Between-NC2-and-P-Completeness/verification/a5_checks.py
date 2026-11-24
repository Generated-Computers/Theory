"""Checks for 005b (hypergraph realization, star barrier), 005c (full-capacity portal),
005d (A5 side-premise star).  Pure Python; A5 realised as even permutations of {0..4}."""
import itertools, random

def compose(p, q):  # (p*q)(i) = p(q(i))  -- right-to-left
    return tuple(p[q[i]] for i in range(5))

def parity(p):
    s, seen = 0, [False]*5
    for i in range(5):
        if not seen[i]:
            j, L = i, 0
            while not seen[j]:
                seen[j] = True; j = p[j]; L += 1
            s += L - 1
    return s % 2

A5 = [p for p in itertools.permutations(range(5)) if parity(p) == 0]
assert len(A5) == 60
E = tuple(range(5))
IDX = {g: i for i, g in enumerate(A5)}

# ---- 61-probe selector (as functions; terms exist by Maurer-Rhodes) ----
random.seed(1)
nonid = [g for g in A5 if g != E]
colorings = []
for j in range(60):
    perm = nonid[:]
    random.shuffle(perm)
    c = [None]*61
    c[0] = E; c[j+1] = E
    it = iter(perm)
    for i in range(61):
        if c[i] is None:
            c[i] = next(it)
    colorings.append(c)
def f(i, g):
    return colorings[IDX[g]][i]

def collision(vals):
    pairs = [(a, b) for a in range(len(vals)) for b in range(a+1, len(vals)) if vals[a] == vals[b]]
    return pairs

for g in A5:
    vals = [f(i, g) for i in range(61)]
    pr = collision(vals)
    assert pr == [(0, IDX[g]+1)], pr
print("selector: every g has exactly one collision {0, j+1}: OK")

# ---- hypergraph realization: essential support of block e is exactly e ----
def block(e, h):
    a = E
    for i in sorted(e):
        a = compose(a, h[i])
    return tuple(collision([f(j, a) for j in range(61)])[0])

def essential_support(e, t, trials=200):
    ess = set()
    for i in range(t):
        for _ in range(trials):
            h = [random.choice(A5) for _ in range(t)]
            h2 = list(h); h2[i] = random.choice(A5)
            if block(e, h) != block(e, h2):
                ess.add(i); break
    return ess

for trial in range(30):
    t = random.randint(2, 6)
    e = set(random.sample(range(t), random.randint(1, t)))
    ess = essential_support(e, t)
    # anchors outside e: exhaustive check that block does not depend on them
    for i in set(range(t)) - e:
        for _ in range(50):
            h = [random.choice(A5) for _ in range(t)]
            for x in A5:
                h2 = list(h); h2[i] = x
                assert block(e, h) == block(e, h2)
    assert ess == e, (e, ess)
print("hypergraph realization: essential support == e on 30 random hyperedges: OK")

# exhaustive bijectivity of x -> L x R
for L in random.sample(A5, 10):
    for R in random.sample(A5, 10):
        assert len({compose(compose(L, x), R) for x in A5}) == 60
print("x -> LxR bijective: OK")

# ---- star barrier: with h1 fixed, block i collision ranges over all 60 pairs ----
for h1 in A5:
    s = {block({0, 1}, [h1, hi]) for hi in A5}
    assert len(s) == 60
print("star barrier (i): for each fixed h1 the collision of block i takes 60 values: OK")

# ---- 005c: M(x,y) = e if x = e else y ; image of (y_1..y_t) -> (M(x,y_i)) ----
def M(x, y):
    return E if x == E else y
t = 2
for x in A5:
    img = {tuple(M(x, y) for y in ys) for ys in itertools.product(A5, repeat=t)}
    assert len(img) == (1 if x == E else 60**t)
print("full-capacity portal / hard-coefficient switch (t=2): OK")

# ---- 005d: A5 side-premise star via predicate-complete equality ----
S = set(random.sample(A5, 30))
a_, b_ = A5[1], A5[2]
def U(g): return a_ if g in S else b_
def V(g): return a_
pats = set()
for x in random.sample(A5, 5):
    xp = x  # A = E(x,x') true
    for hs in itertools.product(random.sample(A5, 6), repeat=3):
        B = tuple(U(h) == V(h) for h in hs)
        C = tuple(compose(x, U(h)) == compose(xp, V(h)) for h in hs)
        assert B == C
        pats.add(C)
print("side-premise star in A5: C-pattern equals B-pattern; patterns realised:", len(pats), "of 8")
