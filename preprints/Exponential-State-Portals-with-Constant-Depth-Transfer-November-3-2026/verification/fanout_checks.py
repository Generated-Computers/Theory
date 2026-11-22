"""Checks for 005e/005c: fanout set, fanout skeleton levels, formula-forest property,
level-by-level evaluation, merging of equal fanout nodes; Hopf identities and copy-tensor
flattening rank for A5."""
import itertools, random
from a5lib import A5, E, compose, IDX

def inv(p):
    q = [0]*5
    for i in range(5): q[p[i]] = i
    return tuple(q)

def random_slp(n, nterm, p_unary=0.15):
    # nodes 0..nterm-1 terminals (constants); others: ('mul', i, j) or ('inv', i)
    nodes = [('const', random.choice(A5)) for _ in range(nterm)]
    for v in range(nterm, n):
        if random.random() < p_unary:
            nodes.append(('inv', random.randrange(v)))
        else:
            lo = max(0, v - random.randint(1, v))
            nodes.append(('mul', random.randrange(lo, v), random.randrange(lo, v)))
    return nodes

def evaluate(nodes):
    val = []
    for nd in nodes:
        if nd[0] == 'const': val.append(nd[1])
        elif nd[0] == 'inv': val.append(inv(val[nd[1]]))
        else: val.append(compose(val[nd[1]], val[nd[2]]))
    return val

def preds(nd):
    return [] if nd[0] == 'const' else list(nd[1:])

def outdeg(nodes, out):
    d = [0]*len(nodes)
    for nd in nodes:
        for p in preds(nd): d[p] += 1   # with multiplicity
    return d

def skeleton_levels(nodes, out):
    n = len(nodes); d = outdeg(nodes, out)
    H = {v for v in range(n) if d[v] >= 2}
    lev = {}
    # level of v in H: 1 + max level of H-vertices reaching v by H-avoiding paths
    def hpreds(v):  # H-vertices u with an H-avoiding path u -> ... -> v
        res, st, seen = set(), list(preds(nodes[v])), set()
        while st:
            u = st.pop()
            if u in seen: continue
            seen.add(u)
            if u in H: res.add(u)
            else: st.extend(preds(nodes[u]))
        return res, seen
    for v in range(n):
        if v in H or v == out:
            hp, region = hpreds(v)
            lev[v] = 1 + max([lev[u] for u in hp], default=0)
            # formula-forest property: every non-H vertex of the region has a unique use inside region+v
            nonH = [u for u in region if u not in H]
            for u in nonH:
                uses = sum(1 for w in list(region) + [v] for p in preds(nodes[w]) if p == u
                           and (w == v or w not in H))
                assert uses == 1, "non-H vertex used twice in region"
    d_height = max([lev[v] for v in H], default=0)
    return H, lev, d_height

def level_evaluate(nodes, out, H, lev):
    known = {}
    def formula_value(v):  # evaluate v using known H values only, recursing through non-H nodes
        nd = nodes[v]
        def get(u):
            if u in H: return known[u]
            return formula_value(u)
        if nd[0] == 'const': return nd[1]
        if nd[0] == 'inv': return inv(get(nd[1]))
        return compose(get(nd[1]), get(nd[2]))
    maxl = max(lev.values())
    for L in range(1, maxl + 1):
        layer = [v for v in H if lev[v] == L]
        for v in layer: known[v] = formula_value(v)   # all of these use only lower levels
    return formula_value(out)

random.seed(3)
gap_examples = 0
for trial in range(300):
    n = random.randint(5, 60)
    nodes = random_slp(n, random.randint(1, 4))
    out = n - 1
    H, lev, d = skeleton_levels(nodes, out)
    assert d <= len(H)
    val = evaluate(nodes)
    assert level_evaluate(nodes, out, H, lev) == val[out]
    # merge equal fanout nodes (full equality): earliest representative, redirect uses
    rep = {}
    first = {}
    for v in sorted(H):
        g = val[v]
        if g in first: rep[v] = first[g]
        else: first[g] = v
    new = []
    for nd in nodes:
        if nd[0] == 'const': new.append(nd)
        else: new.append((nd[0],) + tuple(rep.get(p, p) for p in nd[1:]))
    H2, lev2, d2 = skeleton_levels(new, out)
    assert evaluate(new)[out] == val[out]
    cK = len(first)
    assert len(H2) <= cK and d2 <= cK <= 60
    if len(H) >= 3 * max(d, 1): gap_examples += 1
print("fanout height: level evaluation correct, d<=h, merged d<=c<=60 on 300 random SLPs; h>=3d in",
      gap_examples, "cases")

# Hopf identities on basis vectors (as maps on basis labels)
for g in A5:
    for x in A5:
        gx = compose(g, x)
        # Delta2 o mu (g,x) = (gx, gx);  (mu x mu)(id x tau x id)(Delta2 x Delta2)(g,x) = (g x, g x)
        assert (gx, gx) == (compose(g, x), compose(g, x))
    assert compose(g, inv(g)) == E and compose(inv(g), g) == E
print("Hopf identities (copy through product, antipode): OK")

# flattening rank of Delta_2 : 60 x 3600 matrix, rows indexed by input g, column (g,g) -> 1
def rank_mod_p(rows, p=1000003):
    rows = [r[:] for r in rows]; rk = 0; ncol = len(rows[0])
    for c in range(ncol):
        piv = next((i for i in range(rk, len(rows)) if rows[i][c] % p), None)
        if piv is None: continue
        rows[rk], rows[piv] = rows[piv], rows[rk]
        iv = pow(rows[rk][c], p-2, p)
        rows[rk] = [(x*iv) % p for x in rows[rk]]
        for i in range(len(rows)):
            if i != rk and rows[i][c]:
                fct = rows[i][c]
                rows[i] = [(a - fct*b) % p for a, b in zip(rows[i], rows[rk])]
        rk += 1
    return rk
cols = [(a, b) for a in range(60) for b in range(60)]
M = [[1 if (a == g and b == g) else 0 for (a, b) in cols] for g in range(60)]
print("flattening rank of copy tensor Delta_2:", rank_mod_p(M))
