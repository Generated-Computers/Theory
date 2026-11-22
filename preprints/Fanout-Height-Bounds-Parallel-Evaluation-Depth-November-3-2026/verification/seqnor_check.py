"""005e: for Sequential NOR (x0=1, x_i = NOR(x_{i-1}, x_{j_i})), fanout set = set of parents and
fanout-skeleton height d equals h = |H|."""
import random
random.seed(2)
for trial in range(2000):
    n = random.randint(1, 40)
    j = [None] + [random.randrange(i) for i in range(1, n+1)]
    preds = {0: []}
    for i in range(1, n+1): preds[i] = [i-1, j[i]]
    outdeg = [0]*(n+1)
    for i in range(1, n+1):
        for p in preds[i]: outdeg[p] += 1
    H = {v for v in range(n+1) if outdeg[v] >= 2}
    assert H == set(j[1:]), (H, j)
    # skeleton levels
    lev = {}
    def hpreds(v):
        res, st, seen = set(), list(preds[v]), set()
        while st:
            u = st.pop()
            if u in seen: continue
            seen.add(u)
            if u in H: res.add(u)
            else: st.extend(preds[u])
        return res
    for v in range(n+1):
        if v in H:
            lev[v] = 1 + max([lev[u] for u in hpreds(v)], default=0)
    d = max(lev.values(), default=0)
    assert d == len(H)
print("Sequential NOR: H = set of parents and d = h on 2000 random parent arrays: OK")
