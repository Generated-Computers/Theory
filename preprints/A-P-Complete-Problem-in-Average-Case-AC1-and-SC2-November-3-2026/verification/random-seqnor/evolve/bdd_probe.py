# How large are the exact cut-to-cut maps of an instance (NOTE.md §5j)? For a cut s, the live set
# L(s) = {p < s : some gate g >= s reads p} determines everything after s. Symbolic forward simulation
# from s, with the values in L(s) as BDD variables (larger positions on top), gives each later position
# as a function of L(s). At horizon h the map from cut s to cut s+h is the vector of functions for
# L(s+h); we report its shared BDD size, its support and whether it is constant (coalesced).
# Anchored doubling with BDDs must represent exactly such maps, so they decide whether a better
# representation could beat the width barrier: small maps for every horizon mean BDD doubling works.
# usage: python3 -I bdd_probe.py file.bin cut horizon1 horizon2 ...
import random, struct, sys

class BDD:
    def __init__(self):
        self.var, self.lo, self.hi = [None, None], [0, 1], [0, 1]   # ids 0, 1 terminals
        self.uniq, self.memo = {}, {}
    def mk(self, v, lo, hi):
        if lo == hi: return lo
        k = (v, lo, hi); r = self.uniq.get(k)
        if r is None:
            r = len(self.var); self.var.append(v); self.lo.append(lo); self.hi.append(hi); self.uniq[k] = r
        return r
    def top(self, f): return self.var[f] if f > 1 else 1 << 60     # smaller level = nearer the top
    def ite(self, f, g, h):
        if f == 1: return g
        if f == 0: return h
        if g == h: return g
        if g == 1 and h == 0: return f
        k = (f, g, h); r = self.memo.get(k)
        if r is not None: return r
        v = min(self.top(f), self.top(g), self.top(h))
        def cof(x, b):
            return (self.hi[x] if b else self.lo[x]) if x > 1 and self.var[x] == v else x
        r = self.mk(v, self.ite(cof(f, 0), cof(g, 0), cof(h, 0)), self.ite(cof(f, 1), cof(g, 1), cof(h, 1)))
        self.memo[k] = r
        return r
    def nor(self, a, b): return self.ite(a, 0, self.ite(b, 0, 1))
    def shared_size(self, roots):
        seen, stack = set(), [r for r in roots if r > 1]
        while stack:
            x = stack.pop()
            if x in seen: continue
            seen.add(x)
            for y in (self.lo[x], self.hi[x]):
                if y > 1: stack.append(y)
        return len(seen), len({self.var[x] for x in seen})

def load(path):
    with open(path, 'rb') as fh:
        n = struct.unpack('<i', fh.read(4))[0]
        return n, [0] + list(struct.unpack('<%di' % n, fh.read(4 * n)))

def live_sets(n, j):
    last = [0] * (n + 1)
    for g in range(1, n + 1):
        last[g - 1] = max(last[g - 1], g); last[j[g]] = max(last[j[g]], g)
    return last                                  # p is live at s iff p < s <= last[p]

def probe(n, j, s, horizons, node_cap=2_000_000, order='desc', seed=0):
    """order of the variables (live positions at s), top first: 'desc' (larger positions on top),
    'asc', 'random', or 'reader' (by the first gate >= s that reads the position)"""
    last = live_sets(n, j)
    L = sorted((p for p in range(s) if last[p] >= s), reverse=True)
    if order == 'asc': L.reverse()
    elif order == 'random': random.Random(seed).shuffle(L)
    elif order == 'reader':
        first = {}
        for g in range(s, n + 1):
            for p in (g - 1, j[g]):
                if p < s and p not in first: first[p] = g
        L.sort(key=lambda p: first.get(p, n + 1))
    B = BDD(); val = {}
    for lev, p in enumerate(L): val[p] = B.mk(lev, 0, 1)
    out = []; hs = sorted(horizons); hi = 0
    for i in range(s, min(n, s + hs[-1]) + 1):
        a, b = val[i - 1], val[j[i]]
        val[i] = B.nor(a, b)
        if len(B.var) > node_cap: out.append((i - s, None, None, None, len(L))); return out
        while hi < len(hs) and i - s + 1 == hs[hi]:
            c = i + 1                            # cut after position i
            Lc = [p for p in val if p < c and last[p] >= c]
            roots = [val[p] for p in Lc]
            size, supp = B.shared_size(roots)
            const = all(r <= 1 for r in roots)
            out.append((hs[hi], size, supp, const, len(Lc)))
            hi += 1
        # drop dead positions to save memory
        for p in (i - 1, j[i]):
            if p in val and last[p] <= i and p not in L: del val[p]
        if len(B.memo) > 4_000_000: B.memo.clear()
    return out

if __name__ == '__main__':
    n, j = load(sys.argv[1]); s = int(sys.argv[2]); hs = [int(x) for x in sys.argv[3:]]
    print('%s n=%d cut=%d' % (sys.argv[1].split('/')[-1], n, s))
    for h, size, supp, const, w in probe(n, j, s, hs):
        print('   horizon %6d: live width %4d, map size %s, support %s%s' % (h, w, size, supp, ', constant' if const else ''))
