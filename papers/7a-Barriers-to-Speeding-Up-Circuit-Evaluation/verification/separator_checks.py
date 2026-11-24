"""Checks for 005a: dyadic congestion of constant-lag edges, the dyadic-to-chronological frontier
bound, and the call count of the online separator recursion."""
import random, math

def build(lo, hi, nodes, depth=0):
    v = len(nodes); nodes.append([lo, hi, None, None, depth])
    if lo < hi:
        mid = (lo + hi) // 2
        nodes[v][2] = build(lo, mid, nodes, depth+1)
        nodes[v][3] = build(mid+1, hi, nodes, depth+1)
    return v

def assign(nodes, s, t):
    v = 0
    while True:
        lo, hi, l, r, _ = nodes[v]
        mid = (lo + hi) // 2
        if t <= mid: v = l
        elif s > mid: v = r
        else: return v

random.seed(5)
for N in [7, 16, 33, 100, 257, 1000]:
    nodes = []; build(1, N, nodes)
    height = max(nd[4] for nd in nodes)
    assert height == math.ceil(math.log2(N))
    for c in range(1, 6):
        cnt = {}
        for s in range(1, N - c + 1):
            v = assign(nodes, s, s + c); cnt[v] = cnt.get(v, 0) + 1
        assert max(cnt.values()) <= c
print("constant-lag edges (s,s+c): at most c per tree node: OK")

for trial in range(200):
    N = random.randint(4, 300)
    nodes = []; build(1, N, nodes)
    height = max(nd[4] for nd in nodes)
    # random read edges, each stage t reads at most one earlier stage
    edges = [(random.randint(1, t-1), t) for t in range(2, N+1) if random.random() < 0.8]
    E = {}
    for (s, t) in edges: E.setdefault(assign(nodes, s, t), []).append((s, t))
    B = max(len(x) for x in E.values()) if E else 0
    # Lemma: every chronological cut crossed by at most B*height edges
    for tau in range(1, N):
        cross = sum(1 for (s, t) in edges if s <= tau < t)
        assert cross <= B * height
    # online recursion: oracle fails exactly when the subtree contains a heavy node (worst case)
    for Bthr in [1, 2, 4, 8]:
        heavy = {v for v, x in E.items() if len(x) > Bthr}
        def has_heavy(v):
            if v in heavy: return True
            lo, hi, l, r, _ = nodes[v]
            return l is not None and (has_heavy(l) or has_heavy(r))
        marked = sum(1 for v in range(len(nodes)) if has_heavy(v))
        calls = 0
        def solve(v):
            global calls
            calls += 1
            if has_heavy(v):
                lo, hi, l, r, _ = nodes[v]
                solve(l); solve(r)
        solve(0)
        assert len(heavy) <= len(edges) / Bthr
        assert marked <= len(heavy) * (height + 1)
        assert calls <= 1 + 2 * marked
print("frontier bound B*h and recursion call count 1+2*marked <= 1+2(N/B)(h+1): OK")
