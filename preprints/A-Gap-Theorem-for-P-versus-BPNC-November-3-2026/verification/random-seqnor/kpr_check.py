"""Exhaustive check of the relevance-pruned iteration (KPR) on every parent array with n <= 8.

For each array: run KP and KPR exactly as defined in the paper (values come only from known
positions, never from the trace), and check
  (1) every value KPR records equals the trace,
  (2) the KPR known set after t rounds is {i : D(i) <= t} for the min-max depth D,
  (3) the KP known set is contained in the KPR known set after every round,
  (4) the O(n) recursion used by kp_probe.c (kprd) gives max D.
"""
import itertools, sys

def trace(j):
    x = [1]
    for i in range(1, len(j)):
        x.append(int(not (x[i - 1] or x[j[i]])))
    return x

def kp_round(j, K, v, prune):
    n = len(j) - 1
    K2, v2 = {0}, {0: 1}
    r, ok = 0, True
    for i in range(1, n + 1):
        q = j[i]; isnot = q == i - 1; res = isnot or q in K
        a_prev = v2[i - 1] if (i - 1) in v2 else alt(r, v2, v, i - 1)
        if res and not isnot and v[q] == 1:
            r, ok = i, True
        elif not res and (not prune or a_prev == 0):
            ok = False
        if ok:
            val = 0 if r == i else alt(r, v2, v, i)
            K2.add(i); v2[i] = val
    return K2, v2

def alt(r, v2, v, p):
    base = v2[r] if r in v2 else (1 if r == 0 else 0)
    return base ^ ((p - r) & 1)

def run(j, prune):
    K, v, hist = {0}, {0: 1}, [{0}]
    for _ in range(len(j) + 1):
        K, v = kp_round(j, K, v, prune)
        hist.append(K)
        if len(K) == len(j):
            break
    return K, v, hist

def depth(j, x):
    n = len(j) - 1; D = [0] * (n + 1)
    for i in range(1, n + 1):
        hits = [k for k in range(2, i + 1) if j[k] != k - 1 and x[j[k]] == 1]
        rel_hits = [k for k in hits if x[k - 1] == 0]
        last = rel_hits[-1] if rel_hits else 0
        cands = [k for k in hits if k >= last] + ([0] if last == 0 else [])
        best = None
        for r in cands:
            m = D[j[r]] if r >= 1 else 0
            for k in range(r + 1, i + 1):
                if x[k - 1] == 0 and j[k] != k - 1:
                    m = max(m, D[j[k]])
            best = m if best is None else min(best, m)
        D[i] = 1 + best
    return D

def kprd(j, x):
    n = len(j) - 1; d = [0] * (n + 1); m = 0
    for i in range(1, n + 1):
        q = j[i]; isnot = q == i - 1; rel = x[i - 1] == 0; hit = (not isnot) and x[q] == 1
        if hit and rel: m = d[q]
        elif hit: m = min(m, d[q])
        elif rel and not isnot: m = max(m, d[q])
        d[i] = 1 + m
    return max(d)

def main(nmax):
    count = 0
    for n in range(1, nmax + 1):
        for tail in itertools.product(*[range(k) for k in range(2, n + 1)]):
            j = [0, 0] + list(tail)
            j = j[:n + 1]
            x = trace(j)
            Kr, vr, hr = run(j, True)
            Kk, vk, hk = run(j, False)
            assert len(Kr) == n + 1 and all(vr[i] == x[i] for i in range(n + 1)), (j, "KPR value")
            D = depth(j, x)
            for t, K in enumerate(hr):
                assert K == {i for i in range(n + 1) if D[i] <= t}, (j, t, "KPR = depth")
            for t in range(len(hk)):
                assert hk[t] <= hr[min(t, len(hr) - 1)], (j, t, "KP subset KPR")
            assert kprd(j, x) == max(D), (j, "kprd")
            count += 1
    print(f"KPR checks passed on all {count} parent arrays with n <= {nmax}")

if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 8)
