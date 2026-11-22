# Checks for the Kleene-prefix (KP) iteration (paper Section 10, NOTE.md §5d).
# 1. Lemma K1: the round in which KP first knows x_i equals the dependency depth d(i), and every value KP
#    fixes is correct. Checked on random small instances with random bases and random smoothing.
# 2. The recursive evaluator (space O(depth * log n)) returns the trace, and its number of calls equals the
#    number of dependency chains.
# usage: python3 -I kp_check.py
import random, sys
sys.setrecursionlimit(10000)

def trace(j):
    x = [1] + [0] * (len(j) - 1)
    for i in range(1, len(j)): x[i] = int(not (x[i - 1] or x[j[i]]))
    return x

def kp_rounds(j):
    n = len(j) - 1; known = [False] * (n + 1); val = [0] * (n + 1); known[0] = True; val[0] = 1
    first = [None] * (n + 1); first[0] = 0; t = 0
    while not all(known):
        t += 1; nk = known[:]; ok = True; v = 1
        for i in range(1, n + 1):
            q = j[i]
            if q == i - 1: v ^= 1
            elif known[q]:
                if val[q]: v = 0; ok = True
                else: v ^= 1
            else: ok = False
            if ok:
                if known[i]: assert val[i] == v
                val[i] = v; nk[i] = True
                if first[i] is None: first[i] = t
            else: assert not known[i], "knowledge lost"
        known = nk
        assert t <= n + 1
    return first, val

def depth(j, x):
    n = len(j) - 1; d = [0] * (n + 1)
    for i in range(1, n + 1):
        r = i
        while r >= 1 and not (j[r] != r - 1 and x[j[r]] == 1): r -= 1     # rho(i): last true reset, or 0
        ks = [k for k in range(max(r, 1), i + 1) if j[k] != k - 1]
        d[i] = 1 + max((d[j[k]] for k in ks), default=0)
    return d

def evaluate(j, q, counter):
    counter[0] += 1
    if q == 0: return 1
    for k in range(q, 0, -1):
        if j[k] == k - 1: continue
        if evaluate(j, j[k], counter) == 1: return (q - k) % 2
    return 1 ^ (q % 2)

def chains(j, x, q, memo):
    if q in memo: return memo[q]
    if q == 0: memo[q] = 1; return 1
    r = q
    while r >= 1 and not (j[r] != r - 1 and x[j[r]] == 1): r -= 1
    tot = 1 + sum(chains(j, x, j[k], memo) for k in range(max(r, 1), q + 1) if j[k] != k - 1)
    memo[q] = tot; return tot

R = random.Random(7); cnt = 0
for _ in range(3000):
    n = R.randrange(1, 60); eps = R.choice([0.0, 0.3, 0.8, 1.0])
    kind = R.choice(['unif', 'im2', 'local', 'zero'])
    base = [0, 0] + [R.randrange(i) if kind == 'unif' else max(0, i - 2) if kind == 'im2'
                     else max(0, i - 1 - R.randrange(3)) if kind == 'local' else 0 for i in range(2, n + 1)]
    j = [0] + [R.randrange(i) if R.random() < eps else base[i] for i in range(1, n + 1)]
    x = trace(j); first, val = kp_rounds(j); d = depth(j, x)
    assert val == x and first == d, (j, first, d)
    q = n; c = [0]; assert evaluate(j, q, c) == x[q]
    assert c[0] == chains(j, x, q, {}), (c[0], chains(j, x, q, {}))
    cnt += 1
print("Lemma K1 (KP round = dependency depth, values correct) and the recursive evaluator verified on", cnt, "instances")
