# Checks behind NOTE.md §5b / paper Section 8:
#  (1) the trace equals the lexicographically-first maximal independent set of the graph with
#      edges {i-1,i} and {j_i,i}, processed in the natural order 0,1,2,...;
#  (2) the binary core B(j) = {i : 1 <= j_i <= i-2, j_{i-1} != 0} has size n - O(log n);
#  (3) the live width at the midpoint is about n/4;
#  (4) the density of ones of the trace is close to (3 - sqrt 5)/2.
# usage: python3 -I structure_checks.py
import random, math, statistics, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core import truth, rand_j

def lfmis(n, j):
    adj = [set() for _ in range(n + 1)]
    for i in range(1, n + 1):
        for u in (i - 1, j[i - 1]):
            if u != i: adj[i].add(u); adj[u].add(i)
    sel = [0] * (n + 1)
    for v in range(n + 1):                      # greedy in the natural order
        sel[v] = int(not any(sel[u] for u in adj[v] if u < v))
    return sel

random.seed(2026)
for _ in range(2000):
    n = random.randint(1, 60); j = rand_j(n)
    assert lfmis(n, j) == truth(j)
print("(1) trace == lexicographically-first MIS on 2000 random instances")

rows = []
for n in (10**3, 10**4, 10**5):
    core, live, dens = [], [], []
    for _ in range(20 if n < 10**5 else 5):
        j = rand_j(n); x = truth(j)
        B = sum(1 for i in range(2, n + 1) if 1 <= j[i-1] <= i - 2 and j[i-2] != 0)
        core.append(n - B)
        c = n // 2
        live.append(len({j[i-1] for i in range(c + 1, n + 1) if j[i-1] <= c - 1 or j[i-1] == c}))
        dens.append(sum(x) / (n + 1))
    H = sum(1 / k for k in range(1, n + 1))
    print(f"n={n:6d}: n-|core| mean {statistics.mean(core):6.1f} (exact mean 3H_n-3+1/n = {3*H - 3 + 1/n:5.1f}); "
          f"live width at n/2 / n = {statistics.mean(live)/n:.4f}; density of ones {statistics.mean(dens):.5f}")
print("(3-sqrt5)/2 =", (3 - math.sqrt(5)) / 2)
