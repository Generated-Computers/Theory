"""Size of the dominator-prime core for two-generator A5 SLPs obtained from random Boolean
circuits through the NOT/AND gadgets (illustration for manuscript 004d)."""
import os, random, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from check_a5 import mul, inv, E, cyc, gen, A5, comm, power
from collections import deque

p, q = cyc(1, 2, 3, 4, 5), cyc(1, 2, 3)
a = cyc(1, 2, 3, 4, 5); c = cyc(3, 5, 4); d = cyc(2, 4, 3)

def build(nb, rng):
    nodes = [('P',), ('Q',)]
    def add(nd):
        nodes.append(nd); return len(nodes) - 1
    Pi = add(('inv', 0)); Qi = add(('inv', 1))
    lib = {p: 0, q: 1, inv(p): Pi, inv(q): Qi}
    lib[E] = add(('mul', 0, Pi))
    dq = deque([p, q, inv(p), inv(q)])
    gens = [(p, 0), (inv(p), Pi), (q, 1), (inv(q), Qi)]
    while dq:
        x = dq.popleft()
        for g, gi in gens:
            y = mul(x, g)
            if y not in lib:
                lib[y] = add(('mul', lib[x], gi)); dq.append(y)
    # Boolean circuit: inputs are constants e / a; gates NOT, AND
    wires = [lib[rng.choice([E, a])] for _ in range(4)]
    for _ in range(nb):
        if rng.random() < 0.3:
            x = rng.choice(wires[-8:])
            x2 = add(('mul', x, x)); x4 = add(('mul', x2, x2))
            wires.append(add(('mul', lib[a], x4)))
        else:
            x = rng.choice(wires[-8:]); y = rng.choice(wires)
            z = add(('mul', add(('mul', lib[inv(c)], y)), lib[c]))
            xi = add(('inv', x)); zi = add(('inv', z))
            k = add(('mul', add(('mul', add(('mul', xi, zi)), x)), z))
            wires.append(add(('mul', add(('mul', lib[inv(d)], k)), lib[d])))
    return nodes

def preds(nd):
    return ['s'] if nd[0] in ('P', 'Q') else list(nd[1:])

def prime_count(nodes):
    n = len(nodes)
    dominated = [False] * n   # has a proper dominator other than s
    for dd in range(n):
        R = set()
        for i, nd in enumerate(nodes):
            if i == dd:
                continue
            if any(pp == 's' or pp in R for pp in preds(nd)):
                R.add(i)
        for v in range(dd + 1, n):
            if v not in R:
                dominated[v] = True
    return n - sum(dominated)

rng = random.Random(1)
for nb in (50, 100, 200):
    nodes = build(nb, rng)
    h = prime_count(nodes)
    print(f"Boolean gates {nb}: SLP nodes {len(nodes)}, prime nodes {h}, fraction {h/len(nodes):.3f}")
