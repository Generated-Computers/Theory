#!/usr/bin/env python3
"""Arrays with one NOR gate per cell (types N, X, R only) become monotone after
complementing the odd layers: checks monotonicity of the normalized output in the
layer-0 values, exhaustively over the inputs, for 3000 random small arrays."""
import itertools, random
def evalarr(k, gates, inp):
    v = list(inp)
    for t, row in enumerate(gates, 1):
        nv = []
        for s in range(k):
            o = s - 1 if t % 2 == 1 else s + 1
            a = v[s]; b = v[o] if 0 <= o < k else a
            nv.append({'N': 1 - a, 'X': 1 - b, 'R': 1 - (a | b)}[row[s]])
        v = nv
    return v
rng = random.Random(1); bad = 0
for _ in range(3000):
    k = rng.randint(1, 5); d = rng.randint(1, 6)
    gates = [[rng.choice('NXR') for _ in range(k)] for _ in range(d)]
    f = {inp: [b ^ (d % 2) for b in evalarr(k, gates, inp)] for inp in itertools.product([0, 1], repeat=k)}
    for x in f:
        for y in f:
            if all(a <= b for a, b in zip(x, y)) and any(p > q for p, q in zip(f[x], f[y])): bad += 1
print('monotonicity violations:', bad)
