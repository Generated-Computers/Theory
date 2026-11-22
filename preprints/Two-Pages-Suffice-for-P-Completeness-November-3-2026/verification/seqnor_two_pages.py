#!/usr/bin/env python3
"""Checks for the two-page P-completeness construction of Sequential NOR.

Implements exactly the construction of the paper:
  NOR circuit -> slot program -> NOR/OR array (3-column gadgets) -> Sequential NOR
  instance (2-cell constant blocks, uniform 8-cell blocks, 4-cell tail) with the
  two-page assignment (page 1: transitions of odd layers, internal arcs; page 2:
  transitions of even layers; tail arc on the page of parity d-1).
Checks: gadget tables (all inputs), slot programs, array values, Sequential NOR
values at every block output, parent constraint 0 <= j_i < i, and the absence of
same-page crossings (sweep checker; naive pairwise checker on smaller instances).
Usage: python3 seqnor_two_pages.py [seed]
"""
import itertools, random, sys, bisect

def NOR(a, b): return 1 - (a | b)

# ---------------- Sequential NOR -----------------
def seqnor(j):
    """j[1..n] (j[0] unused); returns trace x[0..n]."""
    n = len(j) - 1
    x = [1] + [0] * n
    for i in range(1, n + 1):
        x[i] = NOR(x[i - 1], x[j[i]])
    return x

# ---------------- NOR circuits -------------------
def eval_circuit(gates):
    """w0=1, w1=0, w_g = NOR(w_a, w_b) for gates[g-2] = (a, b), a, b < g."""
    w = [1, 0]
    for a, b in gates:
        w.append(NOR(w[a], w[b]))
    return w

def slot_program(gates):
    G = len(gates) + 1
    prog = []
    for g in range(2, G + 1):
        a, b = sorted(gates[g - 2])
        prog += [('SWAP', i) for i in range(g - 1, a, -1)]
        prog += [('COPY', a)]
        prog += [('SWAP', i) for i in range(a + 1, g)]
        prog += [('SWAP', i) for i in range(g, b, -1)]
        prog += [('COPY', b)]
        prog += [('SWAP', i) for i in range(b + 1, g + 1)]
        prog += [('NOR', g)]
    return prog

def run_slots(prog, z):
    z = list(z)
    for op, i in prog:
        if op == 'SWAP': z[i], z[i + 1] = z[i + 1], z[i]
        elif op == 'COPY': z[i + 1] = z[i]
        else: z[i] = NOR(z[i], z[i + 1])
    return z

# ---------------- arrays -------------------------
# cell types: N = not self, C = copy self, X = not neighbour, Y = copy neighbour,
# R = NOR(self, neighbour), O = OR(self, neighbour); neighbour = s-1 (t odd), s+1 (t even)
GADGETS = {  # rows = layers 1..h, letters = columns 2i, 2i+1, 2i+2
    'COPY': ['NXN', 'NNN', 'NNY', 'NRC'],
    'NOR':  ['NNN', 'NXN', 'NON', 'XRN'],
    'SWAP': ['NXN', 'NRC', 'NCR', 'RON', 'CRN', 'RCC', 'NNO', 'NRN'],
}

def nbr(t, s): return s - 1 if t % 2 == 1 else s + 1

def cell(m, a, b):
    return {'N': 1 - a, 'C': a, 'X': None if b is None else 1 - b, 'Y': b,
            'R': None if b is None else NOR(a, b), 'O': None if b is None else (a | b)}[m]

def eval_array(layer0, layers):
    k = len(layer0); vals = [list(layer0)]
    for t, row in enumerate(layers, 1):
        v = vals[-1]; nv = []
        for s in range(k):
            o = nbr(t, s); b = v[o] if 0 <= o < k else None
            if row[s] in 'XYRO': assert b is not None, 'reads outside the array'
            nv.append(cell(row[s], v[s], b))
        vals.append(nv)
    return vals

def array_from_program(M, prog, z0):
    k = 2 * M
    layer0 = [0] * k
    for i in range(M): layer0[2 * i] = z0[i]
    layers = []
    for op, i in prog:
        for mv in GADGETS[op]:
            row = ['C'] * k
            row[2 * i:2 * i + 3] = list(mv)
            layers.append(row)
    return layer0, layers

# ---------------- compilation to Sequential NOR --
def compile_array(layer0, layers, out):
    """Returns j (1-indexed), list of arcs (left, right, page), and output positions."""
    k, d = len(layer0), len(layers)
    j = [None, 0]; arcs = [(0, 1, 1)]; pos = {}
    def put(par, page):
        j.append(par); arcs.append((par, len(j) - 1, page))
    for s in range(k):                       # layer 0: 2-cell constant blocks
        c = len(j); put(c - 1, 1); put(c, 1)
        pos[(0, s)] = c if layer0[s] == 1 else c + 1
    for t in range(1, d + 1):                # layers t >= 1: 8-cell blocks, serpentine order
        order = range(k) if t % 2 == 0 else range(k - 1, -1, -1)
        tp = 1 if t % 2 == 1 else 2          # page of transition t
        for s in order:
            c = len(j); m = layers[t - 1][s]; o = nbr(t, s)
            src = {'N': (s, s), 'C': (s, s), 'X': (o, o), 'Y': (o, o),
                   'R': (s, o), 'O': (s, o)}[m]       # (alpha source, beta source): self first
            p, q = pos[(t - 1, src[0])], pos[(t - 1, src[1])]
            put(p, tp); put(c, 1); put(c, 1); put(c, 1)
            put(q, tp); put(c + 4, 1); put(c + 5, 1); put(c + 5, 1)
            pos[(t, s)] = c + 4 if m in 'NXR' else c + 5
    mm = len(j)                              # tail
    put(pos[out], 1 if (d - 1) % 2 == 1 else 2)
    put(mm, 1); put(mm, 1); put(mm, 1)
    return j, arcs, pos

def crossings_sweep(arcs):
    bad = 0; by = {}
    for a, b, p in arcs:
        if b - a > 1: by.setdefault(p, []).append((a, b))
    for L in by.values():
        L.sort(); starts = [a for a, b in L]
        for a1, b1 in L:
            lo = bisect.bisect_right(starts, a1); hi = bisect.bisect_left(starts, b1)
            bad += sum(1 for a2, b2 in L[lo:hi] if a1 < a2 < b1 < b2)
    return bad

def crossings_naive(arcs):
    bad = 0
    for (a1, b1, p1), (a2, b2, p2) in itertools.combinations(arcs, 2):
        if p1 == p2 and (a1 < a2 < b1 < b2 or a2 < a1 < b2 < b1): bad += 1
    return bad

def crossings_one_page(arcs):
    return crossings_sweep([(a, b, 1) for a, b, p in arcs])

# ---------------- checks -------------------------
def check_gadgets():
    for name, rows in GADGETS.items():
        for u, v, other in itertools.product([0, 1], repeat=3):
            # columns: (2i, 2i+1, 2i+2, 2i+3) = (u, 0, v, 0); neighbours outside hold 'other'
            layer0 = [other, u, 0, v, 0, other]
            layers = [['C'] + list(r) + ['C', 'C'] for r in rows]
            vals = eval_array(layer0, layers)[-1]
            want = {'COPY': (u, 0, u), 'NOR': (NOR(u, v), 0, v), 'SWAP': (v, 0, u)}[name]
            assert tuple(vals[1:4]) == want and vals[4] == 0 and vals[0] == other == vals[5], name
            # gadget never reads outside its three columns
            for t, r in enumerate(rows, 1):
                if t % 2 == 1: assert r[0] in 'NC', name
                else: assert r[2] in 'NC', name
    return True

def check_circuits(rng, trials=300):
    stats = dict(instances=0, mismatches=0, crossings=0, naive_checked=0, naive_crossings=0, max_n=0)
    for _ in range(trials):
        G = rng.randint(2, 8)
        gates = [(rng.randrange(g), rng.randrange(g)) for g in range(2, G + 1)]
        w = eval_circuit(gates); M = G + 2; prog = slot_program(gates)
        z0 = [1, 0] + [0] * (M - 2)
        z = run_slots(prog, z0); assert z[:G + 1] == w
        layer0, layers = array_from_program(M, prog, z0)
        vals = eval_array(layer0, layers); d = len(layers)
        assert all(vals[d][2 * i] == w[i] for i in range(G + 1))
        j, arcs, pos = compile_array(layer0, layers, (d, 2 * G))
        assert all(0 <= j[i] < i for i in range(1, len(j)))
        x = seqnor(j)
        if x[-1] != w[G] or any(x[p] != vals[t][s] for (t, s), p in pos.items()):
            stats['mismatches'] += 1
        stats['crossings'] += crossings_sweep(arcs)
        if len(j) < 3000:
            stats['naive_checked'] += 1; stats['naive_crossings'] += crossings_naive(arcs)
        stats['instances'] += 1; stats['max_n'] = max(stats['max_n'], len(j) - 1)
    return stats

def check_random_arrays(rng, trials=450):
    stats = dict(instances=0, mismatches=0, crossings_sweep=0, crossings_naive=0, one_page_crossings=0)
    for _ in range(trials):
        k = rng.randint(1, 7); d = rng.randint(1, 9)
        layer0 = [rng.randint(0, 1) for _ in range(k)]
        layers = [[rng.choice('NCXYRO' if 0 <= nbr(t, s) < k else 'NC') for s in range(k)]
                  for t in range(1, d + 1)]
        out = (d, rng.randrange(k))
        vals = eval_array(layer0, layers)
        j, arcs, pos = compile_array(layer0, layers, out)
        assert all(0 <= j[i] < i for i in range(1, len(j)))
        x = seqnor(j)
        if x[-1] != vals[out[0]][out[1]] or any(x[p] != vals[t][s] for (t, s), p in pos.items()):
            stats['mismatches'] += 1
        stats['crossings_sweep'] += crossings_sweep(arcs)
        stats['crossings_naive'] += crossings_naive(arcs)
        stats['one_page_crossings'] += crossings_one_page(arcs)
        stats['instances'] += 1
    return stats

if __name__ == '__main__':
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 2026
    rng = random.Random(seed)
    print('gadget tables verified:', check_gadgets())
    print('compiled NOR circuits:', check_circuits(rng))
    print('random arrays:', check_random_arrays(rng))
    print('(one_page_crossings > 0 shows the checker detects crossings when all arcs share a page)')
