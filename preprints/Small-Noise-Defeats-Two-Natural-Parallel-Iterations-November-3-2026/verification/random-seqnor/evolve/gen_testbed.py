# Test bed for the algorithm search (NOTE.md §5j). Every instance is a smoothed Sequential NOR
# instance stored as int32 little-endian: n, then j_1..j_n. The engine computes the true trace itself.
# Families (noise 1/64 unless stated):
#   emb-wW   : a layered NOR circuit of width W (each gate reads two gates of the previous layer),
#              compiled by the fault-tolerant post-order compiler of paper Section 9 (6-gate MAJ,
#              m copies, cells of depth h), then smoothed. W = 2, 8, or ~sqrt(#gates).
#   emb-rand : the same compiler on a circuit whose gates read uniform earlier gates (shallow).
#   emb1-wW  : the same layered circuit compiled without redundancy (m = 1, h = 0: one NOR gadget per
#              gate), W = 2, 4, 8; live width about 3W, so it tests whether a candidate follows narrow
#              circuits (the bounded-width frontier).
#   block32  : random block base, blocks of 32, targets at offsets >= 4 (paper Def. 10.15 style).
#   block8   : the same with blocks of 8 (targets at offsets >= 2).
#   rev-wW   : a reversible circuit on W wires (random initial values; each step is a random Toffoli
#              gate c <- c xor (a and b), 7 NOR gates, or with probability 1/4 a NOT), compiled without
#              redundancy. Its state never coalesces, unlike random NOR circuits.
#   remb-wW  : the same reversible circuit compiled with the fault-tolerant compiler (m = 5, h = 1),
#              which preserves the computation at noise 1/64 (Thm 9.7): the candidate hard core.
#   lin2     : j_i = i - 2.
#   NAME@e   : any family smoothed with noise e instead of 1/64 (e.g. block32@0.3).
#   uniform  : eps = 1 (uniform random instances; should be easy).
# usage: python3 -I gen_testbed.py OUTDIR seed size1 size2 ...   (sizes are target n, e.g. 2048)
import math, os, random, struct, sys, zlib

EPS = 1 / 64
M_COPIES, H_CELL = 5, 1
CELL = 4 * 3 ** H_CELL + 6 * (3 ** H_CELL - 1) // 2          # gates per cell (18 for h = 1)

def layered_circuit(s, w, rng):
    """gates 1..s in layers of width w; layer 0 reads constants; gate t reads two gates of the previous layer"""
    gu, gv = [None], [None]
    for t in range(1, s + 1):
        layer = (t - 1) // w
        if layer == 0:
            gu.append(rng.choice(['c0', 'c1'])); gv.append(rng.choice(['c0', 'c1']))
        else:
            lo = (layer - 1) * w + 1; hi = min(layer * w, s)
            a, b = rng.sample(range(lo, hi + 1), 2) if hi > lo else (lo, lo)
            gu.append(a); gv.append(b)
    return gu, gv

def reversible_circuit(s_target, w, rng):
    gu, gv = [None], [None]
    def add(u, v): gu.append(u); gv.append(v); return len(gu) - 1
    def NOT(a): return add(a, a)
    def AND(a, b): return add(NOT(a), NOT(b))
    def XOR(p, q): return add(add(p, q), AND(p, q))
    wire = [add(c, c) for c in (rng.choice(['c0', 'c1']) for _ in range(w))]   # NOR(c0,c0)=1, NOR(c1,c1)=0
    while len(gu) - 1 < s_target:
        if rng.random() < 0.25:
            k = rng.randrange(w); wire[k] = NOT(wire[k])
        else:
            a, b, c = rng.sample(range(w), 3)
            wire[c] = XOR(wire[c], AND(wire[a], wire[b]))
    return gu, gv

def random_circuit(s, rng):
    gu, gv = [None], [None]
    for t in range(1, s + 1):
        ch = ['c0', 'c1'] + list(range(1, t))
        gu.append(rng.choice(ch)); gv.append(rng.choice(ch))
    return gu, gv

def compile6(gu, gv, m, h, rng):
    """post-order compiler of paper Section 9 with the 6-gate MAJ (a, a, c, k+1, b, k), c = k-1"""
    s = len(gu) - 1
    j = [None, 0]; out = {}
    def o(u, r): return 1 if u == 'c0' else 0 if u == 'c1' else out[(u, r)]
    def emit(p): j.append(p); return len(j) - 1
    def tree(t, lev):
        if lev == 0:
            a, b = o(gu[t], rng.randrange(m)), o(gv[t], rng.randrange(m))
            for p in (0, a, 1, b): last = emit(p)
            return last
        a, b, c = tree(t, lev - 1), tree(t, lev - 1), tree(t, lev - 1)
        k = len(j); assert c == k - 1
        for p in (a, a, c, k + 1, b, k): last = emit(p)
        return last
    for t in range(1, s + 1):
        for l in range(m): out[(t, l)] = tree(t, h)
    return j[1:]                                   # j_1..j_n

def smooth(base, eps, rng):
    j = list(base)
    for i in range(2, len(j) + 1):                 # j[i-1] is j_i; gate 1 always points to 0
        if rng.random() < eps: j[i - 1] = rng.randrange(i)
    return j

def family(name, target, rng):
    global EPS
    if '@' in name:
        base, e = name.split('@'); old = EPS; EPS = float(e)
        try: return family(base, target, rng)
        finally: EPS = old
    if name.startswith('remb-w'):
        w = int(name[6:]); gu, gv = reversible_circuit(max(8, round((target - 1) / (M_COPIES * CELL))), w, rng)
        return smooth(compile6(gu, gv, M_COPIES, H_CELL, rng), EPS, rng)
    if name.startswith('rev-w'):
        w = int(name[5:]); gu, gv = reversible_circuit(max(8, round((target - 1) / 4)), w, rng)
        return smooth(compile6(gu, gv, 1, 0, rng), EPS, rng)
    if name.startswith('emb1-w'):
        w = int(name[6:]); s = max(4, round((target - 1) / 4))
        gu, gv = layered_circuit(s, w, rng)
        return smooth(compile6(gu, gv, 1, 0, rng), EPS, rng)
    if name.startswith('emb'):
        s = max(4, round((target - 1) / (M_COPIES * CELL)))
        if name == 'emb-rand': gu, gv = random_circuit(s, rng)
        else:
            w = {'emb-w2': 2, 'emb-w8': 8}.get(name) or max(2, round(math.sqrt(s)))
            gu, gv = layered_circuit(s, w, rng)
        return smooth(compile6(gu, gv, M_COPIES, H_CELL, rng), EPS, rng)
    n = target
    if name in ('block32', 'block8'):
        B, h = (32, 4) if name == 'block32' else (8, 2); base = []
        for i in range(1, n + 1):
            b = i // B
            base.append(max(i - 2, 0) if b == 0 else (b - 1) * B + rng.randint(h, B - 2))
        return smooth(base, EPS, rng)
    if name == 'lin2': return smooth([max(i - 2, 0) for i in range(1, n + 1)], EPS, rng)
    if name == 'uniform': return [0] + [rng.randrange(i) for i in range(2, n + 1)]
    raise ValueError(name)

FAMILIES = ['emb-w2', 'emb-w8', 'emb-wsqrt', 'emb-rand', 'block32', 'lin2', 'uniform', 'emb1-w2', 'emb1-w4', 'emb1-w8',
            'block8', 'block32@0.3', 'emb1-w4@0.1']

if __name__ == '__main__':
    out, seed, sizes = sys.argv[1], int(sys.argv[2]), [int(x) for x in sys.argv[3:]]
    os.makedirs(out, exist_ok=True)
    for f in FAMILIES:
        for size in sizes:
            rng = random.Random(zlib.crc32(('%d/%s/%d' % (seed, f, size)).encode()))
            j = family(f, size, rng)
            assert j[0] == 0 and all(0 <= j[i - 1] < i for i in range(1, len(j) + 1))
            with open(os.path.join(out, '%s_%d.bin' % (f, size)), 'wb') as fh:
                fh.write(struct.pack('<i', len(j))); fh.write(struct.pack('<%di' % len(j), *j))
            print(f, size, 'n =', len(j))
