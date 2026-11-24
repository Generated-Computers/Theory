# Checks for 003d: NAND polytope vertices; NAND normalization of alternating circuits.
import itertools, random
from fractions import Fraction as Fr
random.seed(43)
# constraints a.x >= b on (x,y,z)
cons = [((1,0,0),0),((0,1,0),0),((0,0,1),0),((-1,0,0),-1),((0,-1,0),-1),((0,0,-1),-1),
        ((1,0,1),1),((0,1,1),1),((-1,-1,-1),-2)]
def solve3(A, b):
    M = [[Fr(v) for v in row] + [Fr(bb)] for row, bb in zip(A, b)]
    for c in range(3):
        p = next((r for r in range(c, 3) if M[r][c] != 0), None)
        if p is None: return None
        M[c], M[p] = M[p], M[c]
        for r in range(3):
            if r != c and M[r][c] != 0:
                f = M[r][c] / M[c][c]
                M[r] = [a - f * bb for a, bb in zip(M[r], M[c])]
    return tuple(M[i][3] / M[i][i] for i in range(3))
verts = set()
for tri in itertools.combinations(cons, 3):
    p = solve3([t[0] for t in tri], [t[1] for t in tri])
    if p is None: continue
    if all(sum(a*x for a, x in zip(c[0], p)) >= c[1] for c in cons):
        verts.add(p)
print("vertices:", sorted(tuple(int(v) for v in p) for p in verts))
print("NAND points:", sorted((x, y, 1-(x&y)) for x in (0,1) for y in (0,1)))
# NAND normalization on random layered alternating circuits
bad = 0
for trial in range(2000):
    L = random.randint(2, 6); width = random.randint(1, 4)
    layers = [[random.randint(0,1) for _ in range(width + 1)]]  # inputs (truth values)
    types = []
    top = random.choice(['AND','OR'])
    for l in range(1, L+1):
        typ = top if l % 2 == 1 else ('OR' if top == 'AND' else 'AND')
        prev = layers[-1]; cur = []; gates = []
        for _ in range(width):
            u, w = random.randrange(len(prev)), random.randrange(len(prev))
            t = (prev[u] & prev[w]) if typ == 'AND' else (prev[u] | prev[w])
            cur.append(t); gates.append((u, w))
        types.append((typ, gates)); layers.append(cur)
    # transformed bits: b = t for OR gates, 1-t for AND gates; inputs encoded by consumer type
    for l, (typ, gates) in enumerate(types, start=1):
        for g, (u, w) in enumerate(gates):
            t = layers[l][g]; bv = t if typ == 'OR' else 1 - t
            if l == 1:
                enc = (lambda tt: 1 - tt) if typ == 'OR' else (lambda tt: tt)
                bu, bw = enc(layers[0][u]), enc(layers[0][w])
            else:
                ptyp = types[l-2][0]
                bu = layers[l-1][u] if ptyp == 'OR' else 1 - layers[l-1][u]
                bw = layers[l-1][w] if ptyp == 'OR' else 1 - layers[l-1][w]
            if bv != 1 - (bu & bw): bad += 1
print("NAND normalization failures:", bad)
