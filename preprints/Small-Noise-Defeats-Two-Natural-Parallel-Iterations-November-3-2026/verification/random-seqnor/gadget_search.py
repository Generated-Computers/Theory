# Shortest Sequential-NOR gadgets: each gate is y <- NOR(y, z), z = a constant (x0=1, x1=0),
# an input, or an earlier gate of the gadget. The incoming chain value g is arbitrary (garbage);
# the last gate must equal the target for every g.
import itertools, sys
def search(nvars, target_fn, maxlen):
    V = nvars + 1                      # variable 0 = garbage g, then inputs
    N = 1 << V
    M = (1 << N) - 1
    var = [sum(1 << k for k in range(N) if (k >> v) & 1) for v in range(V)]
    tgt = sum(1 << k for k in range(N) if target_fn(*[(k >> v) & 1 for v in range(1, V)]))
    base = [('x0', M), ('x1', 0)] + [('in%d' % v, var[v]) for v in range(1, V)]
    best = None
    def rec(y, gates, L):
        nonlocal best
        if y == tgt and gates:
            best = list(gates); return True
        if len(gates) == L: return False
        opts = base + [('g%d' % (k + 1), gates[k][1]) for k in range(len(gates))]
        seen = set()
        for name, z in opts:
            ny = ~(y | z) & M
            if ny in seen: continue
            seen.add(ny)
            gates.append((name, ny))
            if rec(ny, gates, L): return True
            gates.pop()
        return False
    for L in range(1, maxlen + 1):
        if rec(var[0], [], L): return L, best
    return None
maj = lambda a, b, c: int(a + b + c >= 2)
nor = lambda a, b: int(not (a or b))
for name, nv, fn, ml in [('NOR(a,b)', 2, nor, 6), ('MAJ(a,b,c)', 3, maj, 12)]:
    r = search(nv, fn, ml)
    print(name, '->', r[0] if r else None, [g[0] for g in r[1]] if r else '')
    sys.stdout.flush()
