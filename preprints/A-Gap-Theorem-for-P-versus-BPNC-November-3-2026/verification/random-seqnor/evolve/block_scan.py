# Growth of cut maps of random block bases with the block length B (NOTE.md §5j). For each B and seed,
# build an unsmoothed random block base (targets uniform on offsets >= max(2, B/8) of the previous
# block), probe the exact map from a cut to later cuts (bdd_probe.py), and report the largest shared
# BDD size over the horizons and the first horizon at which the map is constant (coalescence).
# BDD doubling solves a family in O(log n) rounds with work governed by the largest map, so the growth
# in B decides the no-go bases of Theorem 10.17, whose blocks have Theta(log^2 n) positions.
# usage: python3 -I block_scan.py B1 B2 ... [--seeds k] [--cap nodes] [--order desc|asc|random|reader]
import os, random, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bdd_probe import probe

def block_base(n, B, rng):
    h = max(2, B // 8); j = [0]
    for i in range(1, n + 1):
        b = i // B
        j.append(max(i - 2, 0) if b == 0 else (b - 1) * B + rng.randint(h, B - 2))
    return j

if __name__ == '__main__':
    args = sys.argv[1:]; seeds, cap, order = 3, 3_000_000, 'desc'
    if '--order' in args: k = args.index('--order'); order = args[k + 1]; del args[k:k + 2]
    if '--seeds' in args: k = args.index('--seeds'); seeds = int(args[k + 1]); del args[k:k + 2]
    if '--cap' in args: k = args.index('--cap'); cap = int(args[k + 1]); del args[k:k + 2]
    hs = [2 ** e for e in range(4, 14)]
    for B in map(int, args):
        for sd in range(seeds):
            rng = random.Random(1000 * B + sd); n = 16 * B + 8192 + 64
            j = block_base(n, B, rng); s = 8 * B
            res = probe(n, j, s, hs, node_cap=cap, order=order, seed=sd)
            sizes = [r[1] for r in res]
            capped = any(x is None for x in sizes)
            mx = max(x for x in sizes if x is not None) if any(x is not None for x in sizes) else None
            coal = next((r[0] for r in res if r[3]), None)
            print(order + ' B=%-3d seed=%d live width %3d  max map %s%s  constant from horizon %s'
                  % (B, sd, res[0][4], mx, ' (node cap hit)' if capped else '', coal), flush=True)
