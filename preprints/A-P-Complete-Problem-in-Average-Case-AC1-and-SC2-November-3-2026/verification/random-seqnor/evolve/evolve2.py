# Wide search (NOTE.md §5j, run 2). Genomes now choose a representation as well as a strategy:
#   tt : truth tables over at most K variables (engine.c built with -DKMAX=12), with K, orders
#        (incl. 4 = anchored doubling), substitutions per round, pivot gating, try-simplify;
#   bdd: reduced ordered BDDs with at most S nodes and VMAX variables (engine_bdd.c), with order and
#        substitutions per round.
# Test bed: 13 families (gen_testbed.py), sizes 1024, 4096, 16384. Scoring as in evolve.py (mean
# slope of log rounds against log n; wrong values are fatal; unfinished runs are charged), plus a
# small work term. Selection keeps the best genome in each niche (representation x order class) and
# the global leaders, so that both representations stay in the population.
# usage: python3 -I evolve2.py ENGINE_TT ENGINE_BDD TESTBED OUTDIR [generations] [population] [seed]
import json, math, os, random, subprocess, sys, time
from multiprocessing import Pool

FAMS = ['emb-w2', 'emb-w8', 'emb-wsqrt', 'emb-rand', 'block32', 'lin2', 'uniform', 'emb1-w2', 'emb1-w4',
        'emb1-w8', 'block8', 'block32@0.3', 'emb1-w4@0.1']
SIZES = [1024, 4096, 16384]
CAPF = 4.0
TIMEOUT = 900
TT = {'K': [4, 6, 8, 10, 12], 'orders': ['0', '2', '3', '03', '013', '4', '40', '43', '41', '403', '44'],
      'maxsub': [0, 1, 2, 3], 'rho': [0, 0.5, 0.25, 0.125], 'TL': [1, 2, 4, 8], 'trysimp': [0, 1]}
BDD = {'S': [8, 16, 32], 'VMAX': [16, 32, 64], 'order': [0, 1, 2, 4], 'maxsub': [0, 1, 2, 3]}

def run(cmd):
    out = subprocess.run(cmd, capture_output=True, text=True, timeout=TIMEOUT).stdout
    res = {}
    for line in out.split('\n'):
        p = line.split()
        if len(p) == 8:
            res[os.path.basename(p[0])] = dict(n=int(p[1]), rounds=int(p[2]), fin=int(p[3]), known=float(p[5]), err=int(p[7]))
    return res

def command(eng, g, files):
    if g['engine'] == 'tt':
        return [eng[0], 'sub', str(g['K']), g['orders'], str(g['maxsub']), str(g['rho']), str(g['TL']),
                str(g['trysimp']), '1', str(CAPF)] + files
    return [eng[1], str(g['S']), str(g['VMAX']), str(g['order']), str(g['maxsub']), '1', str(CAPF)] + files

def slope(xs, ys):
    mx, my = sum(xs) / len(xs), sum(ys) / len(ys)
    return sum((a - mx) * (b - my) for a, b in zip(xs, ys)) / sum((a - mx) ** 2 for a in xs)

def work(g):
    return 2 ** (g['K'] - 6) * len(g['orders']) * (1 + g['trysimp']) if g['engine'] == 'tt' else g['S'] / 16

def evaluate(args):
    eng, tb, g = args
    files = [os.path.join(tb, '%s_%d.bin' % (f, s)) for f in FAMS for s in SIZES]
    t0 = time.time()
    try: res = run(command(eng, g, files))
    except subprocess.TimeoutExpired: return dict(genome=g, fit=99, fam=None, err=0, secs=TIMEOUT)
    fam, errs = {}, 0
    for f in FAMS:
        rows = [res.get('%s_%d.bin' % (f, s)) for s in SIZES]
        if any(r is None for r in rows): return dict(genome=g, fit=99, fam=None, err=0, secs=round(time.time() - t0))
        xs, ys = [], []
        for r in rows:
            errs += r['err']
            cap = math.ceil(CAPF * math.log2(r['n']) ** 2)
            R = r['rounds'] if r['fin'] else cap * (1 + 4 * (1 - r['known']))
            xs.append(math.log2(r['n'])); ys.append(math.log2(max(R, 1)))
        fam[f] = dict(slope=round(slope(xs, ys), 3), rounds=[round(2 ** y) for y in ys])
    fit = 99 if errs else sum(v['slope'] for v in fam.values()) / len(fam) + 0.002 * work(g)
    return dict(genome=g, fit=round(fit, 4), fam=fam, err=errs, secs=round(time.time() - t0))

def key(g): return json.dumps(g, sort_keys=True)
def rand_genome(rng, engine=None):
    engine = engine or rng.choice(['tt', 'bdd'])
    sp = TT if engine == 'tt' else BDD
    g = {k: rng.choice(v) for k, v in sp.items()}; g['engine'] = engine; return g
def mutate(g, rng):
    if rng.random() < 0.1: return rand_genome(rng, 'bdd' if g['engine'] == 'tt' else 'tt')
    sp = TT if g['engine'] == 'tt' else BDD; h = dict(g)
    for _ in range(rng.choice([1, 1, 2])):
        k = rng.choice(list(sp)); h[k] = rng.choice(sp[k])
    return h
def cross(a, b, rng):
    if a['engine'] != b['engine']: return dict(a)
    sp = TT if a['engine'] == 'tt' else BDD
    h = {k: (a if rng.random() < 0.5 else b)[k] for k in sp}; h['engine'] = a['engine']; return h
def niche(g):
    o = g['orders'][0] if g['engine'] == 'tt' else str(g['order'])
    return g['engine'] + ('-anchored' if o == '4' else '-greedy')

def main():
    eng = (sys.argv[1], sys.argv[2]); tb, out = sys.argv[3], sys.argv[4]
    gens = int(sys.argv[5]) if len(sys.argv) > 5 else 10
    pop = int(sys.argv[6]) if len(sys.argv) > 6 else 22
    rng = random.Random(int(sys.argv[7]) if len(sys.argv) > 7 else 2)
    os.makedirs(out, exist_ok=True)
    log = open(os.path.join(out, 'log.jsonl'), 'a'); seen = {}
    seeds = [dict(engine='tt', K=8, orders='4', maxsub=0, rho=0, TL=1, trysimp=0),
             dict(engine='tt', K=12, orders='4', maxsub=0, rho=0, TL=1, trysimp=0),
             dict(engine='tt', K=6, orders='0', maxsub=0, rho=0, TL=1, trysimp=0),
             dict(engine='bdd', S=16, VMAX=64, order=4, maxsub=0),
             dict(engine='bdd', S=32, VMAX=64, order=4, maxsub=0)]
    batch = seeds + [rand_genome(rng) for _ in range(pop - len(seeds))]
    with Pool(min(11, os.cpu_count() or 2)) as P:
        for gen in range(gens):
            todo = [g for g in batch if key(g) not in seen]
            for r in P.imap_unordered(evaluate, [(eng, tb, g) for g in todo]):
                r['gen'] = gen; seen[key(r['genome'])] = r
                log.write(json.dumps(r) + '\n'); log.flush()
            ranked = sorted(seen.values(), key=lambda r: r['fit'])
            best = ranked[0]
            cells = {}
            for r in ranked: cells.setdefault(niche(r['genome']), r)
            print('gen %d: %d evaluated; best %.4f %s' % (gen, len(seen), best['fit'], best['genome']), flush=True)
            if best['fam']: print('   slopes: ' + ' '.join('%s:%.2f' % (f, best['fam'][f]['slope']) for f in FAMS), flush=True)
            print('   niches: ' + '; '.join('%s %.3f' % (c, r['fit']) for c, r in sorted(cells.items())), flush=True)
            parents = [r['genome'] for r in ranked[:12] if r['fit'] < 99] + [r['genome'] for r in cells.values() if r['fit'] < 99]
            batch, tries = [], 0
            while len(batch) < pop and tries < 100 * pop:
                tries += 1
                a, b = rng.choice(parents), rng.choice(parents)
                child = mutate(cross(a, b, rng), rng) if rng.random() < 0.5 else mutate(a, rng)
                if key(child) not in seen and child not in batch: batch.append(child)
    ranked = sorted(seen.values(), key=lambda r: r['fit'])
    json.dump(ranked[:30], open(os.path.join(out, 'leaderboard.json'), 'w'), indent=1)
    print('top 8:')
    for r in ranked[:8]:
        print(' %.4f %s (%ss)' % (r['fit'], r['genome'], r['secs']))
        if r['fam']:
            for f in FAMS: print('    %-12s slope %.3f rounds %s' % (f, r['fam'][f]['slope'], r['fam'][f]['rounds']))

if __name__ == '__main__':
    main()
