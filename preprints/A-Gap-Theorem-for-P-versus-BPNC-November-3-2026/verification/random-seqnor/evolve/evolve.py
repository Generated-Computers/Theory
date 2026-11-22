# Evolutionary search over parallel algorithms for smoothed Sequential NOR (NOTE.md §5j).
# A genome is a program in the engine's language (engine.c): K, the substitution orders of up to three
# alternative expressions, substitutions per round, pivot gating (rho, TL) and try-simplify. The
# evaluator runs a genome on the test bed (gen_testbed.py) at three sizes. It rejects any run with a
# wrong value. A family's score is the slope of log2(rounds) against log2(n); unfinished runs are
# charged cap * (1 + 4 * unknown fraction). Fitness is the mean slope over all families plus a tiny
# cost term, and lower is better. A polylogarithmic algorithm has slopes near 0.1-0.3 at these sizes;
# n^a rounds give slope a.
# Loop: elitist archive + tournament selection + uniform crossover + point mutation, evaluated in
# parallel. New primitives are added to engine.c by hand between runs (the "LLM mutation" step of
# AlphaEvolve-style search), after reading the leaderboard and failure statistics this script writes.
# usage: python3 -I evolve.py ENGINE TESTBED OUTDIR [generations] [population] [seed]
import json, math, os, random, subprocess, sys, time
from multiprocessing import Pool

FAMS = ['emb-w2', 'emb-w8', 'emb-wsqrt', 'emb-rand', 'block32', 'lin2', 'uniform']
if os.environ.get('EVOLVE_NARROW') == '1':     # run 2 on: add the narrow compiled families
    FAMS += ['emb1-w2', 'emb1-w4', 'emb1-w8']
SIZES = [2048, 8192, 32768]
CAPF = 4.0
GENES = {'K': [1, 2, 3, 4, 5, 6], 'orders': ['0', '1', '2', '3', '01', '03', '02', '13', '013', '023',
                                             '4', '40', '43', '41', '403'],          # 4: anchored doubling (added after run 1)
         'maxsub': [0, 1, 2, 3], 'rho': [0, 0.5, 0.25, 0.125, 0.0625], 'TL': [1, 2, 4, 8, 16],
         'trysimp': [0, 1]}

def run_engine(engine, files, g, seed=1):
    cmd = [engine, 'sub', str(g['K']), g['orders'], str(g['maxsub']), str(g['rho']), str(g['TL']),
           str(g['trysimp']), str(seed), str(CAPF)] + files
    out = subprocess.run(cmd, capture_output=True, text=True, timeout=3600).stdout.split('\n')
    res = {}
    for line in out:
        p = line.split()
        if len(p) != 8: continue
        res[os.path.basename(p[0])] = dict(n=int(p[1]), rounds=int(p[2]), fin=int(p[3]), stuck=int(p[4]),
                                           known=float(p[5]), meank=float(p[6]), err=int(p[7]))
    return res

def slope(xs, ys):
    mx, my = sum(xs) / len(xs), sum(ys) / len(ys)
    return sum((a - mx) * (b - my) for a, b in zip(xs, ys)) / sum((a - mx) ** 2 for a in xs)

def score(res, sizes=SIZES):
    fam = {}; errs = 0
    for f in FAMS:
        xs, ys, unfinished = [], [], 0
        for s in sizes:
            r = res.get('%s_%d.bin' % (f, s))
            if r is None: return None
            errs += r['err']
            cap = math.ceil(CAPF * math.log2(r['n']) ** 2)
            R = r['rounds'] if r['fin'] else cap * (1 + 4 * (1 - r['known']))
            unfinished += 1 - r['fin']
            xs.append(math.log2(r['n'])); ys.append(math.log2(max(R, 1)))
        fam[f] = dict(slope=slope(xs, ys), rounds=[round(2 ** y) for y in ys], unfinished=unfinished)
    return fam, errs

def fitness(g, fam):
    cost = g['K'] * len(g['orders']) * (1 + g['trysimp'])
    return sum(v['slope'] for v in fam.values()) / len(fam) + 0.002 * cost

def evaluate(args):
    engine, tb, g = args
    files = [os.path.join(tb, '%s_%d.bin' % (f, s)) for f in FAMS for s in SIZES]
    t0 = time.time()
    try: res = run_engine(engine, files, g)
    except subprocess.TimeoutExpired: return dict(genome=g, fit=99, fam=None, err=0, secs=3600)
    sc = score(res)
    if sc is None: return dict(genome=g, fit=99, fam=None, err=0, secs=time.time() - t0)
    fam, errs = sc
    fit = 99 if errs else fitness(g, fam)
    return dict(genome=g, fit=fit, fam=fam, err=errs, secs=round(time.time() - t0, 1))

def key(g): return json.dumps(g, sort_keys=True)
def random_genome(rng): return {k: rng.choice(v) for k, v in GENES.items()}
def mutate(g, rng):
    h = dict(g)
    for _ in range(rng.choice([1, 1, 2])):
        k = rng.choice(list(GENES)); h[k] = rng.choice(GENES[k])
    return h
def cross(a, b, rng): return {k: (a if rng.random() < 0.5 else b)[k] for k in GENES}

def main():
    engine, tb, out = sys.argv[1], sys.argv[2], sys.argv[3]
    gens = int(sys.argv[4]) if len(sys.argv) > 4 else 15
    pop = int(sys.argv[5]) if len(sys.argv) > 5 else 24
    rng = random.Random(int(sys.argv[6]) if len(sys.argv) > 6 else 1)
    os.makedirs(out, exist_ok=True)
    seen = {}
    log = open(os.path.join(out, 'log.jsonl'), 'a')
    base = dict(K=6, orders='0', maxsub=0, rho=0, TL=1, trysimp=0)
    batch = [base, dict(base, K=2)] + [random_genome(rng) for _ in range(pop - 2)]
    with Pool(min(11, os.cpu_count() or 2)) as P:
        for gen in range(gens):
            todo = [g for g in batch if key(g) not in seen]
            for r in P.map(evaluate, [(engine, tb, g) for g in todo]):
                seen[key(r['genome'])] = r; r['gen'] = gen
                log.write(json.dumps(r) + '\n'); log.flush()
            ranked = sorted(seen.values(), key=lambda r: r['fit'])
            best = ranked[0]
            print('gen %d: evaluated %d, best fit %.4f %s | %s' % (gen, len(seen), best['fit'], best['genome'],
                  ' '.join('%s:%.2f' % (f, best['fam'][f]['slope']) for f in FAMS) if best['fam'] else ''), flush=True)
            elite = ranked[:8]
            def tour():
                c = rng.sample(ranked[:max(16, pop)], 3); return min(c, key=lambda r: r['fit'])['genome']
            batch, tries = [], 0
            while len(batch) < pop and tries < 50 * pop:
                tries += 1
                child = mutate(cross(tour(), tour(), rng), rng) if rng.random() < 0.6 else mutate(tour(), rng)
                if key(child) not in seen and child not in batch: batch.append(child)
    ranked = sorted(seen.values(), key=lambda r: r['fit'])
    json.dump(ranked[:20], open(os.path.join(out, 'leaderboard.json'), 'w'), indent=1)
    print('top 5:')
    for r in ranked[:5]:
        print(' %.4f %s' % (r['fit'], r['genome']))
        for f in FAMS: print('    %-10s slope %.3f rounds %s' % (f, r['fam'][f]['slope'], r['fam'][f]['rounds']))

if __name__ == '__main__':
    main()
