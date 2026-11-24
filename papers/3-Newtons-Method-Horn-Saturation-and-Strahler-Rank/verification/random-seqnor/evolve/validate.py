# Validation of search results on a fresh test bed (other seed, sizes up to 131072), against the
# baselines KP, KPR, greedy substitution and anchored doubling (NOTE.md §5j).
# usage: python3 -I validate.py ENGINE_TT ENGINE_BDD TESTBED leaderboard.json [top]
import json, math, os, subprocess, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from evolve2 import run, command, slope

FAMS = ['emb-w2', 'emb-w8', 'emb-wsqrt', 'emb-rand', 'block32', 'lin2', 'uniform', 'emb1-w2', 'emb1-w4', 'emb1-w8',
        'block8', 'block32@0.3', 'emb1-w4@0.1']
SIZES = [2048, 8192, 32768, 131072]

def table(name, res):
    print(name)
    for f in FAMS:
        rows = [res.get('%s_%d.bin' % (f, s)) for s in SIZES]
        rows = [r for r in rows if r is not None]
        if len(rows) < 2: continue
        rs = [r['rounds'] if r['fin'] else -r['rounds'] for r in rows]
        xs = [math.log2(r['n']) for r in rows]; ys = [math.log2(abs(v)) for v in rs]
        errs = sum(r['err'] for r in rows)
        print('   %-10s rounds %-28s slope %.2f%s%s' % (f, rs, slope(xs, ys), '' if all(v > 0 for v in rs) else '  (negative = unfinished at cap)',
                                                      '  ERRORS %d' % errs if errs else ''))

def baseline(engine, files, mode):          # kp, kpr or newton
    out = subprocess.run([engine, mode, '2', '0', '0', '0', '0', '0', '1', '4'] + files, capture_output=True, text=True).stdout
    res = {}
    for line in out.split('\n'):
        p = line.split()
        if len(p) == 8: res[os.path.basename(p[0])] = dict(n=int(p[1]), rounds=int(p[2]), fin=1, known=1.0, err=0)
    return res

if __name__ == '__main__':
    import evolve2; evolve2.TIMEOUT = 6 * 3600
    eng = (sys.argv[1], sys.argv[2]); tb, lb = sys.argv[3], sys.argv[4]
    top = int(sys.argv[5]) if len(sys.argv) > 5 else 3
    files = [os.path.join(tb, '%s_%d.bin' % (f, s)) for f in FAMS for s in SIZES if os.path.exists(os.path.join(tb, '%s_%d.bin' % (f, s)))]
    for mode in ('kp', 'kpr', 'newton'): table('baseline ' + mode, baseline(eng[0], files, mode)); sys.stdout.flush()
    small = [f for f in files if not f.endswith('_131072.bin')]        # BDD runs skip the largest size (time)
    for name, g in (('greedy K=6', dict(engine='tt', K=6, orders='0', maxsub=0, rho=0, TL=1, trysimp=0)),
                    ('anchored K=12', dict(engine='tt', K=12, orders='4', maxsub=0, rho=0, TL=1, trysimp=0))):
        table(name, run(command(eng, g, files))); sys.stdout.flush()
    done = []
    for r in json.load(open(lb)):
        g = r['genome']
        if len(done) >= top or g in done: continue
        done.append(g)
        table('evolved %s (search fitness %.3f)' % (g, r['fit']), run(command(eng, g, small if g['engine'] == 'bdd' else files))); sys.stdout.flush()
