import itertools, random, sys, time
sys.path.insert(0, sys.argv[1])
import ref_check as R

rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 7)
T0 = time.time()
def summ(name, rs):
    keys = ['slot', 'arr', 'val', 'stack', 'bip']
    out = {kk: sum(1 for r in rs if kk in r and r[kk] is False) for kk in keys if any(kk in r for r in rs)}
    br = [r['brute'] for r in rs if 'brute' in r]
    print(f"{name}: {len(rs)} instances, max n={max(r['n'] for r in rs)}, failures={out}, "
          f"brute-checked={len(br)} same-page crossings={sum(br)}  [{time.time()-T0:.0f}s]", flush=True)

print('Table 1 entry mismatches:', R.check_table1())

# 1. exhaustive NOR circuits, G = 2, 3, 4
for G in (2, 3, 4):
    rs = []
    choices = [list(itertools.product(range(g), repeat=2)) for g in range(2, G + 1)]
    for combo in itertools.product(*choices):
        ab = {g: combo[g - 2] for g in range(2, G + 1)}
        rs.append(R.run_circuit(ab, brute_limit=3500 if G <= 3 else 0, bip_limit=6000 if G <= 3 else 0))
    summ(f'exhaustive NOR circuits G={G}', rs)

# 2. adversarial families
fams = {}
for G in (5, 8, 11):
    fams[f'chain-prev-prev G={G}'] = {g: (g - 1, g - 1) for g in range(2, G + 1)}
    fams[f'chain-prev-w0 G={G}'] = {g: (0, g - 1) for g in range(2, G + 1)}
    fams[f'wide w0,w1 G={G}'] = {g: (0, 1) for g in range(2, G + 1)}
    fams[f'fanout gate2 G={G}'] = {**{2: (1, 1)}, **{g: (2, 1) for g in range(3, G + 1)}}
    fams[f'fanout gate2 both G={G}'] = {**{2: (1, 0)}, **{g: (2, 2) for g in range(3, G + 1)}}
    fams[f'far: g reads 1 and g-1 G={G}'] = {g: (g - 1, 1) for g in range(2, G + 1)}
    fams[f'alternating G={G}'] = {g: ((g - 2) // 2 * 2 if g > 2 else 0, g - 1) for g in range(2, G + 1)}
for name, ab in fams.items():
    r = R.run_circuit(ab, brute_limit=2500, bip_limit=12000)
    print(name, r, flush=True)

# 3. random CVP (and/or/not) -> NOR -> ...
rs = []
for _ in range(60):
    nin = rng.randint(1, 3); cvp = [('c', rng.randint(0, 1)) for _ in range(nin)]
    for _ in range(rng.randint(1, 3)):
        op = rng.choice(['and', 'or', 'not']); i = rng.randrange(len(cvp)); k2 = rng.randrange(len(cvp))
        cvp.append(('not', i) if op == 'not' else (op, i, k2))
    ab = R.cvp_to_nor(cvp)
    w = R.eval_nor_circuit(ab)
    assert w[max(ab)] == R.eval_cvp(cvp), ('Lemma 3.1 replacement wrong', cvp)
    if max(ab) <= 9:
        rs.append(R.run_circuit(ab, brute_limit=0, bip_limit=0))
summ('random CVP->NOR->Phi', rs)

# 4. random NOR circuits G up to 10 (stack check only for large)
rs = []
for _ in range(80):
    G = rng.randint(2, 10)
    ab = {g: (rng.randrange(g), rng.randrange(g)) for g in range(2, G + 1)}
    rs.append(R.run_circuit(ab, brute_limit=0, bip_limit=0))
summ('random NOR circuits G<=10', rs)

# 5. random arrays, brute force, several type distributions
def rand_array(k, d, alphabet):
    L0 = [rng.randint(0, 1) for _ in range(k)]
    types = [[rng.choice(alphabet if 0 <= R.sigma(t, s) < k else 'NC') for s in range(k)] for t in range(1, d + 1)]
    return L0, types
for alpha in ('NCXYRO', 'RO', 'XY', 'RX', 'OY', 'NR'):
    rs = []
    for _ in range(120):
        k = rng.randint(1, 10); d = rng.randint(1, 12)
        L0, types = rand_array(k, d, alpha)
        r, *_ = R.run_array(L0, types, rng.randrange(k), brute=True)
        rs.append(r)
    summ(f'random arrays types={alpha}', rs)

# 6. exhaustive small arrays
for (k, d) in ((2, 1), (2, 2), (2, 3), (3, 1), (3, 2), (1, 3)):
    rs = []
    cells = [(t, s) for t in range(1, d + 1) for s in range(k)]
    opts = [('NCXYRO' if 0 <= R.sigma(t, s) < k else 'NC') for (t, s) in cells]
    for L0 in itertools.product([0, 1], repeat=k):
        for combo in itertools.product(*opts):
            types = [[combo[(t - 1) * k + s] for s in range(k)] for t in range(1, d + 1)]
            for sout in range(k):
                r, *_ = R.run_array(list(L0), types, sout, brute=True)
                rs.append(r)
    summ(f'exhaustive arrays k={k} d={d}', rs)
print('done', time.time() - T0)
