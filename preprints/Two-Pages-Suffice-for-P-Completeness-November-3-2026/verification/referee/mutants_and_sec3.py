import itertools, random, sys
sys.path.insert(0, sys.argv[1])
import ref_check as R
rng = random.Random(11)

# ---- mutation tests: the checker must detect crossings when the construction is broken ----
def compile_variant(L0, types, sout, neighbour_first=False, no_serpentine=False):
    k = len(L0); d = len(types); j = {1: 0}; o = {}; role = {1: 'short'}
    for s in range(k):
        c = 2 + 2 * s; j[c] = c - 1; j[c + 1] = c; role[c] = role[c + 1] = 'short'
        o[(0, s)] = c if L0[s] else c + 1
    for t in range(1, d + 1):
        order = list(range(k)) if (no_serpentine or t % 2 == 0) else list(range(k - 1, -1, -1))
        for e, s in enumerate(order):
            c = 2 + 2 * k + 8 * (k * (t - 1) + e); T = types[t - 1][s]
            pi, ka = R.sources(T, t, s)
            if neighbour_first and T in 'RO': pi, ka = ka, pi
            p, q = o[(t - 1, pi)], o[(t - 1, ka)]
            for r, par in enumerate([p, c, c, c, q, c + 4, c + 5, c + 5]): j[c + r] = par; role[c + r] = 'short'
            role[c] = role[c + 4] = ('trans', t)
            o[(t, s)] = c + 4 if T in 'NXR' else c + 5
    m = 2 + 2 * k + 8 * k * d; j[m] = o[(d, sout)]; j[m + 1] = j[m + 2] = j[m + 3] = m
    role[m] = 'tail'; role[m + 1] = role[m + 2] = role[m + 3] = 'short'
    n = m + 3; jl = [None] + [j[i] for i in range(1, n + 1)]
    return jl, n, o, role, d

for label, kw in (('neighbour-first convention', dict(neighbour_first=True)),
                  ('no serpentine (all left-to-right)', dict(no_serpentine=True))):
    tot = 0; inst = 0; nonbip = 0; valbad = 0
    for _ in range(100):
        k = rng.randint(2, 8); d = rng.randint(1, 8)
        L0 = [rng.randint(0, 1) for _ in range(k)]
        types = [[rng.choice('NCXYRO' if 0 <= R.sigma(t, s) < k else 'NC') for s in range(k)] for t in range(1, d + 1)]
        sout = rng.randrange(k)
        jl, n, o, role, dd = compile_variant(L0, types, sout, **kw)
        V = R.eval_array(L0, types); x = R.trace(jl, n)
        if x[n] != V[d][sout]: valbad += 1
        arcs = R.pages(jl, n, role, dd); c = R.brute_same_page(arcs); tot += c; inst += (c > 0)
        if n < 2500 and not R.bipartite_crossing_graph(jl, n)[0]: nonbip += 1
    print(f'MUTANT {label}: instances with same-page crossings {inst}/100, total {tot}, '
          f'non-bipartite crossing graph {nonbip}, value errors {valbad}')

# tail on the page of layer d
tot = 0
for _ in range(100):
    k = rng.randint(2, 8); d = rng.randint(1, 8)
    L0 = [rng.randint(0, 1) for _ in range(k)]
    types = [[rng.choice('NCXYRO' if 0 <= R.sigma(t, s) < k else 'NC') for s in range(k)] for t in range(1, d + 1)]
    jl, n, o, role, dd = R.compile_phi(L0, types, rng.randrange(k))
    arcs = [(a, b, (1 if d % 2 == 1 else 2) if role[b] == 'tail' else p) for a, b, p in R.pages(jl, n, role, dd)]
    tot += R.brute_same_page(arcs) > 0
print('MUTANT tail on layer-d page: instances with crossings', tot, '/100')

# ---- Section 3: five-cell reduction and Corollary 3.4 ----
def okhotin(ab):
    G = max(ab); pos = lambda w: w if w <= 1 else 5 * w - 5
    n = 5 * G - 1; j = [None] * (n + 1); j[1] = 0
    for w in range(2, G + 1):
        i1 = 5 * w - 8; a, b = ab[w]
        j[i1], j[i1 + 1], j[i1 + 2], j[i1 + 3], j[i1 + 4] = pos(a), 0, i1, pos(b), 0
    j[5 * G - 3], j[5 * G - 2], j[5 * G - 1] = pos(G), 0, 5 * G - 3
    return j, n, pos
bad = 0; cor_viol = []; cnt = 0
for G in range(2, 6):
    for combo in itertools.product(*[list(itertools.product(range(g), repeat=2)) for g in range(2, G + 1)]):
        ab = {g: combo[g - 2] for g in range(2, G + 1)}
        j, n, pos = okhotin(ab); x = R.trace(j, n); w = R.eval_nor_circuit(ab); cnt += 1
        if x[n] != w[G] or any(x[pos(g)] != w[g] for g in range(G + 1)): bad += 1
        v = [i for i in range(2, n + 1) if j[i] == i - 1]
        if v and len(cor_viol) < 3: cor_viol.append((ab, v))
        elif v: cor_viol.append(None)
print('five-cell reduction: circuits', cnt, 'value errors', bad)
print('Corollary 3.4 premise j_i != i-1 violated in', len(cor_viol), 'circuits; examples', [c for c in cor_viol[:3]])
