import itertools, subprocess, sys, random, os
D = sys.argv[1]; sys.path.insert(0, D)
import ref_check as R
def dump_and_check(jl, n, role, d, extra_spine=True):
    arcs = R.pages(jl, n, role, d)
    if extra_spine: arcs += [(i - 1, i, 1) for i in range(1, n + 1)]
    fn = os.path.join(D, 'arcs.txt')
    with open(fn, 'w') as f:
        for a, b, p in arcs: f.write(f'{a} {b} {p}\n')
    out = subprocess.run([os.path.join(D, 'brute'), fn], capture_output=True, text=True).stdout.split()
    return int(out[0]), int(out[1]), int(out[2])
tot_bad = 0; tot_pairs = 0; cnt = 0; maxn = 0
Gmax = int(sys.argv[2])
for G in range(2, Gmax + 1):
    for combo in itertools.product(*[list(itertools.product(range(g), repeat=2)) for g in range(2, G + 1)]):
        ab = {g: combo[g - 2] for g in range(2, G + 1)}
        P = R.slot_prog(ab); L0, types = R.build_array(G + 2, P)
        jl, n, o, role, d = R.compile_phi(L0, types, 2 * G)
        na, pr, bad = dump_and_check(jl, n, role, d)
        tot_bad += bad; tot_pairs += pr; cnt += 1; maxn = max(maxn, n)
print(f'C brute force, all NOR circuits G<= {Gmax}: {cnt} instances, max n={maxn}, same-page pairs tested={tot_pairs}, crossings={tot_bad}')
# adversarial larger ones
fams = {'wide G=8': {g: (0, 1) for g in range(2, 9)}, 'fanout G=8': {**{2: (1, 1)}, **{g: (2, 2) for g in range(3, 9)}},
        'chain-prev-w0 G=8': {g: (0, g - 1) for g in range(2, 9)}, 'far G=9': {g: (g - 1, 1) for g in range(2, 10)}}
for name, ab in fams.items():
    G = max(ab); P = R.slot_prog(ab); L0, types = R.build_array(G + 2, P)
    jl, n, o, role, d = R.compile_phi(L0, types, 2 * G)
    print(name, 'n=%d arcs=%d pairs=%d crossings=%d' % ((n,) + dump_and_check(jl, n, role, d)))
