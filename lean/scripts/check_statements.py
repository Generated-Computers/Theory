# For each Comparator config, compare the fingerprints (#dump_stmt) of the listed theorems and
# their GC.* dependencies in the challenge module and in the solution module.
# usage (from lean/): python3 scripts/check_statements.py . [+only-substring | skip-substring]
import glob, json, os, re, subprocess, sys
M = sys.argv[1]
skip = sys.argv[2] if len(sys.argv) > 2 else None
os.chdir(M)
cfgs = sorted(glob.glob('ComparatorChallenges/*.json'))
if skip and skip[0] == '+': cfgs = [c for c in cfgs if skip[1:] in open(c).read()]
elif skip: cfgs = [c for c in cfgs if skip not in open(c).read()]
mods = sorted({json.load(open(c))['challenge_module'] for c in cfgs})
r = subprocess.run(['lake', 'build', 'StmtDump'] + mods, capture_output=True, text=True)
if r.returncode: print(r.stdout[-3000:], r.stderr[-2000:]); sys.exit('challenge build failed')
def dump(mod, names, tag):
    f = 'StmtCheck_%s.lean' % tag
    open(f, 'w').write('import StmtDump\nimport %s\n#dump_stmt %s\n' % (mod, ' '.join(names)))
    out = subprocess.run(['lake', 'env', 'lean', f], capture_output=True, text=True).stdout
    os.remove(f)
    return sorted(re.findall(r'STMT .*', out)), out
bad = 0
for c in cfgs:
    j = json.load(open(c)); names = j['theorem_names'] + j.get('definition_names', [])
    a, oa = dump(j['challenge_module'], names, 'a'); b, ob = dump(j['solution_module'], names, 'b')
    thm_lines = [l for l in a if l.split()[1] in names]
    ok = a == b and len(thm_lines) == len(names) and not any('MISSING' in x or 'AXIOM' in x for x in a + b)
    bad += not ok
    print('%-50s %s  (%d theorems, %d constants)' % (os.path.basename(c), 'MATCH' if ok else 'MISMATCH', len(names), len(a)))
    if not ok:
        for l in sorted(set(a) ^ set(b))[:12]: print('   ', 'challenge' if l in a else 'solution ', l)
        if not a: print(oa[-1500:])
print('mismatches:', bad, 'of', len(cfgs))
