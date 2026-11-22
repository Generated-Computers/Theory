# Print the axioms of every main theorem listed in the Comparator configurations.
# usage (from lean/, after `lake build`): python3 scripts/axioms.py
import glob, json, re, subprocess
names = []
for c in sorted(glob.glob('ComparatorChallenges/*.json')): names += json.load(open(c))['theorem_names']
mods = [l.split()[1] for l in open('GC.lean') if l.startswith('import ')]
open('AxiomCheck.lean', 'w').write(''.join('import %s\n' % m for m in mods) + ''.join('#print axioms %s\n' % n for n in names))
out = subprocess.run(['lake', 'env', 'lean', 'AxiomCheck.lean'], capture_output=True, text=True).stdout
ok = {'propext', 'Quot.sound', 'Classical.choice'}
bad = [l for l in out.splitlines() if 'depends on axioms' in l and not set(re.findall(r'\[(.*)\]', l)[0].split(', ')) <= ok]
print(len(names), 'theorems;', out.count('depends on axioms') + out.count('does not depend on any axioms'), 'reported;', len(bad), 'with other axioms')
for l in bad: print(l)
