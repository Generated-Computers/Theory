import sys, subprocess, os
D = sys.argv[1]; sys.path.insert(0, D)
import ref_check as R
ab = {2: (0, 1), 3: (2, 0), 4: (3, 2)}
G = 4; P = R.slot_prog(ab); L0, types = R.build_array(G + 2, P)
jl, n, o, role, d = R.compile_phi(L0, types, 2 * G)
fn = os.path.join(D, 'arcs_ctrl.txt')
for label, f in (('all on one page', lambda a, b, p, r: 1),
                 ('arc into c on page by parity, arc into c+4 swapped', lambda a, b, p, r: (3 - p) if (r != 'short' and r != 'tail' and (b - (2 + 2 * len(L0))) % 8 == 4) else p)):
    with open(fn, 'w') as fh:
        for (a, b, p) in R.pages(jl, n, role, d): fh.write(f'{a} {b} {f(a, b, p, role[b])}\n')
    print(label, subprocess.run([os.path.join(D, 'brute'), fn], capture_output=True, text=True).stdout.strip())
