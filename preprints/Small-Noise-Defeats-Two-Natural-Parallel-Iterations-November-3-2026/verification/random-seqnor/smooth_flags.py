"""Monte Carlo test of Lemma 9.6 and of the flag argument in Theorem 9.7 (paper Section 9).

Compiles random NOR circuits with Comp' (padding of N(0,0) gadgets, cells = ternary trees of N leaves
and 6-gate M' majorities in post-order), smooths at noise eps, and checks on every run:
  (1) Lemma 9.6: psi_{g-1} >= 0.19 for all g >= g_* = 400 ln(n+1) + 500;
  (2) the coupling: with f_g, h_g and auxiliary uniforms U_g as in the proof, every effective hit
      (pi_g = 1 and x[rho_g] != x[j_g]) has B_g = 1, and the empirical flag rate matches eps * h_g;
  (3) Step 1 with flags: every node whose output is wrong satisfies D(nu), where
      D(leaf) = flagged or an input cell is bad, D(internal) = flagged or >= 2 children with D.
usage: python3 -I smooth_flags.py
"""
import math, random

def run(s, m, h, eps, rng):
    gu, gv, val = [None], [None], [None]
    for t in range(1, s + 1):
        ch = lambda: rng.choice(['c0', 'c1'] + list(range(1, t)))
        gu.append(ch()); gv.append(ch())
        v = lambda u: 0 if u == 'c0' else 1 if u == 'c1' else val[u]
        val.append(int(not (v(gu[t]) or v(gv[t]))))
    cells = s * m * (4 * 3 ** h + 6 * (3 ** h - 1) // 2)
    est = 1 + cells + 4 * 3000
    P = math.ceil((400 * math.log(est + 1) + 500) / 4) + 2
    j = [None, 0]
    for _ in range(P):
        for p in (0, 0, 1, 0): j.append(p)
    gstar_pos = len(j)                       # first cell gate
    out, nodes = {}, []                      # node: (kind, gates, out_pos, children/inputs, cell)
    def o(u, r): return 1 if u == 'c0' else 0 if u == 'c1' else out[(u, r)]
    def tree(t, lev, cell):
        if lev == 0:
            ra, rb = rng.randrange(m), rng.randrange(m)
            a, b = o(gu[t], ra), o(gv[t], rb)
            k = len(j); j.extend((0, a, 1, b))
            nodes.append(('leaf', list(range(k, k + 4)), k + 3, ((gu[t], ra), (gv[t], rb)), cell))
            return len(nodes) - 1
        kids = [tree(t, lev - 1, cell) for _ in range(3)]
        a, b, c = (nodes[x][2] for x in kids)
        k = len(j); assert c == k - 1
        j.extend((a, a, c, k + 1, b, k))
        nodes.append(('maj', list(range(k, k + 6)), k + 5, kids, cell))
        return len(nodes) - 1
    roots = {}
    for t in range(1, s + 1):
        for l in range(m):
            r = tree(t, h, (t, l)); roots[(t, l)] = r; out[(t, l)] = nodes[r][2]
    n = len(j) - 1
    pi = [0, 0] + [int(rng.random() < eps) for _ in range(2, n + 1)]
    rho = [0, 0] + [rng.randrange(i) for i in range(2, n + 1)]
    U = [rng.random() for _ in range(n + 1)]
    jt = [None, 0] + [rho[i] if pi[i] else j[i] for i in range(2, n + 1)]
    x = [1] + [0] * n; ones = [1] + [0] * n          # ones[g] = O_g
    for i in range(1, n + 1):
        x[i] = int(not (x[i - 1] or x[jt[i]])); ones[i] = ones[i - 1] + x[i]
    gstar = 400 * math.log(n + 1) + 500
    assert gstar <= gstar_pos
    dens_ok = all(ones[g - 1] / g >= 0.19 for g in range(math.ceil(gstar), n + 1))
    B = [0] * (n + 1); eff = 0; flags = 0; expect = 0.0
    for g in range(gstar_pos, n + 1):
        psi = ones[g - 1] / g
        f = psi if x[j[g]] == 0 else 1 - psi
        hg = 0.501 if j[g] == 1 else 0.81
        expect += eps * hg
        if f <= hg:
            B[g] = int(pi[g] == 1 and (x[rho[g]] != x[j[g]] or U[g] < (hg - f) / (1 - f)))
        else:
            B[g] = int(pi[g] == 1 and U[g] < hg)
        flags += B[g]
        if pi[g] and x[rho[g]] != x[j[g]]:
            eff += 1
            if dens_ok: assert B[g] == 1
    bad = {(t, l): x[out[(t, l)]] != val[t] for t in range(1, s + 1) for l in range(m)}
    D = [False] * len(nodes); wrong_nodes = 0
    for idx, (kind, gates, op, ch, cell) in enumerate(nodes):
        flagged = any(B[g] for g in gates)
        if kind == 'leaf':
            D[idx] = flagged or any(u not in ('c0', 'c1') and bad[(u, r)] for u, r in ch)
        else:
            D[idx] = flagged or sum(D[c] for c in ch) >= 2
        if dens_ok and x[op] != val[cell[0]]:
            wrong_nodes += 1
            assert D[idx], ("wrong node without D", idx, kind)
    return dens_ok, eff, flags, expect, wrong_nodes, max(sum(bad[(t, l)] for l in range(m)) / m for t in range(1, s + 1))

rng = random.Random(7)
for eps, reps in ((1 / 64, 6), (0.04, 6), (0.08, 4)):
    tot = [0, 0, 0.0, 0]; dens = 0; worst = 0
    for _ in range(reps):
        d, eff, fl, ex, wr, wb = run(12, 10, 3, eps, rng)
        dens += d; tot[0] += eff; tot[1] += fl; tot[2] += ex; tot[3] += wr; worst = max(worst, wb)
    print(f"eps={eps:.4f}: density event held in {dens}/{reps} runs; effective hits {tot[0]}, flags {tot[1]} "
          f"(expected {tot[2]:.0f}); wrong nodes {tot[3]}, all with D; worst bundle {worst:.2f} bad")
    assert dens == reps and abs(tot[1] - tot[2]) <= 4 * math.sqrt(tot[2]) + 5
print("Lemma 9.6 and the flag argument of Theorem 9.7 pass on all runs")
