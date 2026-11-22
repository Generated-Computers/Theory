"""Exhaustive check of the switch characterisation of the relevance-pruned depth (Lemma kpr-switch).

For every parent array with n <= 8 and its trace x, with D the min-max depth of Definition kpr:
  (1) D obeys the forward recursion
        relevant reset          D(i) = 1 + D(j_i)
        irrelevant reset        D(i) = min(D(i-1), 1 + D(j_i))
        relevant non-reset, not a NOT gate   D(i) = max(D(i-1), 1 + D(j_i))
        otherwise               D(i) = D(i-1),
      for 2 <= i <= n, and D(1) = 1 (gate 1 is a NOT gate);
  (2) for every t >= 1 and i:  D(i) >= t+1  iff  some relevant non-NOT gate a <= i has D(j_a) >= t
      and every reset g in (a, i] has D(j_g) >= t;
  (3) the same statement for the Kleene-prefix depth d, with "relevant non-NOT" replaced by "non-NOT";
  (4) the single-anchor relaxations D_last and D_rel of Remark rem:kpr, defined from their anchor
      (last reset, resp. last relevant reset), equal the forward recursions in kpr_relax.c and are >= D.
"""
import itertools, sys
sys.path.insert(0, __import__("os").path.dirname(__file__))
from kpr_check import trace, depth

def kp_depth(j, x):
    n = len(j) - 1; d = [0] * (n + 1)
    for i in range(1, n + 1):
        r = max([k for k in range(2, i + 1) if j[k] != k - 1 and x[j[k]] == 1], default=0)
        d[i] = 1 + max([d[j[k]] for k in range(max(r, 1), i + 1) if j[k] != k - 1], default=0)
    return d

def switch(j, x, D, i, t, allowed):
    for a in range(1, i + 1):
        if allowed(a) and D[j[a]] >= t and all(D[j[g]] >= t for g in range(a + 1, i + 1)
                                               if j[g] != g - 1 and x[j[g]] == 1):
            return True
    return False

def relax_def(j, x, kind):
    n = len(j) - 1; E = [0] * (n + 1)
    for i in range(1, n + 1):
        hits = [k for k in range(2, i + 1) if j[k] != k - 1 and x[j[k]] == 1]
        if kind == "rel": hits = [k for k in hits if x[k - 1] == 0]
        r = hits[-1] if hits else 0
        vals = ([E[j[r]]] if r >= 1 else []) + [E[j[k]] for k in range(r + 1, i + 1) if x[k - 1] == 0 and j[k] != k - 1]
        E[i] = 1 + max(vals, default=0)
    return E

def relax_fwd(j, x, kind):
    n = len(j) - 1; d = [0] * (n + 1); m = 0
    for i in range(1, n + 1):
        q = j[i]; isnot = q == i - 1; hit = not isnot and x[q] == 1; rel = x[i - 1] == 0
        if (hit and kind == "last") or (hit and rel): m = d[q]
        elif rel and not isnot and not hit: m = max(m, d[q])
        d[i] = 1 + m
    return d

def main(nmax):
    count = 0
    for n in range(1, nmax + 1):
        for tail in itertools.product(*[range(k) for k in range(2, n + 1)]):
            j = ([0, 0] + list(tail))[:n + 1]
            x = trace(j); D = depth(j, x); d = kp_depth(j, x)
            for i in range(1, n + 1):
                q = j[i]; isnot = q == i - 1; hit = not isnot and x[q] == 1; rel = x[i - 1] == 0
                if hit and rel: f = 1 + D[q]
                elif hit: f = min(D[i - 1], 1 + D[q])
                elif rel and not isnot: f = max(D[i - 1], 1 + D[q])
                else: f = D[i - 1] if i >= 2 else 1
                assert f == D[i], (j, i, "recursion")
                fd = (1 + d[q] if hit else max(d[i - 1], 1 + d[q]) if not isnot else d[i - 1]) if i >= 2 else 1
                assert fd == d[i], (j, i, "recursion for d")
                for t in range(1, n + 1):
                    rel_nonnot = lambda a: j[a] != a - 1 and x[a - 1] == 0
                    nonnot = lambda a: j[a] != a - 1
                    assert (D[i] >= t + 1) == switch(j, x, D, i, t, rel_nonnot), (j, i, t, "switch KPR")
                    assert (d[i] >= t + 1) == switch(j, x, d, i, t, nonnot), (j, i, t, "switch KP")
            for kind in ("last", "rel"):
                E = relax_def(j, x, kind)
                assert E == relax_fwd(j, x, kind) and all(a >= b for a, b in zip(E, D)), (j, kind)
            count += 1
    print(f"switch characterisation, forward recursion and relaxations verified on all {count} parent arrays with n <= {nmax}")

if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 8)
