#!/usr/bin/env python3
"""Independent referee checker for the two-page construction (manuscript 006a).
Written from the text of main.tex only (Sections 3, 7), not from code/.

Pipeline: CVP (and/or/not) -> NOR circuit (Lemma 3.1) -> slot program (Lemma 7.3)
-> array via Table 1 gadgets (Lemma 7.5) -> parent array Phi (Sec. 7.3, Table 2)
-> direct Sequential NOR trace; two-page assignment of Thm 7.11; brute-force
pairwise crossing test on each page; independent bipartiteness test of the
crossing graph (pg <= 2 regardless of the paper's assignment) on small instances.
"""
import itertools, random, sys

def nor(a, b): return 1 - (a | b)

# ---------------- Sequential NOR, directly from (1) ----------------
def trace(j, n):
    x = [1] + [None] * n
    for i in range(1, n + 1):
        assert 0 <= j[i] < i, ("bad parent", i, j[i])
        x[i] = nor(x[i - 1], x[j[i]])
    return x

# ---------------- NOR circuits ----------------
def eval_nor_circuit(ab):            # ab[g] = (a_g, b_g) for g >= 2
    G = max(ab)
    w = [1, 0] + [None] * (G - 1)
    for g in range(2, G + 1):
        a, b = ab[g]; assert a < g and b < g
        w[g] = nor(w[a], w[b])
    return w

def cvp_to_nor(cvp):
    """cvp: list of gates in topo order; entries ('c',bit) | ('not',i) | ('and',i,k) | ('or',i,k)
    referencing earlier entries. Lemma 3.1 local replacement."""
    ab = {}; nxt = [2]; where = {}
    def new(a, b):
        g = nxt[0]; ab[g] = (a, b); nxt[0] += 1; return g
    for idx, gate in enumerate(cvp):
        if gate[0] == 'c': where[idx] = 0 if gate[1] == 1 else 1
        elif gate[0] == 'not': a = where[gate[1]]; where[idx] = new(a, a)
        elif gate[0] == 'or':
            a, b = where[gate[1]], where[gate[2]]; u = new(a, b); where[idx] = new(u, u)
        else:
            a, b = where[gate[1]], where[gate[2]]; u = new(a, a); v = new(b, b); where[idx] = new(u, v)
    # output must be the last gate w_G; add double negation if the output is a constant/earlier gate
    out = where[len(cvp) - 1]
    if out != nxt[0] - 1 or out < 2:
        u = new(out, out); new(u, u)
    if nxt[0] - 1 < 2: new(1, 1)
    return ab

def eval_cvp(cvp):
    v = []
    for gate in cvp:
        if gate[0] == 'c': v.append(gate[1])
        elif gate[0] == 'not': v.append(1 - v[gate[1]])
        elif gate[0] == 'and': v.append(v[gate[1]] & v[gate[2]])
        else: v.append(v[gate[1]] | v[gate[2]])
    return v[-1]

# ---------------- slot programs, Lemma 7.3 ----------------
def slot_prog(ab):
    G = max(ab); P = []
    for g in range(2, G + 1):
        a, b = sorted(ab[g])
        for i in range(g - 1, a, -1): P.append(('SWAP', i))
        P.append(('COPY', a))
        for i in range(a + 1, g): P.append(('SWAP', i))
        for i in range(g, b, -1): P.append(('SWAP', i))
        P.append(('COPY', b))
        for i in range(b + 1, g + 1): P.append(('SWAP', i))
        P.append(('NOR', g))
    return P

def run_slot(P, z):
    z = list(z)
    for op, i in P:
        if op == 'SWAP': z[i], z[i + 1] = z[i + 1], z[i]
        elif op == 'COPY': z[i + 1] = z[i]
        else: z[i] = nor(z[i], z[i + 1])
    return z

# ---------------- Table 1, transcribed with the claimed values ----------------
# claimed values as functions of (u,v)
NOT = lambda f: (lambda u, v: 1 - f(u, v))
U = lambda u, v: u; V = lambda u, v: v; Z = lambda u, v: 0; ONE = lambda u, v: 1
TABLE1 = {
 'COPY': [(('N', NOT(U)), ('X', NOT(U)), ('N', NOT(V))),
          (('N', U), ('N', U), ('N', V)),
          (('N', NOT(U)), ('N', NOT(U)), ('Y', U)),
          (('N', U), ('R', Z), ('C', U))],
 'NOR':  [(('N', NOT(U)), ('N', ONE), ('N', NOT(V))),
          (('N', U), ('X', V), ('N', V)),
          (('N', NOT(U)), ('O', lambda u, v: u | v), ('N', NOT(V))),
          (('X', lambda u, v: nor(u, v)), ('R', Z), ('N', V))],
 'SWAP': [(('N', NOT(U)), ('X', NOT(U)), ('N', NOT(V))),
          (('N', U), ('R', lambda u, v: u & v), ('C', NOT(V))),
          (('N', NOT(U)), ('C', lambda u, v: u & v), ('R', lambda u, v: (1 - u) & v)),
          (('R', lambda u, v: u & (1 - v)), ('O', V), ('N', lambda u, v: u | (1 - v))),
          (('C', lambda u, v: u & (1 - v)), ('R', lambda u, v: (1 - u) & (1 - v)), ('N', lambda u, v: (1 - u) & v)),
          (('R', V), ('C', lambda u, v: (1 - u) & (1 - v)), ('C', lambda u, v: (1 - u) & v)),
          (('N', NOT(V)), ('N', lambda u, v: u | v), ('O', lambda u, v: 1 - u)),
          (('N', V), ('R', Z), ('N', U))],
}

def sigma(t, s): return s - 1 if t % 2 == 1 else s + 1

def cell_val(T, a, b):
    return {'N': 1 - a, 'C': a, 'X': None if b is None else 1 - b, 'Y': b,
            'R': None if b is None else nor(a, b), 'O': None if b is None else (a | b)}[T]

def eval_array(L0, types):
    k = len(L0); V = [list(L0)]
    for t in range(1, len(types) + 1):
        prev = V[-1]; row = []
        for s in range(k):
            T = types[t - 1][s]; o = sigma(t, s)
            if T in 'XYRO': assert 0 <= o < k, ("type reads outside", t, s, T)
            row.append(cell_val(T, prev[s], prev[o] if 0 <= o < k else None))
        V.append(row)
    return V

def check_table1():
    """Check every entry of Table 1 (type and value) inside a width-7 array with junk outside."""
    bad = 0
    for name, rows in TABLE1.items():
        for u, v, j1, j2, sup in itertools.product([0, 1], repeat=5):
            # columns: 0 junk, 1 junk(support 2i-1), 2:u, 3: support(sup), 4: v, 5 support 0, 6 junk
            L0 = [j1, j2, u, sup, v, 0, j1]
            types = [['C', 'C'] + [r[0][0], r[1][0], r[2][0]] + ['C', 'C'] for r in rows]
            Vals = eval_array(L0, types)
            for t, r in enumerate(rows, 1):
                for c in range(3):
                    if sup == 0 and Vals[t][2 + c] != r[c][1](u, v): bad += 1
            want = {'COPY': (u, 0, u), 'NOR': (nor(u, v), 0, v), 'SWAP': (v, 0, u)}[name]
            if tuple(Vals[-1][2:5]) != want: bad += 1          # also with support != 0
            if Vals[-1][0:2] != [j1, j2] or Vals[-1][5:] != [0, j1]: bad += 1
        # no read outside: odd row col 2i type N/C, even row col 2i+2 type N/C
        for t, r in enumerate(rows, 1):
            if t % 2 == 1 and r[0][0] not in 'NC': bad += 1
            if t % 2 == 0 and r[2][0] not in 'NC': bad += 1
    return bad

def build_array(M, P):
    k = 2 * M; L0 = [0] * k; L0[0] = 1
    types = []
    for op, i in P:
        assert 0 <= i and 2 * i + 2 <= k - 1
        for r in TABLE1[op]:
            row = ['C'] * k
            row[2 * i], row[2 * i + 1], row[2 * i + 2] = r[0][0], r[1][0], r[2][0]
            types.append(row)
    return L0, types

# ---------------- Section 7.3 compilation ----------------
NORTYPE = set('NXR'); ORTYPE = set('CYO')
def sources(T, t, s):
    sg = sigma(t, s)
    return {'N': (s, s), 'C': (s, s), 'X': (sg, sg), 'Y': (sg, sg), 'R': (s, sg), 'O': (s, sg)}[T]

def compile_phi(L0, types, sout):
    k = len(L0); d = len(types)
    j = {1: 0}; o = {}; role = {1: 'short'}; layer_of_arc = {}
    for s in range(k):
        c = 2 + 2 * s
        j[c] = c - 1; j[c + 1] = c; role[c] = role[c + 1] = 'short'
        o[(0, s)] = c if L0[s] == 1 else c + 1
    for t in range(1, d + 1):
        order = list(range(k - 1, -1, -1)) if t % 2 == 1 else list(range(k))
        for e, s in enumerate(order):
            c = 2 + 2 * k + 8 * (k * (t - 1) + e)
            T = types[t - 1][s]; pi, ka = sources(T, t, s)
            p, q = o[(t - 1, pi)], o[(t - 1, ka)]
            blk = [p, c, c, c, q, c + 4, c + 5, c + 5]
            for r in range(8):
                assert c + r not in j; j[c + r] = blk[r]
                role[c + r] = 'short'
            role[c] = ('trans', t); role[c + 4] = ('trans', t)
            o[(t, s)] = c + 4 if T in NORTYPE else c + 5
    m = 2 + 2 * k + 8 * k * d
    assert m not in j
    j[m] = o[(d, sout)]; j[m + 1] = j[m + 2] = j[m + 3] = m
    role[m] = 'tail'; role[m + 1] = role[m + 2] = role[m + 3] = 'short'
    n = m + 3
    assert sorted(j) == list(range(1, n + 1)), "positions not exactly 1..n"
    jl = [None] + [j[i] for i in range(1, n + 1)]
    return jl, n, o, role, d

def pages(jl, n, role, d):
    """Theorem 7.11 assignment.  Returns list of (a,b,page)."""
    arcs = []
    for i in range(1, n + 1):
        r = role[i]
        if r == 'short': pg = 1
        elif r == 'tail': pg = 1 if d % 2 == 0 else 2
        else: pg = 1 if r[1] % 2 == 1 else 2
        arcs.append((jl[i], i, pg))
    return arcs

def crosses(a, b, c, e):
    return a < c < b < e or c < a < e < b

def brute_same_page(arcs, also_spine=True):
    """Every pair of arcs on the same page, pure brute force. Spine arcs (i-1,i)
    are added on page 1 too (they cannot cross, but we test it)."""
    A = list(arcs)
    if also_spine:
        n = max(b for _, b, _ in A)
        A += [(i - 1, i, 1) for i in range(1, n + 1)]
    by = {}
    for a, b, p in A: by.setdefault(p, []).append((a, b))
    bad = 0
    for p, L in by.items():
        L = list(set(L))
        for x in range(len(L)):
            a, b = L[x]
            for y in range(x + 1, len(L)):
                c, e = L[y]
                if (a < c < b < e) or (c < a < e < b): bad += 1
    return bad

def stack_check(arcs):
    """O(N log N) independent test that each page is non-crossing (bracket matching)."""
    by = {}
    for a, b, p in arcs:
        if b - a > 1: by.setdefault(p, set()).add((a, b))
    for p, S in by.items():
        ev = []
        for a, b in S:
            ev.append((b, 0, -a, a, b))   # close first at a point, inner (larger a) first
            ev.append((a, 1, -b, a, b))   # open: outer (larger b) first
        ev.sort()
        st = []
        for _, kind, _, a, b in ev:
            if kind == 1: st.append((a, b))
            else:
                if not st or st[-1] != (a, b): return False
                st.pop()
    return True

def bipartite_crossing_graph(jl, n):
    """pg(j) <= 2 iff crossing graph bipartite; independent of the paper's assignment."""
    A = sorted(set((jl[i], i) for i in range(1, n + 1) if i - jl[i] > 1))
    adj = {x: [] for x in A}
    for x in range(len(A)):
        a, b = A[x]
        for y in range(x + 1, len(A)):
            c, e = A[y]
            if c >= b: break
            if a < c < b < e: adj[A[x]].append(A[y]); adj[A[y]].append(A[x])
    col = {}
    for s in A:
        if s in col: continue
        col[s] = 0; stk = [s]
        while stk:
            u = stk.pop()
            for w in adj[u]:
                if w not in col: col[w] = 1 - col[u]; stk.append(w)
                elif col[w] == col[u]: return False, sum(len(v) for v in adj.values()) // 2
    return True, sum(len(v) for v in adj.values()) // 2

# ---------------- end-to-end ----------------
def run_circuit(ab, brute_limit=4000, bip_limit=6000):
    G = max(ab); w = eval_nor_circuit(ab); M = G + 2
    P = slot_prog(ab)
    z = run_slot(P, [1] + [0] * (M - 1))
    ok_slot = z[:G + 1] == w[:G + 1]
    L0, types = build_array(M, P)
    V = eval_array(L0, types)
    ok_arr = all(V[-1][2 * i] == w[i] for i in range(G + 1)) and all(V[-1][2 * i + 1] == 0 for i in range(M))
    jl, n, o, role, d = compile_phi(L0, types, 2 * G)
    x = trace(jl, n)
    ok_val = x[n] == w[G] and all(x[o[(t, s)]] == V[t][s] for (t, s) in o)
    arcs = pages(jl, n, role, d)
    res = dict(G=G, n=n, slot=ok_slot, arr=ok_arr, val=ok_val, stack=stack_check(arcs))
    if n <= brute_limit: res['brute'] = brute_same_page(arcs)
    if n <= bip_limit: res['bip'] = bipartite_crossing_graph(jl, n)[0]
    return res

def run_array(L0, types, sout, brute=True):
    V = eval_array(L0, types)
    jl, n, o, role, d = compile_phi(L0, types, sout)
    x = trace(jl, n)
    ok = x[n] == V[d][sout] and all(x[o[(t, s)]] == V[t][s] for (t, s) in o)
    arcs = pages(jl, n, role, d)
    r = dict(n=n, val=ok, stack=stack_check(arcs))
    if brute: r['brute'] = brute_same_page(arcs)
    return r, arcs, jl, n

if __name__ == '__main__':
    print('Table 1 entry mismatches:', check_table1())
