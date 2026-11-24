#!/usr/bin/env python3
"""Breadth-first search that found the 3-column gadgets (for reproducibility).
States are 4-tuples of truth tables over (u, v); columns 2i, 2i+1, 2i+2, 2i+3 start
as (u, 0, v, 0). Moves per column: N C X Y R O, never reading outside the 4 columns."""
import itertools
from collections import deque
FULL = 15; U = 0b1100; V = 0b1010
def opts(st, s, odd):
    o = s - 1 if odd else s + 1; a = st[s]; c = [('N', FULL & ~a), ('C', a)]
    if 0 <= o < len(st):
        b = st[o]; c += [('X', FULL & ~b), ('Y', b), ('R', FULL & ~(a | b)), ('O', a | b)]
    return c
def bfs(start, accept, maxdepth=8):
    seen = {(start, 0): None}; q = deque([(start, 0, 0)])
    while q:
        st, par, dep = q.popleft()
        if dep >= maxdepth: continue
        for combo in itertools.product(*[opts(st, s, par == 0) for s in range(4)]):
            ns = tuple(c[1] for c in combo); mv = ''.join(c[0] for c in combo)
            if par == 1 and accept(ns):
                path = [mv]; key = (st, par)
                while seen[key] is not None:
                    prev, m = seen[key]; path.append(m); key = prev
                return path[::-1]
            if (ns, 1 - par) not in seen:
                seen[(ns, 1 - par)] = ((st, par), mv); q.append((ns, 1 - par, dep + 1))
start = (U, 0, V, 0)
rest = lambda st: st[1] == 0 and st[3] == 0
print('COPY', bfs(start, lambda st: rest(st) and st[0] == U and st[2] == U))
print('NOR ', bfs(start, lambda st: rest(st) and st[0] == FULL & ~(U | V)))
print('SWAP', bfs(start, lambda st: rest(st) and st[0] == V and st[2] == U))
