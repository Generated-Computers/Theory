import itertools, random

def compose(p, q):  # (p*q)(i) = p(q(i))  -- right-to-left
    return tuple(p[q[i]] for i in range(5))

def parity(p):
    s, seen = 0, [False]*5
    for i in range(5):
        if not seen[i]:
            j, L = i, 0
            while not seen[j]:
                seen[j] = True; j = p[j]; L += 1
            s += L - 1
    return s % 2

A5 = [p for p in itertools.permutations(range(5)) if parity(p) == 0]
assert len(A5) == 60
E = tuple(range(5))
IDX = {g: i for i, g in enumerate(A5)}

