# Check the worst-case family W_n: E_1 = {5,6}, fronts f_t = 2t+3, T_n = floor((n-1)/2).
def newton_rounds(j, n):
    xs = [1] + [0] * n
    for i in range(1, n + 1): xs[i] = int(not (xs[i-1] | xs[j[i]]))
    x = [1] + [0] * n; fronts = []; E1 = None; t = 0
    while True:
        E = [i for i in range(n + 1) if x[i] != xs[i]]
        if t == 1: E1 = E
        if not E: return t, fronts, E1
        fronts.append(E[0])
        d = [0] * (n + 1)
        for i in range(1, n + 1):
            p, q = i - 1, j[i]
            F = x[i] ^ ((1 ^ x[p]) & (1 ^ x[q]))
            s = d[p] if p == q else (((1 ^ x[q]) & d[p]) ^ ((1 ^ x[p]) & d[q]))
            d[i] = F ^ s
        x = [x[i] ^ d[i] for i in range(n + 1)]; x[0] = 1; t += 1
bad = 0
for n in range(6, 401):
    j = [None, 0, 1, 0, 1, 2] + [1 if i % 2 == 0 else i - 2 for i in range(6, n + 1)]
    T, fronts, E1 = newton_rounds(j, n)
    ok = T == (n - 1) // 2 and E1 == [5, 6] and all(fronts[t] == 2 * t + 3 for t in range(1, T))
    bad += not ok
print("W_n checked for n = 6..400; failures:", bad)
