# Front trajectory of Newton on eps-smoothed j_i = max(0,i-2): jump/sqrt(f) and error density past the front.
import random, sys, math
def run(n, eps, seed):
    R = random.Random(seed)
    j = [0]*(n+1)
    for i in range(2, n+1): j[i] = R.randrange(i) if R.random() < eps else i-2
    xs = [1]+[0]*n
    for i in range(1, n+1): xs[i] = int(not (xs[i-1] or xs[j[i]]))
    x = [1]+[0]*n; out = []
    while True:
        f = next((i for i in range(n+1) if x[i] != xs[i]), None)
        if f is None: break
        dens = sum(x[i] != xs[i] for i in range(f, min(n+1, 2*f))) / max(1, min(n+1, 2*f) - f)
        out.append((f, dens))
        d = [0]*(n+1)
        for i in range(1, n+1):
            p, q = i-1, j[i]
            F = x[i] ^ ((1 ^ x[p]) & (1 ^ x[q]))
            sg = d[p] if p == q else (((1 ^ x[q]) & d[p]) ^ ((1 ^ x[p]) & d[q]))
            d[i] = F ^ sg
        x = [a ^ b for a, b in zip(x, d)]; x[0] = 1
    return out
n, eps = int(sys.argv[1]), float(sys.argv[2])
tr = run(n, eps, 5)
print("rounds", len(tr))
for k in range(0, len(tr)-1, max(1, len(tr)//14)):
    f, dn = tr[k]; f2 = tr[k+1][0]
    print("t=%4d f=%6d jump=%5d jump/sqrt(f)=%.2f  err-density in [f,2f)=%.3f" % (k, f, f2-f, (f2-f)/math.sqrt(f), dn))
