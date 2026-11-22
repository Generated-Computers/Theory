"""Numbers behind the two-sided density lemma (Lemma kp-density2) and the threshold (1+sqrt 13)/6.

1. Iterates l_{s+1} = L(m_s), m_{s+1} = U(l_{s+1}) from m_0 = 1/2 and compares the limit with the
   closed form  eps*l* = ((2+eps) - sqrt(4 + 4 eps - 3 eps^2)) / 2.
2. Solves eps*l*(eps) = 1 - eps and compares with (1+sqrt 13)/6.
3. Simulates prefix densities on a few bases (including j_k = 0, which the remark uses to show that
   no density bound can push the method below 3/4) and reports min_{g >= n/50} O_g/(g+1).
4. Lemma kp-density3 / Theorem kp-34: the root rho(eps) of rho = eps(1-rho)^2 (called varpi in the
   paper) satisfies rho >= l*, rho(3/4) = 1/3 and eps*rho = 1-eps exactly at 3/4; prefix densities
   on further bases (blocks, two-scale) are compared with rho.
"""
import math, random

def L(m, e): return e * (1 - m) / (1 + e * (1 - m))
def U(l, e): return (1 - e * l) / (2 - e * l)
def lstar(e): return ((2 + e) - math.sqrt(4 + 4 * e - 3 * e * e)) / 2 / e

def iterate(e, S):
    m = 0.5; out = []
    for _ in range(S):
        l = L(m, e); m = U(l, e); out.append((l, m))
    return out

print("eps   stages s=1..5 of l_s                          limit      closed form")
for e in (0.7, 0.7676, 0.8, 1.0):
    seq = iterate(e, 60)
    print(f"{e:.4f} " + " ".join(f"{l:.4f}" for l, _ in seq[:5]) + f"   {seq[-1][0]:.6f}   {lstar(e):.6f}")
    assert abs(seq[-1][0] - lstar(e)) < 1e-9
    assert all(seq[s][0] <= seq[s + 1][0] + 1e-15 and seq[s][1] >= seq[s + 1][1] - 1e-15 for s in range(59))

a, b = 0.5, 1.0
for _ in range(80):
    c = (a + b) / 2
    if c * lstar(c) > 1 - c: b = c
    else: a = c
print(f"threshold eps*l*(eps) = 1-eps at {b:.12f}; (1+sqrt13)/6 = {(1 + math.sqrt(13)) / 6:.12f}")
assert abs(b - (1 + math.sqrt(13)) / 6) < 1e-10
print(f"at eps=1: l* = {lstar(1):.6f}, (3-sqrt5)/2 = {(3 - math.sqrt(5)) / 2:.6f}")
r34 = 1 / 3
print(f"zero base fixed point rho = eps(1-rho)^2 at eps = 3/4: rho = {r34:.6f}, eps*rho = {0.75 * r34:.4f} = 1 - eps")

def prefix_min(base, e, n, seed):
    rng = random.Random(seed)
    x = [1]; O = 1; worst = 1.0
    for i in range(1, n + 1):
        q = rng.randrange(i) if (i >= 2 and rng.random() < e) else base(i)
        xi = 0 if (x[i - 1] or x[q]) else 1
        x.append(xi); O += xi
        if i >= n // 50: worst = min(worst, O / (i + 1))
    return worst

bases = {
    "zero (j_k = 0)": lambda i: 0,
    "NOT then zero": lambda i: i - 1 if i < 20000 else 0,
    "im2": lambda i: max(0, i - 2),
    "half": lambda i: i // 2,
}
n = 200000
print(f"\nmin over g >= n/50 of O_g/(g+1), n = {n}")
for e in (0.75, 0.7676, 0.85):
    row = "  ".join(f"{name}: {prefix_min(f, e, n, 1):.4f}" for name, f in bases.items())
    print(f"eps={e:.4f}  l*={lstar(e):.4f}  eps/(2+eps)={e / (2 + e):.4f}  |  {row}")

# Lemma kp-density3: the root rho(eps) of rho = eps (1-rho)^2 bounds the density from below on every
# base; eps rho(eps) = 1 - eps exactly at eps = 3/4 (Theorem kp-34).
def rho(e): return ((2 * e + 1) - math.sqrt(4 * e + 1)) / (2 * e)
assert abs(rho(0.75) - 1 / 3) < 1e-12 and abs(rho(1.0) - (3 - math.sqrt(5)) / 2) < 1e-12
assert all(rho(e) > lstar(e) - 1e-12 for e in (0.5, 0.6, 0.7, 0.8, 0.9, 1.0))
a, b = 0.5, 1.0
for _ in range(80):
    c = (a + b) / 2
    if c * rho(c) > 1 - c: b = c
    else: a = c
print(f"\neps*rho(eps) = 1-eps at {b:.12f}")
assert abs(b - 0.75) < 1e-10
bases["blocks (j=i-1 / j=0 / j=i-2 in blocks of 1000)"] = lambda i: (i - 1, 0, max(0, i - 2))[(i // 1000) % 3]
bases["two-scale (j=i-1 for i in [4^k, 2*4^k), else 0)"] = lambda i: i - 1 if 4 ** int(math.log(i, 4)) * 2 > i else 0
print(f"min over g >= n/50 of O_g/(g+1) against rho(eps), n = {n}")
for e in (0.6, 0.75, 0.9):
    row = "  ".join(f"{name.split(' ')[0]}: {prefix_min(f, e, n, 2):.4f}" for name, f in bases.items())
    print(f"eps={e:.2f}  rho={rho(e):.4f}  |  {row}")
