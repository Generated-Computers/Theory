"""Heuristic first-moment growth rates behind Remark rem:kpr (not a proof).

One step of a dependency chain is found by scanning back from its start position P. Each gate is
resampled with probability eps and then reads a one with probability psi; the adversary's gates read
whatever value the adversary prefers. A pointer into a deep position is a continuation; resampled
pointers are dropped (their weight in Steps 3-4 is O(1/(lambda+1))). Continuations are of two types:
a child (relevant non-reset) reads a zero, so the next scan starts at a zero; an anchor (reset) reads
a one, so the next scan starts at a one. The growth rate is the spectral radius of the resulting
two-type mean map, and a first-moment count is subcritical when it is < 1. psi is a density of ones:
the proven lower bound l*(eps) of Lemma kp-density2, or the density rho(eps) of the zero base.

KP (depth d): every gate in the window counts once; rate (1-eps)/(eps psi), threshold eps_B.

D_last (anchor = last reset, counted once): from a zero, children (1-eps)(1-p)/(p(2-p)) and one
anchor 1-eps; from a one, children (1-eps)/(p(2-p)) and anchor 1-eps; p = eps psi.

D (switch witnesses, Lemma kpr-switch(b)): resets that are not followed must also be deep; near the
top of a chain that is rare, so they end the scan. Scanning back from a gate at which the alternation
predicts output 1 (it is relevant), an adversarial gate reads a zero and is a child; a resampled gate
continues if it reads a zero. At a predicted 0, an adversarial gate either is the relevant reset that
starts the step (the alternation breaks below it: one anchor) or reads a zero and is passed; a
resampled gate is passed if it reads a zero. With weights w0 (child) and w1 (anchor):
  U1 = (1-eps)(w0 + U0) + eps(1-psi) U0,   U0 = (1-eps) max(w1, U1) + eps(1-psi) U1,
and a scan from a zero starts in U0, from a one in U1. The adversary may choose per gate, so the rate
is the spectral radius of the monotone homogeneous map w -> (U0(w), U1(w)), computed as
min over w of max_s U_s(w)/w_s.
"""
import math

def lstar(e): return ((2 + e) - math.sqrt(4 + 4 * e - 3 * e * e)) / 2 / e
def rho0(e):  # root of rho = e (1 - rho)^2 in (0, 1/2)
    return ((2 * e + 1) - math.sqrt(4 * e + 1)) / (2 * e)

def rate_kp(e, psi): return (1 - e) / (e * psi)

def rate_last(e, psi):
    p = e * psi; c = (1 - e) / (p * (2 - p)); a = 1 - e
    t = c * (1 - p) + a; det = -a * c * p
    return (t + math.sqrt(t * t - 4 * det)) / 2

def U(e, psi, w0, w1):
    u1 = u0 = 0.0
    for _ in range(20000):
        n1 = (1 - e) * (w0 + u0) + e * (1 - psi) * u0
        n0 = (1 - e) * max(w1, u1) + e * (1 - psi) * u1
        if abs(n1 - u1) + abs(n0 - u0) < 1e-13: break
        u1, u0 = n1, n0
    return n0, n1

def rate_switch(e, psi):
    def worst(r):  # weights w = (1, r)
        u0, u1 = U(e, psi, 1.0, r)
        return max(u0, u1 / r)
    lo, hi = 1e-3, 1e3  # golden-section search on log r (worst is quasi-convex in practice)
    a, b = math.log(lo), math.log(hi)
    for _ in range(200):
        m1, m2 = a + (b - a) * 0.382, a + (b - a) * 0.618
        if worst(math.exp(m1)) < worst(math.exp(m2)): b = m2
        else: a = m1
    return worst(math.exp((a + b) / 2))

def threshold(rate, dens):
    a, b = 0.3, 0.999
    for _ in range(60):
        c = (a + b) / 2
        if rate(c, dens(c)) < 1: b = c
        else: a = c
    return b

for name, dens in (("l*(eps)", lstar), ("rho(eps), zero base", rho0)):
    print(f"psi = {name}: thresholds  KP {threshold(rate_kp, dens):.4f}   D_last {threshold(rate_last, dens):.4f}"
          f"   D {threshold(rate_switch, dens):.4f};   at eps = 0.6: rate_D = {rate_switch(0.6, dens(0.6)):.4f},"
          f" rate_last = {rate_last(0.6, dens(0.6)):.4f}")
assert abs(threshold(rate_kp, lstar) - (1 + math.sqrt(13)) / 6) < 1e-6
