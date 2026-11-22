# Explicit constants for Theorem 10.3 (KP on eps-smoothed instances), paper Section 10 / NOTE.md §5d.
# For eps > eps_K = (sqrt(17)-1)/4 a grid search over eta in (0, 0.95 eps/(2+eps)) and lambda picks
#   c = eps/(2+eps) - eta,  theta = (eps/(lam+1) + 1 - eps) / (eps*c),  kappa = (2/((2+eps)*0.9*eta))^2,
#   g0 = ceil(kappa ln n) + gmin, where gmin is the least g >= 3 with (ln g + 4)/(2g) <= eta/10,
#   rounds <= A ln(n+1) + gmin + 2 with A = (lam+2)/ln(1/theta) + kappa, for every n >= 2; failure <= 2/n.
# usage: python3 -I kp_constants.py
import math
EPS_K = (math.sqrt(17) - 1) / 4

def best(eps):
    top = None
    for ie in range(1, 950):
        eta = ie / 1000 * eps / (2 + eps)
        c = eps / (2 + eps) - eta
        if c <= 0: break
        for lam in [x / 4 for x in range(1, 4000)]:
            theta = (eps / (lam + 1) + 1 - eps) / (eps * c)
            if theta >= 1: continue
            kappa = (2 / ((2 + eps) * 0.9 * eta)) ** 2
            A = (lam + 2) / math.log(1 / theta) + kappa
            if top is None or A < top[0]: top = (A, eta, lam, theta, kappa)
    return top

def gmin(eta):
    g = 3
    while (math.log(g) + 4) / (2 * g) > eta / 10: g += 1
    for h in range(g, g + 10**6, 97):                       # (ln g + 4)/(2g) is decreasing for g >= 3
        assert (math.log(h) + 4) / (2 * h) <= eta / 10
    return g

print("eps_K = (sqrt 17 - 1)/4 = %.6f" % EPS_K)
for eps in [0.79, 0.8, 0.85, 0.9, 0.95, 1.0]:
    A, eta, lam, theta, kappa = best(eps)
    assert theta < 1 and eps * (eps / (2 + eps) - eta) > 1 - eps
    print("eps=%.2f  A=%9.1f  B=gmin+2=%6d  (eta=%.4f lambda=%6.2f theta=%.4f kappa=%8.1f)"
          % (eps, A, gmin(eta) + 2, eta, lam, theta, kappa))
# the threshold: eps^2/(2+eps) > 1-eps  <=>  2 eps^2 + eps - 2 > 0
# Corollary 10.6(b) may use a smaller lambda' for the running time: at eps = 1 any lambda' > 1/c - 1 works.
eta1 = 0.01; c1 = 1 / 3 - eta1
print("eps=1, eta=%.2f: theta(lambda') < 1 for lambda' > %.3f" % (eta1, 1 / c1 - 1))
for e in [EPS_K - 1e-9, EPS_K + 1e-9]:
    print("at eps = %.9f: eps^2/(2+eps) - (1-eps) = %+.2e" % (e, e * e / (2 + e) - (1 - e)))
