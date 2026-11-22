# Machine check that the window-lemma recursion closes with the explicit constants of NOTE.md §4.
# Follows the proof exactly: canonical Pi_l, bottom level and depth bound, a-priori phase split,
# Markov allocation, the theta-proviso X_l <= 1/20, R_0 and the final failure budget.
# All arithmetic is in log space, so f can be astronomically large (f = e^F).
# This checks arithmetic only; the probabilistic steps are in the note.
# usage: python3 -I check_constants.py
import math

def lse(*xs):
    m = max(xs)
    return m + math.log(sum(math.exp(x - m) for x in xs))

LAM, BETA, THETA = 450.0, 1 / 20, 1 / 5
EPS_LN = 100.0                      # eps = e^{-100}
ln_eps = -EPS_LN
B_COEF = 2500.0                     # b >= (G/theta) * LAM with G/theta <= 5.53
A_COEF = 2 * B_COEF + 12            # linear-phase growth a = 2b + 12
GAMMA0 = 400 * LAM                  # c_L <= GAMMA0 * eps
M1 = 8 * math.ceil(EPS_LN)          # linear-phase Markov factor
k1 = math.floor((EPS_LN - math.log(GAMMA0 + 1)) / math.log(A_COEF * M1))  # a-priori linear levels
ETA_BOUND = 12 / 16 * 2.0 ** (-k1)  # proof: ln c_1 <= 12 * 2^Q <= 12 * (ln f / 16) * 2^-k1 = (3/128) ln f

def run(F):
    lnf = F
    lnPi1 = math.log(5) + 0.5 * (math.log(lnf) - lnf)                 # Pi_1 = 5 sqrt(ln f / f)
    lnPi = [None, lnPi1]
    small = math.log(3) + math.log(lnf) - lnf                          # 3 ln f / f
    while lnPi[-1] < 0:
        lnPi.append(math.log(15) + 0.5 * lse(lnPi[-1], small))        # Pi_{l+1} = 15 sqrt(Pi_l + 3lnf/f)
    for l in range(1, len(lnPi) - 1):
        assert 2 * lnPi[l + 1] <= math.log(LAM) + lnPi[l] + 1e-9      # (P2) Pi_{l+1}^2 <= LAM Pi_l
        assert lnPi[l + 1] >= lnPi[l]                                  # (P2) increasing
    for l in range(1, len(lnPi)):                                      # (P2) lower bound used for depth
        rhs = math.log(225) + 2.0 ** (1 - l) * (lnPi1 - math.log(225))
        assert lnPi[l] >= rhs - 1e-9 * max(1.0, abs(rhs))              # relative tol: |rhs| ~ ln f
    lb = max(l for l in range(1, len(lnPi) - 1) if lnPi[l + 1] <= math.log(BETA))
    L = lb + 1
    assert lb >= 1 and lnPi[L] >= -math.log(400 * LAM) - 1e-9          # (P3) Pi_{lb+1} > beta^2/lambda
    depth = (math.log(225) - lnPi1) / math.log(4500)                   # (P3) 2^lb <= ln(225/Pi_1)/ln 4500
    assert 2 ** lb <= depth + 1e-9 and depth <= lnf / 16               #      <= ln f / 16
    assert 2.0 ** (-lb) * (-lnPi1) >= math.log(20) - 1e-9              # (P3) used by the Phase-2 proviso
    ln_nu = -(lnf + lnPi1)
    assert ln_nu <= ln_eps                                             # nu <= eps (f >= e^200)
    lnc = ln_eps - lnPi[L]                                             # c_L = eps / Pi_L
    assert lnc <= math.log(GAMMA0) + ln_eps + 1e-9
    fail, worst_lnX, quad, ph1max = 0.0, -1e300, 0, -1e300
    for k in range(1, L):                                              # level l = L - k
        l = L - k
        if k <= k1:
            M = M1
        else:
            quad += 1; M = 2 ** (quad + 2)
        fail += 1 / M
        # c_l <= M [ 5.3 eps + 5.53 nu + b (c + nu)(1 + c) ]   with c = c_{l+1}
        lnbr = lse(math.log(5.3) + ln_eps, math.log(5.53) + ln_nu,
                   math.log(B_COEF) + lse(lnc, ln_nu) + lse(0.0, lnc))
        lnc = math.log(M) + lnbr
        if k <= k1:
            assert lnc <= 1e-9, ("linear phase exceeded 1", k, lnc)     # Phase 1: c <= 1
            ph1max = max(ph1max, lnc)
        worst_lnX = max(worst_lnX, lnc + lnPi[l])
    assert worst_lnX <= math.log(BETA), ("X too large", worst_lnX)   # proviso X <= 1/20
    eta = lnc / lnf
    assert eta <= ETA_BOUND + 1e-12 and ETA_BOUND <= 1 / 16, ("eta", eta, ETA_BOUND)
    assert quad <= max(0, lb - k1)
    # Step 4: R_0 = (G/theta)(1 + (X_1 f + 1)(Pi_1 + X_1)) <= 340 f^{1/8} ln f, then the budget
    lnX1 = lnc + lnPi1
    lnR0 = math.log(5.53) + lse(0.0, lse(lnX1 + lnf, 0.0) + lse(lnPi1, lnX1))
    assert lnR0 <= math.log(340) + lnf / 8 + math.log(lnf)
    total = fail + math.exp(lnR0 - lnf / 3) + math.exp(-lnf / 3)      # Sum 1/M + R_0/B + B^2/f
    assert total <= 0.26, ("budget", total)
    return L, quad, eta, fail, total, worst_lnX, ph1max

grid = sorted(set([200.0 + 0.25 * i for i in range(0, 7201)] +                   # 200 .. 2000, fine
                  [10 ** (math.log10(2000) + (20 - math.log10(2000)) * i / 4000) for i in range(4001)]))
worst = dict(eta=-1e9, fail=0, total=0, lnX=-1e300, ph1=-1e300)
for F in grid:
    L, quad, eta, fail, total, wX, ph1 = run(F)
    worst['eta'] = max(worst['eta'], eta); worst['fail'] = max(worst['fail'], fail)
    worst['total'] = max(worst['total'], total); worst['lnX'] = max(worst['lnX'], wX)
    worst['ph1'] = max(worst['ph1'], ph1)
print(f"eps = e^-{EPS_LN:.0f}; b = {B_COEF:.0f}; a = {A_COEF:.0f}; M1 = {M1}; k1 = {k1}; "
      f"analytic eta bound = {ETA_BOUND:.5f} (3/128)")
print(f"checked {len(grid)} values of ln f in [200, 1e20]")
print(f"worst eta = {worst['eta']:.4f}, worst Markov failure = {worst['fail']:.5f}, "
      f"worst total budget = {worst['total']:.5f}, worst ln X = {worst['lnX']:.1f}, "
      f"worst Phase-1 ln c = {worst['ph1']:.1f}")
print("all assertions passed")
