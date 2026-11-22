# Reset-set iteration Phi of #25 (5.1): Phi(R) = {-1} u {i : j_i - pred_R(j_i) odd}, pred_R(i) = max{r in R : r <= i}.
# Counts the rounds in which R changes (one more application then confirms the fixed point).
# Checks the linear family j_i = max(0, i-2) of #25 §15.4 against ceil(n/3) for every n <= 300,
# then reports mean rounds on random instances.
# usage: python3 -I phi_check.py
import bisect, random, statistics
def phi_rounds(j, n):
    R = [-1]; t = 0
    while True:
        new = [-1] + [i for i in range(1, n + 1) if (j[i] - R[bisect.bisect_right(R, j[i]) - 1]) % 2 == 1]
        if new == R: return t
        R = new; t += 1
bad = [n for n in range(1, 301) if phi_rounds([None] + [max(0, i - 2) for i in range(1, n + 1)], n) != -(-n // 3)]
print("j_i = max(0,i-2): changing rounds == ceil(n/3) for all 1 <= n <= 300; mismatches:", bad)
random.seed(1)
for n in (256, 1024, 4096):
    r = [phi_rounds([None] + [random.randrange(i) for i in range(1, n + 1)], n) for _ in range(10)]
    print(f"random n={n}: mean changing rounds {statistics.mean(r):.1f} (add 1 for #25's convention)")
