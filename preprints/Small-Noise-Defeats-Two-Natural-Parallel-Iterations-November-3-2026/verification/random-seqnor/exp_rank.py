# Theorem 1 checks: the Strahler rank of a random SeqNOR instance follows the level process,
# a level started at s survives K steps with probability prod_{k=1..K} (s+1)/(s+k),
# and rank/sqrt(n) -> sqrt(8/pi).
# usage: python3 -I exp_rank.py <dir containing core.py>
import sys, random, math, statistics
sys.path.insert(0, sys.argv[1]); from core import strahler
random.seed(3)

def rank_fast(n):
    # rank increments at i iff j_i lands in [a, i-2], where a = start of the current level
    a = 0; r = 0
    for i in range(1, n + 1):
        ji = random.randrange(i)
        if a <= ji <= i - 2:
            r += 1; a = i
    return r

for _ in range(300):
    n = random.randint(1, 400); st = random.getstate()
    j = [random.randrange(i) for i in range(1, n + 1)]
    random.setstate(st)
    assert strahler(j)[n] == rank_fast(n)
print("level process == Strahler recursion on 300 random instances")

s, K, trials = 500, 40, 200000
emp = sum(1 for _ in range(trials)
          if all(not (s <= random.randrange(s + k) <= s + k - 2) for k in range(1, K + 1))) / trials
exact = math.exp(sum(math.log((s + 1) / (s + k)) for k in range(1, K + 1)))
print(f"P(level from s=500 survives 40 steps): empirical {emp:.4f}, product formula {exact:.4f}")

print("n, mean rank/sqrt(n), sd  (limit sqrt(8/pi) = %.4f)" % math.sqrt(8 / math.pi))
for n in (10**4, 10**5, 10**6):
    T = 40 if n < 10**6 else 12
    v = [rank_fast(n) / math.sqrt(n) for _ in range(T)]
    print(n, round(statistics.mean(v), 4), round(statistics.stdev(v), 4))
