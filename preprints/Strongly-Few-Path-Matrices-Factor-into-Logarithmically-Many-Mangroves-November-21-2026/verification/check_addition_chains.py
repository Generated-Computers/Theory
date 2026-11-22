"""Both directions of Theorem 9.1, constructively.

* Upper bound: for every 1 <= r <= R (default 128) an optimal addition chain is found by
  iterative deepening; the graph of the proof (vertices v_0..v_l, two subdivided branches per
  step) is built and checked to be a simple trimmed two-terminal DAG with exactly r paths and
  cyclomatic number l(r).
* Lower bound: for random trimmed two-terminal DAGs (up to 14 vertices) the addition chain of
  the proof (distinct values of the partial sums of p(v) = sum p(u), sorted) is extracted and
  checked to be a valid addition chain ending at r of length <= c.
Usage: python3 check_addition_chains.py [R=128] [random=3000] [seed=2026]
"""
import random
import sys

from sfcommon import path_matrix, topo_order


def optimal_chain(r):
    if r == 1:
        return [1]

    def search(chain, left):
        last = chain[-1]
        if last == r:
            return list(chain)
        if left == 0 or last << left < r:
            return None
        cand = set()
        for i in range(len(chain)):
            for j in range(i, len(chain)):
                s = chain[i] + chain[j]
                if last < s <= r:
                    cand.add(s)
        for s in sorted(cand, reverse=True):
            chain.append(s)
            res = search(chain, left - 1)
            chain.pop()
            if res:
                return res
        return None

    L = (r - 1).bit_length()
    while True:
        res = search([1], L)
        if res:
            return res
        L += 1


def chain_graph(chain):
    l = len(chain) - 1
    n = 3 * l + 1
    A = [[0] * n for _ in range(n)]
    nxt = l + 1
    for i in range(1, l + 1):
        a = chain[i]
        j, h = next((j, h) for j in range(i) for h in range(j, i) if chain[j] + chain[h] == a)
        x, y = nxt, nxt + 1
        nxt += 2
        A[j][x] = A[x][i] = 1
        A[h][y] = A[y][i] = 1
    return A, 0, l


def trimmed(A, s, t):
    C = path_matrix(A)
    n = len(A)
    if any(C[s][v] == 0 or C[v][t] == 0 for v in range(n)):
        return False
    return True


def extract_chain(A, s, t):
    """Chain of the proof of Theorem 9.1 (lower bound) from a trimmed two-terminal DAG."""
    n = len(A)
    order = topo_order(A)
    p = [0] * n
    p[s] = 1
    values = {1}
    additions = 0
    for v in order:
        if v == s:
            continue
        acc = None
        for u in range(n):
            for _ in range(A[u][v]):
                if acc is None:
                    acc = p[u]
                else:
                    acc += p[u]
                    additions += 1
                    values.add(acc)
        p[v] = acc
    chain = sorted(values)
    return chain, additions, p[t]


def valid_chain(chain):
    if chain[0] != 1:
        return False
    for i in range(1, len(chain)):
        if chain[i] <= chain[i - 1]:
            return False
        if not any(chain[a] + chain[b] == chain[i] for a in range(i) for b in range(a, i)):
            return False
    return True


def main():
    R = int(sys.argv[1]) if len(sys.argv) > 1 else 128
    nr = int(sys.argv[2]) if len(sys.argv) > 2 else 3000
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 2026
    lens = []
    for r in range(1, R + 1):
        ch = optimal_chain(r)
        A, s, t = chain_graph(ch)
        C = path_matrix(A)
        m = sum(map(sum, A))
        n = len(A)
        if C[s][t] != r or m - n + 1 != len(ch) - 1 or not trimmed(A, s, t) or max(map(max, A)) > 1:
            print("FAILURE: construction for r =", r)
            sys.exit(1)
        lens.append(len(ch) - 1)
    print(f"construction of Theorem 9.1 verified for r = 1..{R}; l(r) =", lens)
    rng = random.Random(seed)
    done = 0
    while done < nr:
        n = rng.randint(2, 14)
        A = [[0] * n for _ in range(n)]
        dens = rng.random()
        for i in range(n):
            for j in range(i + 1, n):
                if rng.random() < dens:
                    A[i][j] = rng.choice([1, 1, 1, 2])
        if not trimmed(A, 0, n - 1):
            continue
        chain, adds, r = extract_chain(A, 0, n - 1)
        c = sum(map(sum, A)) - n + 1
        if adds != c or chain[-1] != r or not valid_chain(chain) or len(chain) - 1 > c:
            print("FAILURE: extraction", A)
            sys.exit(1)
        done += 1
    print(f"lower-bound extraction verified on {nr} random trimmed two-terminal DAGs")
    print("all checks passed")


if __name__ == "__main__":
    main()
