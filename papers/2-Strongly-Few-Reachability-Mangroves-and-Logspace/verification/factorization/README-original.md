# Computer checks

Plain Python 3, standard library only. Run from this directory (the scripts import
`sfcommon.py`). Theorem numbers refer to `paper.pdf`. The proofs in the paper do not depend on
these checks.

Path counts are computed by dynamic programming in topological order and, independently, by
the matrix series `I + A + ... + A^(n-1)` and by explicit depth-first enumeration of walks.
Every acyclic digraph on `n` vertices is isomorphic to a subgraph of the transitive tournament
(edges from smaller to larger labels), so enumerating those subgraphs covers all acyclic
digraphs.

| script | what it checks | time |
|---|---|---|
| `check_fixedpoint.py` | Thm 3.1 (bounded fixed point, exhaustive over all candidate matrices C), Thm 3.3 and Cor 3.4 (budgeted stabilization), on all digraphs on at most 4 vertices, cyclic ones included | 25 s |
| `check_factorization.py` | Lemma 4.1, Thm 4.2, Cor 4.3, Thm 5.1 (every threshold), Cor 5.2, Thm 5.3 (level partition), Thm 6.2 (factorization multiplied back; every factor verified to be the path-count matrix of a mangrove), Remark 5.6 (the source's square-root recursion), Thms 7.1, 7.2, 11.3, 11.4; all 33,867 acyclic digraphs on at most 6 vertices and 300 random k-strongly-unambiguous digraphs (7 to 24 vertices, k up to 1000) | 25 s |
| `check_cyclomatic.py` | Lemma 8.2, Thm 8.3, Thm 8.8 (both directions), Thm 8.6, Thm 8.5, Thm 10.1, Thm 9.1 (lower bound c >= l(r) for every graph; equality of the minimum for small r) on all 707,284 trimmed two-terminal DAGs among the simple ones on at most 7 vertices and the multigraphs on at most 5 vertices with multiplicities at most 3 | 35 s |
| `check_addition_chains.py` | Thm 9.1: the construction for every r <= 128, and the extraction of an addition chain from 3000 random trimmed two-terminal DAGs | 1 s |
| `check_obstructions.py` | Thm 10.4 and Remark 10.5 on every minimal k-violation in the families above; the extraction of Thm 10.6 on all acyclic digraphs on at most 6 vertices; enumeration of the families F_1, F_2, F_3 with the subdivision-containment test of Remark 10.7 | 10 min |
| `check_density.py` | exact ex_sf(n,k) for n <= 7 (all graphs) and for n = 8, k <= 6 (pruned search); Thm 11.1, Prop 11.2 and the three-layer construction (Table 1) | 4 s / 7 min |
| `explore_min_factors.py` | Remark 6.6: least number of mangrove factors for T_4, T_5 and D_2 | 5 s |

## Commands and outputs

```
python3 check_fixedpoint.py
```
```
Theorem 3.1: 164 (graph, k) pairs checked by exhaustive search over C
Theorem 3.3 / Corollary 3.4: 1131102 (graph, root, budget) cases, 168985 within budget
all checks passed
```

```
python3 check_factorization.py          # defaults: max_n = 6, 300 random graphs, seed 2026
```
```
n = 1: all 1 upper-triangular DAGs checked
n = 2: all 2 upper-triangular DAGs checked
n = 3: all 8 upper-triangular DAGs checked
n = 4: all 64 upper-triangular DAGs checked
n = 5: all 1024 upper-triangular DAGs checked
n = 6: all 32768 upper-triangular DAGs checked
300 random k-strongly-unambiguous graphs (7 <= n <= 24) checked
  balanced factorizations verified: 29850
  graphs: 34167
  level factorizations verified: 34167
  max factors/(2 floor(log2 k)+1): 1.0
  pairs u~>v (4.1, 4.2): 551930
  separators (7.2): 107877
  thresholds tau (5.1): 74764
all checks passed
```
("balanced factorizations" are those of the source's recursion, Remark 5.6; they exist for
k >= 2.)

```
python3 check_cyclomatic.py             # defaults: simple n <= 7, multigraphs n <= 5
```
```
simple DAGs, n = 7: done (199564 trimmed graphs so far)
multigraphs (multiplicity <= 3), n = 5: done (707284 trimmed graphs so far)
  equality graphs (r = 2^c): 186
  graphs: 707284
l(r) for r = 1..40: [0, 1, 2, 2, 3, 3, 4, 3, 4, 4, 5, 4, 5, 5, 5, 4, 5, 5, 6, 5, 6, 6, 6, 5, 6, 6, 6, 6, 7, 6, 7, 5, 6, 6, 7, 6, 7, 7, 7, 6]
min c found     : [0, 1, 2, 2, 3, 3, 4, 3, 4, 4, 5, 4, 5, 5, 5, 4, 5, 5, 6, 5, 6, 6, 7, 5, 6, 6, 6, 6, 7, 6, 7, 7, 7, 7, 7, 6, 7, 7, 7, 7]
r in 1..40 with min c = l(r): [1, 2, ..., 22, 24, 25, 26, 27, 28, 29, 30, 31, 35, 36, 37, 38, 39]
c >= l(r) holds for every graph; all checks passed
```
(Intermediate progress lines omitted. For r = 23, 32, 33, 34, 40 the small graphs do not reach
l(r); the construction of Theorem 9.1 needs more vertices, and `check_addition_chains.py`
verifies it for these r.)

```
python3 check_addition_chains.py        # defaults: R = 128, 3000 random graphs, seed 2026
```
```
construction of Theorem 9.1 verified for r = 1..128; l(r) = [0, 1, 2, 2, 3, 3, 4, 3, ...]
lower-bound extraction verified on 3000 random trimmed two-terminal DAGs
all checks passed
```

```
python3 check_obstructions.py
```
```
Theorem 10.4: edge-minimal violators checked, per k: {1: 109, 2: 1020, 3: 4351, ...}   (797,325 pairs (H,k) in all)
Theorem 10.6 extraction: 72005 (graph, k) cases on n <= 6 vertices
k = 1: 1 reduced cores up to isomorphism (path counts [2]); 1 remain after removing members that contain a subdivision of another member
k = 2: 7 reduced cores up to isomorphism (path counts [3, 3, 3, 3, 3, 4, 4]); 7 remain ...
k = 3: 53 reduced cores up to isomorphism (path counts [4, 4, ..., 4]); 53 remain ...
all checks passed
```
The full output, with the edge lists of all members of F_1, F_2, F_3, is in
`out_obstructions.txt`.

```
python3 check_density.py                # n <= 7, all graphs
python3 check_density.py 8 6            # n = 8, graphs with all path counts <= 6
```
```
n = 7: (k, ex_sf, three-layer lower bound, upper bound of Thm 11.1) =
    [(1, 12, 12, 12.25), (2, 15, 15, 17.5), (3, 16, 16, 21), (4, 17, 16, 21), (5, 17, 14, 21), (6, 18, 11, 21)]
n = 8: (k, ex_sf, three-layer lower bound, upper bound of Thm 11.1) =
    [(1, 16, 16, 16.0), (2, 19, 19, 22.0), (3, 21, 21, 28), (4, 22, 21, 28), (5, 22, 20, 28), (6, 23, 17, 28)]
all checks passed
```
(Rows n = 2, ..., 6 are in `out_density.txt`.)

```
python3 explore_min_factors.py
```
```
T4: minimum number of mangrove factors = 2
T5: minimum number of mangrove factors = 3
D2: minimum number of mangrove factors = 2
```
Each factorization found is multiplied back and compared with the path-count matrix; the
factor graphs are printed in `out_min_factors.txt`.

All outputs are stored in the `out_*.txt` files.
