# Computer checks

Plain Python 3 scripts, standard library only. They check finite claims of the paper; every
statement they touch is proved in the text. Run each from this folder with `python3 -I <script>`.
None of the scripts reads or writes files, so no paths needed changing.

| Script | Source preprint | What it checks | Run time / result (24 Nov 2026) |
| --- | --- | --- | --- |
| `check_43.py` | P-Complete Equal-Flow Programs with Capacities at Most Two | Exact enumeration of the vertices of the NAND polytope (Theorem 3.2); NAND normalization (Theorem 3.1) on 2,000 random alternating circuits | 0.1 s; vertices are exactly the four NAND points; 0 normalization failures |
| `check_44.py` | Min-Cost Flow Has No Read-Only Comparator | Boundary functions of 1,238 random networks (4 terminals, at most 2 internal vertices) by exhaustive enumeration: exchange inequality (Theorem 4.1) and absence of the comparator signature (Theorem 4.4); crossbar table (Remark 4.7); NAND relation is not a lattice under any of the 8 complementations (Theorem 4.11 and the remark after it) | 2.9 s; 0 exchange violations, 0 comparator signatures; crossbar table `|x-y|` with crossed states of cost 0 and exchange satisfied; NAND never a lattice |
| `check_33.py` | Circuit LPs Need Linear Precision | Fibonacci point of Theorem 5.2 for n = 2..39 and the minor of Theorem 5.3 for m = 2..29 in exact arithmetic; escape switching (Theorems 7.8, 7.11) on 3,000 random monotone circuits, rank-biased and random starts; rank layers (Lemma 7.10) on 500 random circuits; Latin contraction root domains (Theorem 7.3) over S_3 on 300 random components | 0.9 s; all assertions pass; max(rounds - (r+1)) = 0, so the bound r+1 is attained |

Recorded output:

```
$ python3 -I check_43.py
vertices: [(0, 0, 1), (0, 1, 1), (1, 0, 1), (1, 1, 0)]
NAND points: [(0, 0, 1), (0, 1, 1), (1, 0, 1), (1, 1, 0)]
NAND normalization failures: 0

$ python3 -I check_44.py
random networks tested: 1238 M-exchange violations: 0 comparator signatures: 0
crossbar table |x-y|: {(0, 0): 0, (0, 1): 1, (1, 0): 1, (1, 1): 0} crossed states: 0 0 M-exchange: True
NAND lattice under any of the 8 complementations: False

$ python3 -I check_33.py
Fibonacci point verified for n = 2..39
minor |det| = F_m verified for m = 2..29
escape switching: trials 3000 max (rounds - (r+1)) = 0
rank layers by reachability verified
Latin contraction root domains verified: 300
```

The preprint What Flow Reductions Need for RNC Speedups had no verification scripts.
