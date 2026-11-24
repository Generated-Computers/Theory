# Computer checks for "Barriers to Speeding Up Circuit Evaluation"

All scripts are plain Python 3 using only the standard library. Run each one from any directory as

```
python3 <script>.py
```

They do not read or write files. Theorem numbers refer to [`../paper.pdf`](../paper.pdf); see also Appendix A of the paper.

| Script | Source preprint | What it checks |
|---|---|---|
| `copy_program.py` | Four Barriers to Speeding Up Circuit Evaluation | The copy program of Section 3.1 as an append-only machine, for 2 ≤ d ≤ 6 and N < 60: all real values are 1, the read-adaptivity rank is ⌊(t−1)/d⌋, and the global table iteration needs exactly ⌈N/d⌉ rounds. |
| `correction_rank.py` | Four Barriers to Speeding Up Circuit Evaluation | The correction rank of Definition 3.1 on the copy program for radii L ≤ 4 and N < 40, over all block partitions (Theorem 3.2). |
| `padding.py` | Four Barriers to Speeding Up Circuit Evaluation | Exact Newton delay on ladders of length ≤ 11 (Theorem 3.5), the bound ρ+1 on random affine–product circuits, and output preservation, rank and frontier bounds of padded circuits with up to 8 ladders (Theorem 3.6). |
| `masked_prefix_or_check.py` | Prefix OR Defeats Treewidth and Curvature Measures | The masked prefix-OR identity y_e = x_e ⊕ OR_{i<e} x_i for m ≤ 11 on random inputs (Theorem 4.8). |
| `check_47_41.py` | Fractional Covers Do Not Certify Sequential Hardness | In exact rational arithmetic: the primal and dual certificates δ = h/2 and the integral catalyst height ⌈h/2⌉ (over all 2^h covers) of the matched-rail mirage for h ≤ 8 (Theorem 5.10); the general and incomparable bounds of Theorem 5.5 on 383 random DAGs with random feasible duals. It also checks the level structure of the catalyst compiler and threshold rounding of the group-6a paper on random circuits. |
| `separator_checks.py` | Separator Speedups Would Put MCVP in NC | Lemma 10.3 (constant-lag edges) and the tree height ⌈log₂ N⌉ for N ∈ {7,16,33,100,257,1000}; on 200 random executions with N ≤ 300, the frontier bound Bh of Lemma 10.12 at every cut and the counts used in the proof of Theorem 10.9 (heavy nodes, marked nodes, calls). |

## Output of the last run (24 November 2026)

All six scripts finished in under ten seconds each and were rerun for this paper.

```
$ python3 check_47_41.py                     # about 4 s
mirage: delta = h/2 certificates and integral chi = ceil(h/2) verified for h <= 8
concentration: instances 383 min ratio E/(bound/2) incomparable: 2.083064516129032 general: 1.6455479350536937
SeqNOR parents comparable: yes (x_j is an ancestor of x_{i-1} along the chain)
catalyst compiler level checks: 500  rounding checks: 500

$ python3 copy_program.py
copy program ok

$ python3 correction_rank.py                 # about 5 s
correction rank ok

$ python3 masked_prefix_or_check.py
masked prefix OR ok

$ python3 padding.py
S.2 ladder delay ok (k<=11)
Newton-Strahler bound ok on random circuits
S.4 padding: output preserved, rank>=k, frontier>=2w ok

$ python3 separator_checks.py
constant-lag edges (s,s+c): at most c per tree node: OK
frontier bound B*h and recursion call count 1+2*marked <= 1+2(N/B)(h+1): OK
```

## Checks without scripts

The grid pebbling price g+1 (Lemma 9.16) for g = 2, 3, 4 and the guard–router reduction (Theorem 8.19), with and without guards, on random DAGs with at most five vertices and k ∈ {2, 3}, were checked by exhaustive search with scripts that are not part of this repository.
