# Checking scripts for the parameterized deciders

Plain Python 3, standard library only. Run from this directory (the scripts import
`common.py`):

```
python3 choice_compressed.py [seed]   # Section 3; about 14 s
python3 bypass_pruning.py [seed]      # Section 4; about 5 s
python3 cycle_signatures.py [seed]    # Sections 5 and 6; about 80 s
python3 robustification.py [seed]     # Sections 7 and 8; about 2 s
python3 examples.py                   # Table 1; under 1 s
```

The default seed is 2026. Every script compares against walk counts computed independently in
`common.py`. The reference count is N(u,v) = sum_{l<n} (A^l)_{uv}. It is set to infinity exactly
when a vertex on a directed cycle is reachable from u and reaches v. Paths with distinct
vertices are counted by depth-first enumeration. Connectivity tests, done by Reingold's
algorithm in the paper, are done here by breadth-first search.

## What is checked

`choice_compressed.py` (Theorem 3.1, Lemma 3.3, Theorem 3.4)
- The branching-budget identity L_a = 1 + sum_v N(a,v)(d+(v) - 1) on all 29,853 labelled DAGs
  with at most 5 vertices.
- The total decider of Theorem 3.4 as stated. Its state between steps is only the choice
  string sigma, the depth, the node counter and the target counter, and the current vertex is
  recomputed by replaying sigma. It applies the orientation rule, the depth, node, target and
  stack caps, and the cap k*lambda - 1. It is run on all digraphs with loops on at most 3
  vertices (k = 1..4), all loopless digraphs on 4 vertices (k = 1..3) and 1,500 random
  digraphs and DAGs on 5-9 vertices (k around the largest finite count), for two (s,t) pairs
  each. Decisions are compared with membership in STCON_sf, and all pair counts are compared on
  valid inputs. The longest choice string is compared with k*lambda - 1.

`bypass_pruning.py` (Lemmas 4.2-4.4, Corollary 4.5, Theorem 4.6)
- The decider of Theorem 4.6: rejection of loops and antiparallel pairs, the cycle test along
  the non-forest arcs of the canonical spanning forest, and the pair recounts with pruned
  searches. It is run on all loopless digraphs with at most 4 vertices and on 600 random ones.
- At every push, the explicit bypass cycle C_i (two admissible successors joined by a BFS path
  avoiding the earlier frames and the new frame vertex), and a GF(2) rank test showing that the
  cycles of all active frames are independent.
- The number of frames is at most the cycle rank of the root's weak component on every search,
  including pruned searches for all pairs on every invalid loopless input (cyclic ones too), and
  at most k*tau_plus - 1 on valid inputs.

`cycle_signatures.py` (Lemmas 5.1-5.2, Theorem 5.4, Lemmas 6.1-6.2, Theorem 6.3)
- Signature counting: the number of z in GF(2)^c with X(z) a directed x-y path equals the
  number of directed paths from x to y. Checked on all digraphs with loops on at most 3
  vertices, all loopless digraphs on 4 vertices and 300 random digraphs on 5-8 vertices with
  cycle rank at most 9, cyclic ones included, with antiparallel arcs as parallel undirected
  edges.
- Signature cycle detection against a topological sort, on the same graphs.
- The Menger block test of Lemma 6.1 against Tarjan's algorithm, on all 1,099 labelled
  undirected graphs with at most 5 vertices and 300 random ones on 6-9 vertices.
- The route lemma: the separators of (u,v) are linearly ordered by the relation of Lemma 6.2(a),
  consecutive route vertices share exactly one block, and the number of directed simple u-v
  paths is the product of the blockwise signature counts. Checked for all pairs on all 59,809
  digraphs with at most 5 vertices and no loops or antiparallel pairs, and on 400 random ones
  on 6-10 vertices with bcw <= 8 (cyclic ones included).
- The decider of Theorem 6.3 (blockwise cycle test, saturated products) against brute force for
  k = 0..4 on the same graphs, and that no signature longer than bcw(G) is ever enumerated.

`robustification.py` (Theorem 8.1, Propositions 7.1, 7.2, 8.4)
- The robustification G_rho, for all digraphs with loops on at most 3 vertices with rho = 2,
  all loopless digraphs on 3 vertices with rho = 3, and 60 random digraphs on 4-6 vertices with
  rho in {2, 3, 4}. Checked: the counts in (1), finite and infinite; multiplicity at most one
  for every other pair; equivalence of k-strong unambiguity for k = 1..4; preservation of the
  s-t count and of {x : s ~> x ~> t} for all original s, t; minimum degree rho; vertex
  connectivity at least rho by deleting every set of rho - 1 vertices (for rho <= 3, 641 of the
  654 cases); that the neighbourhood of a private vertex separates; edge connectivity rho by
  maximum flow; diameter at most 4.
- Path flow through vertices and arcs, and dominators, by explicit path enumeration on 400
  random DAGs. Rank-one insertion with C_yx = 0 and deletion against recomputed counts, and that
  insertion with C_yx > 0 creates a cycle.
- The second-path construction: N(s',t') = 1 + N(s,t) on 300 random DAGs.

`examples.py` computes Table 1: k* = max N(u,v), lambda, gamma, bcw and the longest choice
string of Theorem 3.4 for the zigzag, diamond comb, comb and subdivided grid families.

## Output with the default seed

```
$ python3 choice_compressed.py
branching-budget identity: 29853 DAGs on <= 5 vertices checked
decider cases: 36198, of which valid inputs: 6890
rejections by cap (invalid inputs): {'target cap': 1292, 'depth cap': 2000, 'stack cap': 3512, 'node cap': 18}
largest |sigma| on valid inputs: 8, largest ratio |sigma|/(k*lambda-1): 1.000
errors: 0
$ python3 bypass_pruning.py
decider cases: 9424, valid inputs: 1188
rejections: {'node cap': 190, 'cycle found': 309, 'target cap': 722, 'depth cap': 32}
invalid loopless inputs traversed for all pairs: 8236
pushes checked for GF(2) independence: 105133
largest number of active frames: 6; largest frames/gamma: 1.000
errors: 0
$ python3 cycle_signatures.py
signature counts checked: 62860 pairs; signature cycle detection checked: 4926 graphs
Menger block test vs Tarjan: 1399 undirected graphs
product formula checked on 60209 graphs (all pairs); decider runs: 301045; largest signature length used: 8 (never above bcw)
errors: 0
$ python3 robustification.py
robustification: 654 (G, rho) pairs; vertex connectivity by exhaustive deletion on 641 of them
path flow: 400 DAGs; insertions: 397; deletions: 366
second-path construction: 300 DAGs
errors: 0
$ python3 examples.py
family               n   k*  lambda  gamma  bcw  accept  |sigma|  k*lambda-1
zigzag 2             6    2       1      1    1    True        1           1
zigzag 4            10    2       1      3    3    True        1           1
zigzag 8            18    2       1      7    7    True        1           1
diamond comb 2       8    2       2      2    1    True        2           3
diamond comb 4      16    2       4      4    1    True        2           7
diamond comb 8      32    2       8      8    1    True        2          15
comb 2               6    1       2      0    0    True        1           1
comb 4              12    1       4      0    0    True        3           3
comb 8              24    1       8      0    0    True        7           7
subdivided grid 2    9    2       1      4    4    True        1           1
subdivided grid 3   22    2       1     12   12    True        1           1
```

These checks support the proofs in the paper; the proofs do not depend on them.
