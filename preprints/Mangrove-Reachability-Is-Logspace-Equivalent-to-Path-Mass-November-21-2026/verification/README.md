# Computer checks for "Mangrove Reachability Is Logspace-Equivalent to Path Mass"

Plain Python 3, standard library only (no numpy). Run from any directory:

```
python3 check_mass.py                  # about 15 s
python3 check_mangrove.py              # about 3 min
python3 check_elimination_powers.py    # about 25 s
```

`common.py` holds the shared helpers. Walk counts are computed in three independent ways:
explicit depth-first enumeration of walks, with infinite counts detected through directed
cycles (`walk_counts`); the matrix sum I + A + ... + A^(n-1); and dynamic programming in
reverse topological order (`dag_counts`). The scripts compare them wherever they apply.
Random choices use the fixed seed 2026.

## What is checked

`check_mass.py` (Sections 3, 4, 5.1, 7, 8 of the paper)
- Theorem 3.1, Corollary 3.2, Proposition 3.3 on all 65,536 + 512 + 16 + 2 digraphs with
  self-loops on at most 4 vertices. The fixed point (PM) is compared with an exact rational
  solve. Every supersolution in the box x_v <= M(v)+1 dominates M. On cyclic graphs with at most
  3 vertices there is no nonnegative solution or supersolution in {0,...,8}^n, and every
  rational solution of (PM) has a negative entry.
- Theorems 4.2 and 4.3 (universal sink, terminal chain, quotient and remainder), and Theorem 5.1
  (rank formula = depth-first preorder index; stackless unranking inverts it). This is done on
  all labelled DAGs with at most 4 vertices, all upper-triangular DAGs on 5 vertices, and
  upper-triangular multigraphs with multiplicities at most 2 on 2 and 3 vertices.
- Theorem 7.1: the annotated verifier, implemented stage by stage as in the proof. It is run on
  every digraph on at most 3 vertices for every k in {0,1,2,3}, every (s,t) and every
  m in {0,...,4}^n plus the true mass vector, and on every digraph on 4 vertices with the true
  vector and its 8 one-coordinate perturbations. It accepts exactly when the instance is in
  STCON_sf and m is the true path-mass vector.
- Theorems 8.1-8.3 in exact rational arithmetic: the scaled row sums and margins, the
  stochastic rows, the probability 1/m(v) of every complete walk, and det(I - A + 1 e_s^T) - 1
  = M(s).

`check_mangrove.py` (Sections 5, 6 and Corollary 7.4)
- Mangroves: all labelled ones on at most 5 vertices, all upper-triangular ones on 6 vertices
  (randomly relabelled), and 300 random ones on 7 to 12 vertices.
- Theorem 5.3 (hidden two-tree normal form) and Lemma 5.4 (subtree sizes = masses; rank order
  = preorder).
- Every reduction of Lemmas 6.3-6.5 (Theorem 6.2), including the compositions REACH -> RANK
  (one query) and CONE -> REACH. The oracles REACH, MASS, PARENT, RANK, UNRANK, CONE first check
  their promise and raise an exception if a query violates it.
- Corollary 7.4(b): the total mangrove language is decided by the verifier with candidate
  masses produced from a "promise reachability algorithm". Four such algorithms are used: true
  reachability and three that answer at random on non-mangroves. This is checked on all
  digraphs with self-loops on at most 4 vertices.
- Corollary 7.4(a): the verifier fed by three adversarial mass procedures, correct only under
  the k-strong unambiguity promise, decides STCON_sf exactly (all digraphs on at most 3
  vertices, k <= 3). The interval argument recovers N(s,t) from a total STCON_sf decider (all
  labelled DAGs on at most 4 vertices, all upper-triangular DAGs on 5).

`check_elimination_powers.py` (Sections 9, 10, 11)
- Theorem 9.1: recurrence (W) = direct count of walks with interior in S_i, the bound
  W_i <= max N, and, on at most 4 vertices, the Schur complement (I - A)/S_i computed by exact
  inversion. This is done for every elimination order on labelled DAGs with at most 4 vertices,
  and for 8 random orders on each upper-triangular DAG on 5 vertices.
- Corollary 9.2; Proposition 9.3 (maximum over all orders = max over u != v of N(u,v));
  Proposition 9.4 (topological and reverse orders display only A; diamond chains r <= 6 have
  2^r walks and Boolean fills); Theorem 9.6 (Fill -> Mass through the induced graph and the
  terminal chain).
- Theorems 10.1 and 10.3 on all multigraphs with multiplicities at most 2 on at most 3
  vertices and all simple digraphs on 4 vertices (self-loops allowed), for k = 0..3 and all
  (s,t). Lemma 10.2 against full 2n x 2n block powers on 1500 random multigraphs. Tightness:
  the n-cycle passes the test at exponent nk and fails at nk+1 (n = 2..6, k = 1..4). Theorem
  10.5 (no-growth), Theorem 10.6 (mass as one entry of H^n, entries <= nk), both directions of
  Theorem 10.8 (400 random NGPower instances, and B_G^n on all labelled DAGs with at most 4
  vertices), Remark 10.10 (subdivision).
- Proposition 10.12 on 300 random layered strongly-few DAGs: the census output and the query
  bound 1 + 2k ceil(log2 |V_c|).
- Theorem 11.2: the chain argument on 400 random graphs that are reach-unambiguous from a root,
  with cycles allowed off the cone.

## Output (seed 2026)

```
$ python3 check_mass.py
Section 3: digraphs n<=4: 572 DAGs, 65494 cyclic; supersolution boxes: 572 DAGs, 501 cyclic (n<=3)
Sections 4-5.1: 1626 DAGs (incl. multigraphs), 12253 terminal-chain pairs, 19186 walks ranked/unranked
Section 7: 4079912 verifier calls, 951 accepted, all as predicted
Section 8: 572 labelled DAGs (n<=4)
TOTAL FAILURES: 0

$ python3 check_mangrove.py
Theorem 6.2: 7962 mangroves, 1971732 oracle queries, no promise violation
Corollary 7.4(b): 4213000 (graph, algorithm, s, t) cases, all correct
Corollary 7.4(a), mass -> STCON_sf: 42066 cases, all correct
Corollary 7.4(a), STCON_sf -> COUNT via the interval: 34526 (DAG, s, t) cases, all correct
TOTAL FAILURES: 0

$ python3 check_elimination_powers.py
Section 9: 21381 (DAG, order) pairs, diamond chains r<=6
Section 10: 85303 digraphs/multigraphs exhaustively (k=0..3), cycles n<=6, 400 NGPower instances
Proposition 10.12: 300 random layered strongly-few DAGs
Theorem 11.2: 400 random rooted reach-unambiguous graphs (cycles allowed off the cone)
TOTAL FAILURES: 0
```

These checks support the proofs in the paper; the proofs do not depend on them.
