# Checking scripts for the strongly-few reachability manuscript

Plain Python 3, standard library only. Run from this directory:

```
python3 check_capped.py [seed]    # default seed 2026; about 7 s
python3 check_budgets.py [seed]   # about 37 s
python3 check_lift.py [seed]      # about 9 s
```

`walks.py` holds the reference walk counts, computed independently of the algorithms
under test: `N(u,v) = inf` is decided by the criterion of Lemma 2.2 (some vertex on a
cycle lies between u and v), finite values by summing powers of the multiplicity matrix
up to length n-1, and bounded counts `N^{<=L}` by dynamic programming over lengths.
Graphs are simple digraphs with self-loops allowed, or multigraphs given as lists of edge
occurrences (parallel occurrences are distinct, as in the paper).

`check_capped.py` implements Listings 1 and 2 (Section 3) exactly and checks:

- all simple digraphs with n <= 4 vertices, all (s,t), k = 0,1,2,3: the decider accepts
  exactly STCON_sf (4,213,000 instances, 9,942 accepted);
- that running Listing 2 separately for each (s,t) agrees with the all-pairs run;
- random simple digraphs with 5 <= n <= 7 (134,326 instances) and random multigraphs with
  parallel edges in the occurrence-indexed form of Proposition 3.9 (83,546 instances);
- Lemmas 3.3, 3.5 and 3.6 along the way;
- Remark 3.7: on the directed n-cycle (n <= 7, k <= 4) the unfolding to depth nk-1 has
  exactly nk nodes, each endpoint k times, and the depth-(nk-1) variant of Listing 2
  accepts the cycle, while the real decider rejects it.

`check_budgets.py` checks:

- Theorem 4.1 and Corollary 4.2 for every budget vector in {0,..,3}^n on all simple
  digraphs with n <= 3, and every vector in {0,1,2}^4 on all simple digraphs with n = 4,
  every root (21,332,488 triples), plus random multigraphs; on valid instances also that
  all walks from the root have length <= B-1;
- Remark 4.3 for B = 1..12;
- Theorem 4.4: Listing 3 with its recounts accepts exactly RootBudget (171,064 instances);
- Lemma 4.6 (universal source), including infinite values, on all simple digraphs with
  n <= 3 and on random multigraphs, and PairBudget through U(G) (Theorem 4.7);
- Corollary 4.9: the selected-root and two-cone reductions.

`check_lift.py` runs the controller of Definition 5.7 with the prime of Section 5
(p = least prime > max{m, B*S, 2}), scanning every alpha in F_p, and checks:

- it accepts exactly RootBudget on all simple digraphs with n <= 3, every root and every
  budget vector in {0,1,2}^n (41,766 instances), and on 3000 random multigraphs with
  n <= 6, m <= 8;
- Lemma 5.3: every valid instance has a certified alpha, and at most (B-1)S values of alpha
  fail certification;
- Lemma 5.6: for every certified alpha, on valid and invalid instances alike, the fibre
  sizes equal the bounded walk counts N^{<=B}(r,v);
- Remark 5.9 (the diamond): budgets (1,1,1,2) give p = 7, only alpha = 6 fails
  certification, and the instance is accepted; budgets (1,1,1,1) give p = 5, only
  alpha = 4 fails, and the budget comparison rejects (fibre size 2 > 1);
- Corollary 5.11: STCON_sf decided through U(G) and the certified lift on 60 random small
  instances.

Output with the default seed:

```
$ python3 check_capped.py
exhaustive n<=4, k<=3: 4213000 instances (G,s,t,k), 9942 accepted, 0 mismatches
Listing 2 run per (s,t) agrees with the all-pairs run on 3000 random instances
random simple digraphs 5<=n<=7: 134326 instances, 28446 accepted, 0 mismatches
random multigraphs n<=5, m<=8 (parallel edges): 83546 instances, 22154 accepted, 0 mismatches
Remark 3.7 confirmed on directed n-cycles, n<=7, k<=4

$ python3 check_budgets.py
Theorem 4.1 / Corollary 4.2, all simple digraphs n<=4: 1027204 valid and 20305284 violating (graph, root, kappa) triples, 0 mismatches
Theorem 4.1 / Corollary 4.2, random multigraphs n<=5: 98858 valid, 80996 violating, 0 mismatches
Remark 4.3 confirmed for B = 1..12
Theorem 4.4 (Listing 3): 171064 RootBudget instances, 8404 accepted, 0 mismatches
Lemma 4.6 on all simple digraphs n<=3 and 300 random multigraphs; PairBudget via U(G): 5070 instances, 140 accepted, 0 mismatches
Corollary 4.9 reductions (selected roots, two cones): 6000 instances, 1196 accepted, 0 mismatches

$ python3 check_lift.py
exhaustive n<=3, kappa in {0,1,2}^n, all alpha scanned: 41766 instances, 394 accepted;
  valid: 4186 (each had a certified alpha; max (#bad alpha)/((B-1)S) = 0.000);
  invalid with no certified alpha: 3715; invalid with a certified alpha (rejected by the budget comparison): 19943; Lemma 5.6 held for every certified alpha
random multigraphs n<=6, m<=8, all alpha scanned: 3000 instances, 724 accepted; valid 1576; invalid uncertified 91; invalid certified 670; max bad ratio 0.071
Remark 5.9 confirmed: budgets (1,1,1,2): p=7, only alpha=6 collides, accepted; budgets (1,1,1,1): p=5, only alpha=4 collides, rejected by the fibre count 2 > 1
Corollary 5.11 (STCON_sf via U(G) and the certified lift): 60 instances, 17 accepted, 0 mismatches
```

In the exhaustive lift run the remaining 13,922 instances have B = 0 or kappa(r) = 0 and
are rejected at once. Simple digraphs with at most three vertices have no two distinct
equal-length walks with a common endpoint on valid instances, so no alpha fails there;
the random multigraphs (with parallel edges and up to six vertices) exercise collisions.

The checks cover the finite, combinatorial statements. The complexity-theoretic parts
(logspace and pushdown implementations, the composition with a ReachUL oracle, and the
imported theorems) are not checked by computer. The proofs do not depend on these checks.
