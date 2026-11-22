# Checking scripts for the binary-threshold and completeness results

Plain Python 3, standard library only. `walks.py` holds the shared helpers: exact walk
counts with the paper's convention (edge sequences, repeated vertices allowed, the empty walk
counted, parallel edges distinct, value `INF` when a cycle lies between the endpoints). The
counts are computed independently of the constructions: by dynamic programming over walk
lengths with the cycle criterion of Lemma 2.1, or by dynamic programming over a topological
order on acyclic graphs. Run from this folder:

```
python3 rooted_completeness.py [nmax]   # default nmax = 4; about 135 s
python3 binary_threshold.py             # about 2 s
python3 fingerprints.py [trials]        # default 3000; about 8 s
python3 zero_test.py                    # about 1 s
python3 strongfew_hardness.py           # under 1 s
```

## What is checked

`rooted_completeness.py` (Section 3, Lemmas 2.8 and 2.9). On all 66,066 simple digraphs with
at most 4 vertices (self-loops allowed) and every root (263,714 rooted instances):

- the budget-mass truncation lemma (Lemma 2.8), for all budget vectors in {0,1,2}^V when
  n <= 3 and 4 random ones when n = 4;
- the DAG layering of Lemma 3.1 with layers 0..n and with the source's layers 0..2n-1:
  reach-unambiguity from (s,0) agrees with reach-unambiguity of G from s, and (s,0) reaches
  c_t iff s reaches t. Control: layers 0..n-1 give a wrong answer on 409 rooted instances,
  so the depth n is needed;
- the prefix gadget (Lemma 2.9) for k = 2, 3: N_H(r,v) = k N_G(s,v), INF included, and
  RootFew_k validity agrees;
- the two-cone reduction of Theorem 3.5 for k = 1, 2: <H,r,z> in FBFew_{k,1} iff
  <G,s> in RootFew^rec_k.

It also checks the complement reduction of Lemma 3.3 on 3000 random reach-unambiguous
"configuration graphs" with random accepting sets.

`binary_threshold.py` (Section 5).

- (H) Theorem 5.1, hardness. Toy machines are time-layered graphs in which every vertex
  below the last layer has exactly two distinct successors in the next layer, as in Lemma 5.2,
  including configurations unreachable from the start. For full binary trees with T <= 5
  every rejecting count R in [0, 2^T] is realized, and there are 400 random merging machines
  with T <= 6. On every instance: the graph is a simple DAG, N(a,b) = 2^{T+1} + R, every other
  ordered pair has at most 2^T walks, and validity for K = 2^{T+1} + 2^{T-1} - 1 holds iff
  R <= 2^{T-1} - 1 iff A > 2^{T-1}. The source's complement version (accepting sink,
  K = 2^{T+1} + 2^{T-1}) is valid iff A <= 2^{T-1}.
- (M) Theorem 5.1, membership. The MSB-first comparison machine has exactly K+1 accepting
  branches (K = 0..600, three padded bit lengths each). The conjunction "no walk of length
  n, s reaches t, (K+1) - N^{<=n-1}(u,v) > 0 for all u,v" agrees with membership in
  BIN-STCON_sf on all digraphs with n <= 3, all s, t and K = 0..5.
- (P) Theorem 5.4. N(s,t) >= k+1 iff N^{<=(k+2)n}(s,t) >= k+1; N(s,t) < INF iff no s-t
  walk has length in [n, 2n]; the (k+1)-fold prefix sends reachability to a count >= k+1
  and non-reachability to 0. All digraphs with n <= 3, k = 1, 2, 3.

`fingerprints.py` (Section 7). There are 3000 random multigraphs (loops and parallel edges,
up to 6 vertices and 15 edge occurrences), with a random root, B in 1..6 and K in 1..4. The
script uses q0 = (B-1) C(K+1,2) + 1, the least prime p > max(m, q0) and A = {0, ..., q0-1}.
The census D_v is computed by breadth-first search in the aggregate lift. Checked:
Theorem 7.1 (a) threshold equivalence for all t <= K, (b) the ceiling decoding
min{c_v, K+1} = min{ceil(D_v/q0), K+1}, and (c) the maximum variant. It also checks the
faithfulness of the lift (Lemma 7.2) against explicitly enumerated walks, and the root-budget
decision of Theorem 7.3 against exact counts, with A = {0..q0-1} and with a random q0-subset
of F_p. Controls: the floor in place of the ceiling is wrong on 181 endpoints, and the
maximum over the single point alpha = 0 is wrong on 518 endpoints.

`zero_test.py` (Section 6). Proposition 6.1 is checked on all digraphs with n <= 3, all s, t
and k = 1, 2, 3, and on 3000 random digraphs with n = 4, 5. Propositions 6.2 and 6.3 are
checked on 3000 random instances each, the latter on multigraphs. In every case g = 0 iff the
instance is a member.

`strongfew_hardness.py` (Section 4, Theorem 4.1). There are 2000 random acyclic
configuration multigraphs. After subdividing every transition occurrence and adding the
collector, the graph is simple and acyclic, every ordered pair has at most |C| * P walks,
counts between configurations are preserved, and s reaches t iff an accepting configuration
is reachable.

## Output

```
$ python3 rooted_completeness.py
graphs: 66066  rooted instances: 263714
(T) truncation lemma: 1090342 budget vectors, 0 failures
(L) layering depth n and 2n-1: 0 failures
    control depth n-1: fails on 409 rooted instances (expected > 0)
(P) prefix gadget k=2,3: 0 failures
(C) two-cone reduction k=1,2: 0 failures
complement reduction (recognition hardness): 3000 tests, 0 failures

$ python3 binary_threshold.py
(H) gadget instances: 467, failures: 0, all R in [0,2^T] realized for T<=5: True
(M) comparison machine: K = 0..600, 3 bit lengths each, failures: 0
(M) GapL conjunction vs BIN-STCON_sf: 28044 instances, 0 failures
(P) one-pair cap checks: 32718, failures: 0

$ python3 fingerprints.py
endpoints checked: 10654
(1) ceiling decoding failures: 0
(2) threshold equivalence failures: 0
(3) maximum-variant failures: 0
(4) lift faithfulness: 2744 instances enumerated, failures: 0
(5) root-budget decision (A = {0..q0-1}) failures: 0
(6) root-budget decision (random A) failures: 0
control: floor formula wrong on 181 endpoints
control: single evaluation point alpha=0 wrong on 518 of 10599 endpoints

$ python3 zero_test.py
(U) uniform threshold: 17022 instances (1042 members), 0 failures
(B) pair budgets: 3000 instances (987 members), 0 failures
(R) root budgets (multigraphs): 3000 instances (766 members), 0 failures

$ python3 strongfew_hardness.py
StrongFewL construction: 2000 instances, 0 failures
```

These checks support the proofs in the paper; the proofs do not depend on them.
