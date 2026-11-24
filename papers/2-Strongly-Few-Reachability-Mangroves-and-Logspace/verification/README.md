# Computer checks for "Strongly-Few Reachability, Mangroves and Logspace"

Plain Python 3, standard library only. The scripts of the five constituent preprints are kept in
five subfolders, so that no file had to be renamed (two preprints each had a `walks.py`, two a
`common.py`) and no import or path had to be changed. Run every script from its own subfolder:

```
cd verification/<subfolder>
python3 <script>.py
```

The scripts print theorem numbers of the original preprints. The tables below give the numbers
of the consolidated paper (`../paper.pdf`). Each subfolder also contains `README-original.md`, the
README of the constituent preprint, with its full commands and outputs in the old numbering; the
`out_*.txt` files in `factorization/` are the recorded outputs of that preprint.

All scripts that finish within a few minutes were rerun on 24 November 2026 for this
consolidation; every rerun reported 0 failures or "all checks passed". Two long runs were not
rerun (marked below); their recorded outputs are in `factorization/out_obstructions.txt` and
`factorization/out_density8.txt`. The proofs do not depend on any of these checks.

## `reachul/` (from "Strongly-Few Reachability Is in ReachUL")

| script | what it checks (consolidated numbering) | time | rerun result |
|---|---|---|---|
| `check_capped.py [seed]` | Listings 1-2 and Theorem 3.8 on all 4,213,000 instances with n <= 4, k <= 3, on random simple digraphs (5 <= n <= 7) and, in the form of Proposition 3.9, on random multigraphs; Lemmas 3.3, 3.5, 3.6 and Remark 3.7 | 7 s | 0 mismatches |
| `check_budgets.py [seed]` | Theorem 2.25 and Corollary 2.27 on about 2.1·10^7 (graph, root, budget) triples; Remark 2.28 for B <= 12; Listing 3 / Theorem 4.1; Lemma 4.3; the reductions of Theorem 4.4 and Corollary 4.6 | 39 s | 0 mismatches |
| `check_lift.py [seed]` | the controller of Definition 5.7 with its prime and all alpha scanned; Lemma 5.3 (separating points), Lemma 5.6 (certified fibres exact), Remark 5.9 (diamond, primes 7 and 5); STCON_sf through U(G) and the lift (Corollary 5.11) | 9 s | 0 mismatches |
| `walks.py` | helper module (reference walk counts) | - | - |

## `thresholds/` (from "Strongly-Few Reachability with Binary Thresholds Is PL-Complete")

| script | what it checks | time | rerun result |
|---|---|---|---|
| `rooted_completeness.py [nmax]` | Theorem 2.25 on 1,090,342 budget vectors; Lemma 7.2 (layering, with n+1 and 2n layers; n layers fail on 409 instances as a control); Lemma 7.1 for k = 2, 3; the two-cone reduction of Theorem 7.6; the reduction of Lemma 7.4 on 3000 random reach-unambiguous graphs | 137 s | 0 failures |
| `binary_threshold.py` | the hardness reduction of Theorem 9.1 on toy PL machines (every R in [0, 2^T], T <= 5); the comparison machine with exactly K+1 accepting branches; the GapL conjunction of the membership proof; the length bound and reductions of Theorem 9.4 | 2 s | 0 failures |
| `fingerprints.py [trials]` | Theorem 11.1 (a)-(c) on 10,654 endpoints with real primes; Lemma 11.2 against enumerated walks; the root-budget decision of Theorem 11.3; controls: floor decoding wrong on 181 endpoints, one evaluation point wrong on 518 | 8 s | 0 failures |
| `zero_test.py` | Propositions 10.1, 10.2, 10.3 | 1 s | 0 failures |
| `strongfew_hardness.py` | the construction of Theorem 8.1 with subdivided parallel transitions | < 1 s | 0 failures |
| `walks.py` | helper module | - | - |

## `logspace/` (from "Total Strongly-Few Reachability Is in Logspace for Logarithmic Block-Cyclomatic Width")

| script | what it checks | time | rerun result |
|---|---|---|---|
| `choice_compressed.py [seed]` | Theorem 12.1 on all 29,853 DAGs with <= 5 vertices; the decider of Theorem 12.4 with replayed choice strings in 36,198 runs; the bound of Lemma 12.3 (attained) | 14 s | 0 errors |
| `bypass_pruning.py [seed]` | the decider of Theorem 13.6; Lemmas 13.2-13.4 and Corollary 13.5, with GF(2) independence of the bypass cycles checked at 105,133 pushes, on cyclic inputs too | 5 s | 0 errors |
| `cycle_signatures.py [seed]` | Theorem 14.4 (signature counting and cycle detection); Lemma 15.1 against Tarjan's algorithm; Lemma 15.2 (route lemma and product formula); the decider of Theorem 15.3 in 301,045 runs | 81 s | 0 errors |
| `robustification.py [seed]` | all claims of Theorem 17.1 (including infinite counts and connectivity); Propositions 16.1, 16.2 and 17.4 | 1 s | 0 errors |
| `examples.py` | Table 2 (Remark 15.6) | < 1 s | table reproduced |
| `common.py` | helper module | - | - |

## `factorization/` (from "Strongly-Few Path Matrices Factor into Logarithmically Many Mangroves")

| script | what it checks | time | rerun result |
|---|---|---|---|
| `check_fixedpoint.py` | Theorem 18.1 by exhaustive search over all candidate matrices; Theorem 2.25 in the form of Remark 2.26 and Corollary 2.29 on 1,131,102 cases, cyclic graphs included | 25 s | all checks passed |
| `check_factorization.py` | Lemma 19.1, Theorem 19.2, Corollary 19.3, Theorem 20.1, Corollary 20.2, Theorem 20.3, Theorem 21.2 (factors multiplied back and verified to be mangrove factors), Remark 20.6, Theorems 22.1, 22.2, 26.3, 26.4; all 33,867 DAGs with <= 6 vertices and 300 random graphs | 26 s | all checks passed |
| `check_cyclomatic.py` | Lemma 23.2, Theorems 23.3, 23.5, 23.6, 23.8 (186 graphs with r = 2^c), 25.1, and c >= l(r) (Theorem 24.1) on 707,284 trimmed two-terminal DAGs | 36 s | all checks passed |
| `check_addition_chains.py` | Theorem 24.1: the construction for r <= 128 and the extraction from 3000 random graphs | 1 s | all checks passed |
| `check_density.py` | Table 3 for n <= 7, Theorem 26.1, Proposition 26.2 | 4 s | all checks passed |
| `check_density.py 8 6` | Table 3, row n = 8 (pruned search) | about 7 min | **not rerun**; recorded output `out_density8.txt` |
| `check_obstructions.py` | Theorem 25.4 and Remark 25.5 on 797,325 pairs (H, k); the extraction of Theorem 25.6; the families F_1, F_2, F_3 of Remark 25.7 | about 10 min | **not rerun**; recorded output `out_obstructions.txt` |
| `explore_min_factors.py` | Remark 21.6: least numbers of mangrove factors for T_4, T_5, D_2 | 4 s | 2, 3, 2 reproduced |
| `sfcommon.py` | helper module | - | - |

## `mangroves/` (from "Mangrove Reachability Is Logspace-Equivalent to Path Mass")

| script | what it checks | time | rerun result |
|---|---|---|---|
| `check_mass.py` | Theorem 18.3, Corollary 18.4, Proposition 18.5; Theorems 28.2, 28.3, 29.1; the verifier of Theorem 31.1 in 4,079,912 runs; Theorems 32.1-32.3 | 14 s | 0 failures |
| `check_mangrove.py` | Theorem 29.3, Lemma 29.4, every reduction of Lemmas 30.3-30.5 against promise-checking oracles (1,971,732 queries, no violation); Corollary 31.4 (a), (b) with adversarial promise algorithms; Lemma 31.3 | 171 s | 0 failures |
| `check_elimination_powers.py` | Theorem 33.1, Corollary 33.2, Propositions 33.3, 33.4, Theorem 33.6; Theorems 34.1, 34.3 (with tightness on n-cycles), Lemma 34.2, Theorems 34.5, 34.6, 34.8, Remark 34.10, Proposition 34.12; the chain argument of Theorem 35.2 | 25 s | 0 failures |
| `common.py` | helper module | - | - |
