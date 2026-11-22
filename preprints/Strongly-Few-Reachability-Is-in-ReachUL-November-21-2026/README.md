# [Strongly-Few Reachability Is in ReachUL](paper.pdf)

**Author:** Generated Computers

**Date:** November 21, 2026

## Citation

```bibtex
@misc{GC:Strongly-Few-Reachability-Is-in-ReachUL-November-21-2026,
  author = {{Generated Computers}},
  title = {{Strongly-Few Reachability Is in $\mathrm{ReachUL}$}},
  howpublished = {Generated Computers preprint, manuscript 012a},
  year = {2026}
}
```

## Lean

This manuscript is not formalized yet.

## Sources

Rewritten from the following internal note:
- "Total Strongly-Few Directed Reachability: Unambiguity, Auxiliary Pushdowns, Exact
  Counting, and the StrongFewL Boundary" (`STCONsf_Class_Containments_Revised.pdf`,
  9 September 2026, 72 pages). Used: Sections 1 and 2; Section 3 (Definition 3.1,
  Lemmas 3.2-3.6, Remark 3.7, Listings 1-2, Theorem 3.8, Proposition 3.9, Caution 3.10,
  the AuxPDA implementation, Lemma 3.11, Theorem 3.12); Section 4 (Definition 4.1,
  Theorem 4.2, Corollary 4.3, Remark 4.4, Theorem 4.5, Construction 4.6, Lemma 4.7,
  Definition 4.8, Theorems 4.9-4.10, Definition 4.11, Corollary 4.12); Sections 5.1-5.3
  (Lemma 5.1, Section 5.2 with Lemmas 5.2-5.4, Section 5.3, Theorem 5.5, Corollary 5.6,
  the consequences, Remark 5.7); Theorem 7.1, restricted to ReachUL, LOGDCFL and SC^2;
  Appendices A36 (boundary cases) and A37 (Listing 3).
- The main theorem was also announced in arXiv:2610.09139 (October 2026).

## Status

- **Main result (proved in full from the imported theorems below):** STCON_sf is in
  ReachUL (Corollary 5.11), and so are the root-budget, pair-budget, selected-root and
  two-cone languages with budgets of polynomial total size (Theorem 5.8, Corollary 5.11)
  and the fail-closed compiler languages for computation paths of logspace machines
  (Corollary 6.1). Consequences by known containments: UL ∩ coUL, LOGDCFL ⊆ SC^2 and
  DSPACE(log^2 M / log log M), M the input length. New ingredients: the exact budget-mass
  truncation lemma (Theorem 4.1, an elementary pigeonhole argument that we have not seen
  stated in this form, not claimed as a significant novelty), the observation that a
  certified lift gives exact bounded walk counts on every input (Lemma 5.6), and the
  resulting total controller (Theorem 5.8).
- **Imported (stated in Section 2.3, not reproved):** Sudborough 1976/1977/1978
  (LOGDCFL = polynomial-time logspace DAuxPDA); Cook 1979 (such automata are in SC^2);
  Lange 1997 (STCON_ru is in ReachUL); the three-outcome normal form for ReachUL (exactly
  one non-"?" computation path, carrying the correct answer), which Garvin, Stolee, Tewari
  and Vinodchandran use in the proof of their Lemma 4 and derive from closure under
  complement (Buntrock, Jenner, Lange and Rossmanith 1991; their Proposition 3);
  Allender-Lange 1998. ReachFewL = ReachUL (Garvin et al. 2014) is quoted but not needed.
  The oracle composition L^ReachUL ⊆ ReachUL, a sketch in Garvin et al., is written out
  here from the normal form (Lemma 5.1), with adaptive queries and query symbols
  regenerated from a saved configuration.
- **Independent work:** the capped depth-first search proving STCON_sf ∈ LOGDCFL ⊆ SC^2
  (Section 3) is in the source note of 9 September 2026. Cheng and Wu obtained it
  independently (arXiv:2609.23603, Appendix D), and also note that it answers the SC^2
  question of Apers and Edenhofer.
- **Prior work now attributed:** the hash-layer-query plan of Section 5 is that of Garvin et al. (ECCC
  TR11-060, Theorem 8 and Algorithm 1); the source cited them only for the class equality
  and oracle closure. ReachUL ⊆ LOGDCFL is attributed to Buntrock et al. 1991 and Lange
  1997 (as recorded by Apers and Edenhofer), with a self-contained depth-first-search proof
  (Proposition 2.13); the source cited Lange 1997 alone. ReachUL ⊆ UL ∩ coUL is credited
  (Garvin et al.; Pavan, Tewari and Vinodchandran for ReachFewL).
- **Correction: the composition argument of source Lemma 5.1.** The source guessed an
  answer bit and ran "a reach-unambiguous recognizer for the oracle language or its
  complement", claiming that exactly one returning path exists. This fails when the
  recognizer can reach several accepting configurations (each by its own unique path):
  all of them return to the same controller configuration, which then has several
  incoming paths. The proof now uses the three-outcome normal form (a unique non-"?"
  path), as Garvin et al. do.
- **Correction: source Remark 5.7.** It used F_7 for both budget vectors of the diamond.
  For budgets (1,1,1,2) the prescribed prime is 7 (collision at alpha = 6), but for the
  lowered budgets (1,1,1,1) it is 5 (B = 4, S = 0; collision at alpha = 4). Recomputed
  (Remark 5.9); the conclusion is unchanged.
- **Other changes.** Source Theorem 7.1 said clocking is needed for finiteness; it is not,
  since configuration graphs of logspace machines are finite and a reachable cycle makes a
  count infinite and is rejected (Corollary 6.1). The space bound answering Apers and
  Edenhofer is stated in terms of the input length M (log M = O(log n) when k is
  polynomial in n). Budgets are unary by definition, and binary budgets with a checked
  polynomial cap reduce to them (Remark 2.5); this replaces the source's "row sums
  polynomially bounded" hypotheses. Running times are given explicitly (O(M^4) for the
  simple decider and for root budgets, O(M^6) for multigraphs). The controller decides
  at the first certified lift, which is equivalent to the source's rule because all
  certified lifts give the same counts. The certification query's reliance on the
  empty-walk convention is noted, with a pendant-vertex alternative (Table 1). The claim
  that the two-cone family "strictly contains" the strongly-few family is stated as a
  statement about instances. The prime bound p > max{m, BS, 2} with (B-1)S < p, the
  fingerprint degree bound d-1 <= B-1, and the role of p > m (distinct, nonzero edge
  indices mod p) were checked and kept.
- **Left out (in the companion manuscript 012b, mentioned in one sentence each):**
  rooted and two-cone ReachUL-completeness (source Sections 5.4-5.5), the C=L zero test
  (Section 6, and the C=L part of Theorems 1.1 and 7.1), StrongFewL-hardness (Theorem 7.2)
  and Problem 7.3, the NL bound by collision averaging (A1), the binary-threshold
  classification (A2), and the polynomial-threshold #L theorem (A34). Also omitted:
  Listing 4 of A37 (stackless unranking, which belongs to structural appendices not used
  here) and the rows "positive weights" and "matrix convention" of A36.
- Computer checks are in [`verification/`](verification/README.md): the capped decider on
  all 4,213,000 instances with n <= 4, k <= 3 and on random graphs and multigraphs; the
  truncation theorem on about 2.1·10^7 (graph, root, budget) triples; the full-unfolding
  decider, the universal-source bijection and the selected-root and two-cone reductions;
  the certified-lift controller with its actual primes and all evaluation points; the
  tightness Remarks 3.7 and 4.3 and the diamond of Remark 5.9. No mismatch. The proofs do
  not depend on them.
- Not refereed.
