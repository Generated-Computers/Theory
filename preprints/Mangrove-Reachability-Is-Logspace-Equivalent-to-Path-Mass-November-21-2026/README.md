# [Mangrove Reachability Is Logspace-Equivalent to Path Mass](paper.pdf)

**Author:** Generated Computers

**Date:** November 21, 2026

## Citation

```bibtex
@misc{GC:Mangrove-Reachability-Is-Logspace-Equivalent-to-Path-Mass-November-21-2026,
  author = {{Generated Computers}},
  title = {{Mangrove Reachability Is Logspace-Equivalent to Path Mass}},
  howpublished = {Generated Computers preprint, manuscript 012e},
  year = {2026}
}
```

## Lean

This manuscript is not formalized yet.

## Sources

Rewritten from the following internal note:
- "Total Strongly-Few Directed Reachability: Unambiguity, Auxiliary Pushdowns, Exact Counting,
  and the StrongFewL Boundary" (`STCONsf_Class_Containments_Revised.pdf`, 9 September 2026,
  72 pages). Used: Appendices A23 (Theorem A23.1, Remark A23.2, Problem A23.3), A25 (Theorem
  A25.1, Corollary A25.2, Proposition A25.3), A26 (Theorems A26.1, A26.2, Corollary A26.3), A27
  (Theorem A27.1, Corollary A27.2, Theorem A27.3), A28 (Theorem A28.1, Remark A28.2), A29
  (Theorems A29.1-A29.3), A30 (Theorem A30.1, Corollary A30.2, Definition A30.3, Proposition
  A30.4, Theorem A30.5, Cautions A30.6-A30.7), A31 (Theorem A31.1, Lemma A31.2, Theorems
  A31.3-A31.5, Definition A31.6, Theorem A31.7, Remark A31.8), A32 (Theorems A32.1, A32.2,
  Problem A32.3), A33 (Theorem A33.1, Caution A33.2), and Open Problems A35.1, A35.2, A35.3,
  A35.10. Section 2 (Definitions 2.1-2.3) was used for the conventions only.

## Status

- **Main results, proved in full.** (i) On inputs promised to be mangroves (all-pairs walk
  counts at most 1), six problems are pairwise reducible by deterministic logspace Turing
  reductions in which every oracle query keeps the promise: reachability, path mass, parent in
  the hidden out-tree, ranking of walks, unranking of walks, and listing of the cone (Theorem
  6.2). Reachability reduces to path mass and to ranking with one query. (ii) The total
  language STCON_1 = {<G,s,t> : G mangrove, s reaches t} is in L if and only if promise mangrove
  reachability is in L. Likewise STCON_sf is in L if and only if promise strongly-few counting
  (equivalently path mass) is in FL (Corollary 7.4). (iii) For k-strongly unambiguous inputs,
  pair counting, path mass, one Gaussian-elimination fill coefficient (under the full
  strongly-few promise) and no-growth matrix powering are pairwise one-query equivalent
  (Corollary 4.4, Theorems 9.6, 10.8). (iv) Single-power totalization: for every input,
  including cyclic ones, <G,s,t,1^k> is in STCON_sf iff all entries of [[A,I],[0,I]]^(nk+1) are
  at most k and the (s,n+t) entry is positive (Theorem 10.3). (v) The unique-annotation verifier
  (Theorem 7.1). No new algorithm is claimed, and nothing here puts mangrove reachability in L.
- **New in this rewrite.** The promise-to-total transfers of Corollary 7.4. They follow from the
  verifier of A28.1 (any promise algorithm for mass generates the unique annotation, and the
  verifier rejects every annotation on invalid inputs), and from an interval lemma (Lemma 7.3)
  for the converse. Also new: the reduction from mass to unranking alone (sequential queries on a
  sentinel graph, never out of range); tightness of the exponent nk+1 (the directed n-cycle
  passes the test at exponent nk); Proposition 9.3 (bounded fills along every elimination order
  is equivalent to k-strong unambiguity); the observation that NGPower with K = 1 is one-query
  equivalent to mangrove reachability (Remark 10.9); Corollary 6.7 (logspace mangrove
  reachability would give StUL = L).
- **Imported.** Lange (STACS 1997): the language STCON_ru is ReachUL-complete, used only for
  Theorem 11.2. Standard closure of logspace oracle transducers in the Ladner-Lynch model (Lemma
  2.3). Background only, not used: Allender-Lange (1998), Allender (SIGACT News 2023),
  Kannan-Khanna-Roy (FSTTCS 2008), Apers-Edenhofer (CCC 2025), and the companion manuscript of
  this collection (STCON_sf in ReachUL and LOGDCFL).
- **Corrections and changes relative to the source.**
  - Theorem A27.3 of the source said only that six tasks are "mutually reducible in deterministic
    logspace". It listed "computing N_G(s,t)", which coincides with reachability on mangroves, and
    "ranking and unranking" as one task. It did not fix a reduction notion, and its "in
    particular Mangrove-Reach in L iff MASS in FL" left open whether the promise or the total
    version was meant. The theorem now uses a promise-respecting logspace Turing reduction
    (Definition 2.2), lists every reduction and checks its promise, treats ranking and unranking
    separately, and proves that the promise and total versions are equivalent (Corollary 7.4(b)).
  - Proposition A30.4 (diamond counterexample) had a vague proof. It is replaced by an exact
    statement: for every simple DAG and every topological or reverse topological order, all
    displayed fills equal the adjacency entries (Proposition 9.4). Theorem A30.5 is correct as
    stated, with the strongly-few promise on the whole graph (Definition 9.5). The unrestricted
    converse fails, exactly as Caution A30.6 says.
  - Theorem A25.1 assumed a positive integer solution. Any nonnegative real solution suffices,
    and nonnegativity is needed (two parallel self-loops give the solution -1). Proposition
    A25.3 was stated on DAGs only. It is now total: a nonnegative supersolution exists iff the
    graph is acyclic.
  - Theorem A27.1: the workspace O(log M_G(v) + log n) is logarithmic only on strongly-few
    inputs, where M_G(v) <= (n-1)k+1. On general DAGs M_G(v) can be exponential. This is now
    stated explicitly (Theorem 5.1(c), Remark).
  - Theorem A26.2: B > (n-1)k+1 suffices; the source used B = nk+1, which is still allowed.
    Theorems A31.4 and A31.5 hold for all powers r, not only r <= nk+1 and r <= n. Theorem A31.3
    was rechecked on cyclic inputs and is correct; the case k = 0 is now covered.
  - Theorem A32.2: the query bound O(1 + k log(|V_m|+1)) is made explicit as
    1 + 2k ceil(log2 |V_c|), with a stackless traversal in which each node is queried at most
    once.
  - Theorem A28.1: the range check is done by comparing numeral lengths first, so the verifier
    is logspace even when the supplied numerals are very long.
- **Left out.** Remark A23.2 rests on the robustification theorem A22.1, which belongs to another
  part of the source and is not proved here. Its wording "without changing the hidden cone
  trees" is also inaccurate: the shell adds exit leaves to every forward cone. Problem A23.3 is
  not a separate problem any more: by Theorem 6.2 it is equivalent to mangrove reachability.
  Problem A32.3 is merged into Problem 12.3, which for K = 1 is equivalent to Problem 12.1.
  Open Problems A35.4-A35.9 and A35.11 belong to other parts of the source.
- **Attribution.** Ranking and unranking by counting is the recursive method of
  Nijenhuis-Wilf. Gaussian elimination as a path algebra (Theorem 9.1(a,b)) goes back to
  Carre (1971) and Tarjan (1981). The stochastic similarity (Theorem 8.2) is a Doob h-transform.
  Theorem 11.2 is an immediate consequence of Lange's completeness theorem and is probably
  folklore, and so is Corollary 6.7. The stackless Euler tour is classical (Cook-McKenzie 1987).
- **Computer checks** are in [`verification/`](verification/README.md). Three standard-library
  Python scripts check exhaustively on all digraphs with at most 4 vertices, all DAGs and
  mangroves with at most 5 or 6 vertices, and random larger instances: the fixed point, the
  scalarizations, coding and unranking, the verifier (more than 4 million runs), every
  reduction of Theorem 6.2 against promise-checking oracles (about 2 million queries, no
  violation), the promise-to-total transfers with adversarial promise algorithms, the Schur
  complements for all elimination orders, the single-power totalization on all small inputs
  including cyclic ones and multigraphs, the tightness examples, NGPower, the midpoint census,
  and the rooted chain argument. All checks pass. The proofs do not depend on them.
- Not refereed.
