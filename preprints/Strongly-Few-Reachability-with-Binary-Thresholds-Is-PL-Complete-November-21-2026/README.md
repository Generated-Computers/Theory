# [Strongly-Few Reachability with Binary Thresholds Is PL-Complete](paper.pdf)

**Author:** Generated Computers

**Date:** November 21, 2026

## Citation

```bibtex
@misc{GC:Strongly-Few-Reachability-with-Binary-Thresholds-Is-PL-Complete-November-21-2026,
  author = {{Generated Computers}},
  title = {{Strongly-Few Reachability with Binary Thresholds Is PL-Complete}},
  howpublished = {Generated Computers preprint, manuscript 012b},
  year = {2026}
}
```

## Lean

This manuscript is not formalized yet.

## Sources

Rewritten from the following internal note:
- "Total Strongly-Few Directed Reachability: Unambiguity, Auxiliary Pushdowns, Exact Counting,
  and the StrongFewL Boundary" (`STCONsf_Class_Containments_Revised.pdf`, 9 September 2026).
  Used: Section 5.4 (Theorem 5.8), Section 5.5 (rooted recognition, Theorem 5.9), Section 6
  (Theorems 6.1, 6.2, Corollary 6.3), Section 7.2 (Theorem 7.2) and Problem 7.3; Appendix A1
  (Theorem A1.1, Theorem A1.2, Corollary A1.3, Corollary A1.4), Appendix A2 (Theorem A2.1,
  Remark A2.2, Theorem A2.3 and the classification table), Appendix A34 (Theorem A34.1,
  Corollary A34.2, Remark A34.3), Appendix A35 (Problems A35.4, A35.5, A35.9, A35.11).
- Apers and Edenhofer, CCC 2025: Theorems 1.2 and 1.4, Corollary 1.3, footnote 3 and the
  open questions of their conclusion, for the BQL corollary.

## Status

- **Proved in full:** BIN-STCON_sf (binary threshold) is PL-complete under logspace many-one
  reductions, with hardness on acyclic instances where s reaches t (Theorem 5.1). The one-pair
  cap is NL-complete for a fixed cap and PL-complete for a binary cap (Theorem 5.4).
  RootFew_k is ReachUL-complete for every fixed k >= 1, also on DAGs (Theorem 3.2). Rooted
  recognition is ReachUL-complete (Lemma 3.3). FBFew_{k,1}, TwoCone_{k,l} and the unary
  TwoCone are ReachUL-complete (Theorem 3.5). STCON_sf is StrongFewL-hard (Theorem 4.1). Each
  of STCON_sf, PairBudget and RootBudget has a single GapL zero test (Propositions 6.1–6.3).
  The collision-averaged decoding gives min{N^{<=B}(r,v), K+1} = min{ceil(D_v/q0), K+1}
  (Theorem 7.1), and capped counts are computable in FL^NL (Theorem 7.3, Corollary 7.4), also
  for arbitrary #L functions (Theorem 7.5, Corollary 7.6).
- **New in this rewrite:** Corollary 3.6. If the two-cone recognition problem (fixed or
  unary thresholds), i.e. recognizing the promise of Apers–Edenhofer's Theorem 1.2, is in
  BQL, then ReachUL ⊆ BQL. ReachUL ⊆ BQL is not known to us: Apers and Edenhofer prove only
  StrongFewL ⊆ BQL and ask whether BQL can handle reach-few graphs. Also new: Problem 8.3. Since
  STCON_sf ∈ BQL, ReachUL-hardness of STCON_sf would imply ReachUL ⊆ BQL. Further additions are
  the direct many-one reduction of Lemma 3.3, part (c) of Theorem 7.1 (maximum instead of
  average), and the padding observation in Remark 5.3.
- **Imported (stated as facts, not reproved):** memberships of RootBudget, PairBudget and
  STCON_sf in ReachUL (companion manuscript 012a); STCON_ru is ReachUL-complete (Lange 1997);
  ReachUL is closed under complement (Buntrock–Jenner–Lange–Rossmanith 1991) and L^ReachUL =
  ReachUL (Garvin–Stolee–Tewari–Vinodchandran 2014, Lemma 4); NL = coNL
  (Immerman, Szelepcsényi); GapL closure, the GapL characterizations of PL and C=L, and closure
  of PL under logspace conjunctive truth-table reductions (Allender–Ogihara 1996, using
  Beigel–Reingold–Spielman 1995); STCON_sf ∈ BQL and StrongFewL ⊆ BQL (Apers–Edenhofer 2025);
  polynomially bounded #L functions are in FL^NL (Allender–Reinhardt–Zhou 1999). The
  budget-mass truncation lemma is reproved (Lemma 2.8).
- **Correction (Theorem 5.9 of the source).** The source took the ReachUL-hardness of rooted
  recognition from Dinesh–Sasidharan (MFCS 2026). Their Proposition 2 is a reach-unambiguous
  oracle machine that solves reachability with one query to recognition. A ReachUL machine can
  solve STCON_ru without an oracle, so this does not give a logspace many-one reduction. Lemma 3.3
  now gives a direct many-one reduction. It reduces the complement and adds a second path r→y→z
  next to the accepting configurations, and it uses only closure of ReachUL under complement.
- **Correction (Theorem A2.1 of the source), membership.** The source cited Beigel–Fu and
  Hoang–Thierauf for closure of PL under complement, union, intersection and NC¹ reductions.
  The closure actually used, a polynomial conjunction, is closure under logspace conjunctive
  truth-table reductions, proved by Allender–Ogihara (1996). Beigel–Fu (NC¹ closure) and Ogihara
  (1998, PL hierarchy collapse) are stronger and are mentioned but not needed. Hoang–Thierauf
  concerns GapL and is no longer cited. Acyclicity is now one GapL positivity condition
  (no walk of length n).
- **Correction (Theorem A2.1), hardness.** The source asserted that every pair inside "the binary
  computation graph" has at most 2^p walks. That holds only after normalization, because
  configurations unreachable from the start are also in the graph. Lemma 5.2 now gives the
  normal form: a clock, a fair coin at every step, and the coin recorded in the configuration,
  so every vertex has exactly two distinct successors. The source reduced the complement (accepting
  sink, K = C + 2^{p−1}) and then used closure under complement; that is correct. It is replaced
  by a direct reduction with a rejecting sink and K = 2^{T+1} + 2^{T−1} − 1.
- **Other changes.** Theorem 5.8's DAG reduction uses layers 0..n and the truncation lemma; the
  source's 0..2n−1 argument is also correct, and both were checked. Theorem 7.2 no longer needs
  a clock: strong fewness forces acyclicity. The collector bound Z(n)p(n) and the midpoint
  counts are made explicit. The one-pair cap is stated on arbitrary digraphs, with the length
  bound (k+2)n. Theorem A1.1 and A34.1 decode with a ceiling. The ceiling is confirmed, and a
  floor is wrong whenever collisions occur (computer control). Problem A35.9 listed thresholds
  2^{n^ε} as open; padding shows that case is PL-complete (Remark 5.3), and only the
  quasi-polynomial regime stays open (Problem 8.4).
- **Known containments presented as certificates.** The C=L placements (source Section 6) follow
  from ReachUL ⊆ UL ⊆ NL ⊆ C=L, and the NL placements (A1.2, A1.3) from ReachUL ⊆ NL. Both are
  presented as explicit certificates, a single sum-of-squares zero test and FL^NL capped counts,
  not as new containments.
- **Novelty.** For polynomially bounded #L functions the exact value is in FL^NL by
  Allender–Reinhardt–Zhou (1999), and the source did not cite this. Theorem 7.5 is new only in
  its capped form for arbitrary #L functions, with Corollary 7.6 (PolyThreshold-#L = NL). We
  have not found it stated in the literature, but it may be folklore. The hashing idea is close
  to Pavan–Tewari–Vinodchandran (2012).
- **Left out:** nothing from the assigned sections. Remark A34.3 is merged into Remark 5.3.
  Problem A35.11 is restated with a note that the single-pair total problem is already
  NL-complete. The companion reference GC012a carries a placeholder title until the 012a title
  is fixed.
- Computer checks are in [`verification/`](verification/README.md). All digraphs with at most 4
  vertices are covered for the truncation lemma, the layering, the prefix and the two-cone
  reductions, toy PL machines for the A2.1 gadget (every R in [0, 2^T] for T <= 5), real
  primes for the fingerprint decoding, and the zero tests and the StrongFewL construction.
  Every check reports 0 failures. The proofs do not depend on them.
- Not refereed.
