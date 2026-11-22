# [Stable Semisort Is Exactly as Hard as Padded Sorting](paper.pdf)

**Author:** Generated Computers

**Date:** November 3, 2026

## Citation

```bibtex
@misc{GC:Stable-Semisort-Is-Exactly-as-Hard-as-Padded-Sorting-November-3-2026,
  author = {{Generated Computers}},
  title = {{Stable Semisort Is Exactly as Hard as Padded Sorting}},
  howpublished = {Generated Computers preprint, manuscript 011a},
  year = {2026}
}
```

## Lean

Part of this paper is formalized in Lean 4 with Mathlib, in the [Lean library](../../lean/README.md). The scope is described in [`lean/docs/011.md`](../../lean/docs/011.md), and the main statements are in the Comparator challenge [`StableSemisortPaddedSorting.lean`](../../lean/ComparatorChallenges/StableSemisortPaddedSorting.lean). Every listed theorem is proved without `sorry` and uses only the axioms `propext`, `Quot.sound` and `Classical.choice`. Complexity-theoretic conclusions (logspace, NC, P-completeness and the like) are not formalized.

**Stable semisort and padded sorting (011a).** Inputs are `n` records identified by their positions, outputs are lists of original indices, and the problems of Definitions 2.1–2.2 (unstable semisort, stable semisort, stable integer sort, sorting distinct keys, padded sorting) are stated as output specifications. The black boxes are modeled as arbitrary valid outputs, or as oracles that solve every valid instance; nothing is assumed about how they work. Both directions of the equivalence are formalized as explicit transformations with correctness proofs. (1) Theorem 3.1: from any valid unstable-semisort output, the run marks, run numbers, group identifiers and composite keys `(n+1) gid[i] + i` of stages S1–S4 form a valid `PaddedSort(n,(n+1)^2)` instance, and the compaction of any valid padded output is a stable semisort. This includes Lemmas 3.2–3.5, Lemma 2.4 and the reductions `IS ⪯ DS` and `SS ⪯ IS + USemi` of Theorem 4.1. (2) The converse, `PaddedSort(n,(n+1)^2) ⪯ SS`, makes no call to an unstable semisort. It composes `DS ⪯ IS` (a two-pass radix sort; the second pass sorts the records in the order of the first) with `IS ⪯ SS` (segmented-scan offsets, group lengths, their prefix sums and one exclusive scatter) and Lemma 2.4. The collision-energy identity (Lemma 6.2) and the density barrier (Theorem 7.3) are also formalized. Not formalized: all costs (work, depth, space, CREW exclusivity of writes, failure probabilities), so Corollaries 3.7 and 4.3, which are statements about costs, are not formalized either. In `IS ⪯ SS` the group lengths are defined as counts over the semisorted list, not computed by a scan. Also not formalized: the colored-prefix-rank reductions of Theorem 4.1(d), the counting-pass and radix-restoration bounds of Section 5, and the random-anchor bounds of Section 7 (Proposition 7.1, Theorem 7.2).

## Sources

Rewritten from the following internal notes (document numbers of the 27 October 2026 corpus review):
- #02, Stable Semisort Final Closure Note (`Semisort/Stable_Semisort_Final_Closure_Note.pdf`;
  internal title "Stable Work-Efficient Parallel Semisort: A Closure via Padded Integer Sorting"). Used: Sections 1–6 (Definitions 3.1–3.2,
  Theorem 3.3, Algorithm 1, Lemmas 5.1–5.5, Corollaries 6.1–6.2); Appendix B (Theorem B.1);
  Appendix C (model and key-universe audit); Appendix K (Theorem K.1, Lemmas K.2–K.7);
  Appendix L (Theorem L.1, Corollary L.2, Section L.2); Appendix M.1 (Lemma M.1); Appendix N
  (Theorems N.1 and N.2); Appendix O.4 and Section 8 for the remarks on circularity. PDF pages
  1–13 and 23–31.

## Status

- Proved in full: the reduction (Theorem 3.1, source Theorem 3.3/B.1), the equivalence of stable
  semisort, stable integer sorting on [0,n], sorting distinct keys below (n+1)^2 and colored
  prefix ranks (Theorem 4.1, source K.1), the radix-restoration bound (Proposition 5.2, source
  L.1), the identity between prediction-alignment error and collision energy (Lemma 6.2, source
  M.1), the random-anchor bound (Proposition 7.1 and Theorem 7.2, source N.1) and the
  density barrier (Theorem 7.3, source N.2).
- Framing corrected. The source presented Theorem 3.3 as a "closure" that "settles" the
  work–depth question and as a "precise EP result". By the source's own Theorem K.1, the padded
  sort it needs is equivalent to stable semisort itself (given unstable semisort). The paper says
  exactly this (Corollary 4.3) and does not present the reduction as closing anything.
- Small corrections. The source's second black box in K.1 (an unstable sorter for distinct keys
  in [0,n]) is unnecessary; direct addressing does the job (Remark 4.2). The glue code needs
  concurrent reads, so the model is stated as CREW, not EREW. The work bound of L.1 is stated with
  the 2^d term. The constants in the proof of N.1 were re-chosen; the statement is unchanged.
- Left out: the CRCW corollary of the source (it rests on an unverified key-universe assumption
  about the Goodrich–Matias–Vishkin padded sorter, and by Corollary 4.3 its premise is as strong as
  its conclusion); the black boxes of two 2026 works (Hutton–Melrod; Goodrich–Gu) that we could not
  check — unstable semisort appears only as a hypothesis, and of the predictive sorter only the
  definition of its error measure is used; the low-burst and burst-adaptive theorems M.2–M.4, the
  colored-predecessor equivalence O.3–O.4 and the "open frontier" (they depend on the unverified
  sorter); owner restoration J.3 (dominated by Proposition 5.2 with digits of ε log n bits); the
  I/O lower bound I.1, the local-heavy and coarsened-clock sketches D.3–D.4, and the
  positional-cell and cache-line results (not part of this manuscript).
- Fixed-width claims: the source's "O(n) work with 16 passes for 64-bit keys" is a constant only
  because n ≤ 2^64; the paper states the honest Θ(n log n / d) bound and the O(n/ε)-work,
  O(n^ε)-depth trade-off.
- Checks: `verification/check_semisort.py` (run with `python3 verification/check_semisort.py`) verifies the
  reduction against an adversarial unstable semisort, every reduction of Theorem 4.1, the
  collision-energy identity, the expected-energy formula exactly for groups of size ≤ 11, and the
  density bound exhaustively for f ≤ 12, k ≤ 5.
- Not refereed.
