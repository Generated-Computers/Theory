# [Few Nonlinear Gates per Path Put Circuits in NC](paper.pdf)

**Author:** Generated Computers

**Date:** November 3, 2026

## Citation

```bibtex
@misc{GC:Few-Nonlinear-Gates-per-Path-Put-Circuits-in-NC-November-3-2026,
  author = {{Generated Computers}},
  title = {{Few Nonlinear Gates per Path Put Circuits in NC}},
  howpublished = {Generated Computers preprint, manuscript 008e},
  year = {2026}
}
```



## Lean

Part of this paper is formalized in Lean 4 with Mathlib, in the [Lean library](../../lean/README.md). The scope is described in [`lean/docs/008.md`](../../lean/docs/008.md), and the main statements are in the Comparator challenge [`FewNonlinearGates.lean`](../../lean/ComparatorChallenges/FewNonlinearGates.lean). Every listed theorem is proved without `sorry` and uses only the axioms `propext`, `Quot.sound` and `Classical.choice`. Complexity-theoretic conclusions (logspace, NC, P-completeness and the like) are not formalized.

**008e (Few nonlinear gates per path put circuits in NC).** Formalized: the triangular product identity (Lemma `lem:product`): for strictly lower triangular `M` and `2^s ≥ n`, `∏_{k<s}(I + M^{2^k})` is the two-sided inverse of `I + M`; the algebraic core of Theorem `thm:regions` (the local equations `x = Mx + Nz + c` of a region hold if and only if `x = (SN)z + Sc`); and Lemma `lem:boundary` for the non-affine depth (monotone along references, strictly increasing at barriers). Not formalized: Theorems `thm:extract` and `thm:ladder`, Corollary `cor:ladder` (depth bounds, FNC classes, uniformity), the macro grammar, the algebraic-normal-form test, the region graph, and the register example.

## Sources

Rewritten from the following internal notes (document numbers of the 27 October 2026 corpus review):
- Sequential NOR: Automatic Affine-Phase Extraction (`Sequential_NOR_Automatic_Affine_Phase_Extraction_Draft.pdf`, document #14, 7 pp.; candidates UFR-46 to UFR-50): Theorem 2.1, Lemma 3.1, Theorem 3.2, Theorem 4.1, Corollary 4.2, Sections 5.1 and 6. The same text is Component 9 (PDF pp. 261–268) of document #03.

## Status

- Proved in full: syntactic extraction of labels, non-affine depth, regions and boundaries in NC^2; the triangular product identity and the region matrices; the phase ladder depth O(log^2 L + (H_aff+1) log L) and the NC^{max(2,c+1)} corollary; the prefix-parity register example.
- Made precise: the tagged-circuit model and the NOR macro grammar (validity of tags, internal-use condition) are defined; the depth computation uses unary max-plus squaring; the region matrices are computed by one global triangular inversion. The theorem is stated for a supplied bound H, with rejection when H_aff > H.
- Attributed: GF(2) linear algebra (⊕L ⊆ NC^2) plus the number of nonlinear gates on a path (multiplicative depth); known, as the reviewers note; no novelty claimed for the method.
- Left out: the dyadic bank-cascade family (Section 5.2 of the source), which depends on bank interfaces defined in other notes. It is stated explicitly that untagged Sequential NOR has H_aff = n.
- Not refereed.
