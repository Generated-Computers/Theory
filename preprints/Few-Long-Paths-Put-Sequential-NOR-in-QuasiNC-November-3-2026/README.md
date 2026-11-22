# [Few Long Paths Put Sequential NOR in QuasiNC](paper.pdf)

**Author:** Generated Computers

**Date:** November 3, 2026

## Citation

```bibtex
@misc{GC:Few-Long-Paths-Put-Sequential-NOR-in-QuasiNC-November-3-2026,
  author = {{Generated Computers}},
  title = {{Few Long Paths Put Sequential NOR in QuasiNC}},
  howpublished = {Generated Computers preprint, manuscript 006g},
  year = {2026}
}
```



## Lean

Part of this paper is formalized in Lean 4 with Mathlib, in the [Lean library](../../lean/README.md). The scope is described in [`lean/docs/006.md`](../../lean/docs/006.md), and the main statements are in the Comparator challenge [`FewLongPaths.lean`](../../lean/ComparatorChallenges/FewLongPaths.lean). Every listed theorem is proved without `sorry` and uses only the axioms `propext`, `Quot.sound` and `Classical.choice`. Complexity-theoretic conclusions (logspace, NC, P-completeness and the like) are not formalized.

**006g (Few long paths).** For a finite digraph given by an adjacency relation, directed paths are chains of vertices. Formalized: the path-hitting identity (Theorem 4.1) and the packing sandwich $q\le\delta_M\le(M+1)q$ (Theorem 4.3). Also formalized: the path formula $\delta_M(C_L)=\lfloor L/(M+1)\rfloor$ (Theorem 5.2). Not formalized: the bounded search tree algorithm and its running time (Theorem 4.2), the circuit compilers (Theorems 3.1, 6.2, 7.1, Corollary 4.4), Lemma 5.1 and Proposition 5.4 (the contracted DAG of the path family and of the triangle example), and the separator results.

## Sources

Rewritten from the following internal notes (document numbers of the 27 October 2026 corpus review):
- #22 Guarded-Contraction Portfolios for Sequential NOR (`seqnor_generation13_structural_portfolio.pdf`): §2 (motivation), §3 (signed-root normalization, Theorem 3.1), §4 (Theorems 4.1–4.2, Remark 4.3), §5 (Theorem 5.1, Corollary 5.2), §6 (Lemma 6.1, Theorem 6.2), §7 (Definition 7.1, Theorem 7.2), §8 (Theorem 8.1), §11 (stated as an open problem), Appendix A (checks). §9 (relation to the three-round mask theorem and the phase-switch lemma) is omitted; phase repair is in manuscript 007a. §10 (the search engine) is omitted.

## Status

All results are proved in full. They are promise-class (parameterized) upper bounds and exact combinatorial identities, not unconditional results: quasipolynomial-size, polylogarithmic-depth circuits when the contracted anchor DAG has a small deletion set to small depth, a small long-path packing number, or small recursive separator width. The techniques are textbook (bounded search trees for uniform hitting sets, the factor M+1 from a maximal packing, divide and conquer on balanced separators) and are attributed; Svensson's UGC-hardness for DAG vertex deletion is cited for context. The source's path family, which separates the deletion parameter from the separator parameter, is semantically degenerate (every anchor after the first computes NOR(¬z, z) = 0), so the separation holds only for the syntactic parameters; this is stated, and a non-degenerate example (an embedded NOR circuit whose contracted primal graph is the square of a path) is added with proof. The separator proof was rewritten with an explicit invariant for which constraints are checked at which call. The guarded contraction step is the binary-core compression of manuscript 006f and is cited from there. The contraction was rechecked exhaustively for n ≤ 8, and the path family and the added example by brute force for small sizes; these are regression checks only. Not refereed.

## Code

Checking scripts used for this manuscript are in [`verification/`](verification/): `check_006g.py`. They are plain Python 3 with no dependencies outside the standard library unless the script says otherwise.
