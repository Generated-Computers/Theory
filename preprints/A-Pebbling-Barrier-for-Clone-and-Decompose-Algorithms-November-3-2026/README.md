# [A Pebbling Barrier for Clone-and-Decompose Algorithms](paper.pdf)

**Author:** Generated Computers

**Date:** November 3, 2026

## Citation

```bibtex
@misc{GC:A-Pebbling-Barrier-for-Clone-and-Decompose-Algorithms-November-3-2026,
  author = {{Generated Computers}},
  title = {{A Pebbling Barrier for Clone-and-Decompose Algorithms}},
  howpublished = {Generated Computers preprint, manuscript 007c},
  year = {2026}
}
```


## Lean

Part of this paper is formalized in Lean 4 with Mathlib, in the [Lean library](../../lean/README.md). The scope is described in [`lean/docs/007.md`](../../lean/docs/007.md), and the main statements are in the Comparator challenge [`CloneAndDecomposePebbling.lean`](../../lean/ComparatorChallenges/CloneAndDecomposePebbling.lean). Every listed theorem is proved without `sorry` and uses only the axioms `propext`, `Quot.sound` and `Classical.choice`. Complexity-theoretic conclusions (logspace, NC, P-completeness and the like) are not formalized.

*Pebbling barrier (007c).* The formalization defines black pebblings (a step places a pebble on a vertex whose predecessors are pebbled, removes a pebble, or repeats the configuration) and predecessor-preserving partial unfoldings of gate DAGs. It proves the pebbling projection lemma (Lemma 4.4: every pebbling of an unfolding projects to a pebbling of the circuit of no larger cost) and that every vertex of an unfolding computes the value of its label. It also proves the grid pebbling price `Peb(Q_g) = g + 1` for `g ≥ 2` (Lemma 4.8), with the lower bound by the pyramid blocking argument and the upper bound by the explicit row-by-row strategy. As a consequence, every pebbling of every predecessor-preserving partial unfolding of `C_g` costs at least `g + 1`. The tree-depth pebbling bound (Lemma 4.5), the treewidth/tree-depth inequality (Lemma 4.6), and therefore the treewidth form of Theorem 4.7 and Corollaries 4.9–4.10 are not formalized. Neither are the four-coordinate embedding, the tail-factorized system of Section 3, and the compilers.

## Sources

Rewritten from the following internal notes (document numbers of the 27 October 2026 corpus review):
- #07, Structural Parallelization Compendium, Factorized Regional Relations (`Sequential_NOR_Structural_Parallelization_Compendium_Factorized_Regional_Relations_2026-09-02.tex`): Section 36.10 (Definition of the tail-factorized portal system, Lemma 36.28, Theorems 36.29-36.30, Corollary 36.31; pp. 66-68 of the PDF), with the supporting Definition of closed portal-region decompositions (Section 36.5), the balanced-interface evaluator (Section 18) and the imported treewidth module (Section 19).
- #15, Compendium NCk Semantic Pivot Draft (`Sequential_NOR_Compendium_NCk_Semantic_Pivot_Draft.pdf`): Section 36.13 (partial-unfolding compiler, Proposition 36.38, p. 72) and Section 36.15 (Lemmas 36.41-36.43, Theorem 36.44, Lemma 36.45, Corollaries 36.46-36.47; pp. 75-77).
- #03, Sequential NOR to SC full compendium (`Sequential_NOR_to_SC_Full_Research_Compendium_Draft.pdf`), pp. 87-89, which repeat #15 pp. 75-77.

## Status

Proved in full: exactness and size of the tail-factorized system, the compiler with a supplied decomposition, the automatic fixed-treewidth compiler (bounded-treewidth recognition and balancing imported from Bodlaender, Bodlaender-Hagerup and Elberfeld-Jakoby-Tantau), the partial-unfolding compiler, the pebbling projection, the tree-depth pebbling bound, the treewidth/tree-depth inequality, the barrier theorem, and the grid pebbling price g+1 (the lower bound is proved here directly, by the classical blocking argument on the pyramid inside the grid, instead of by citation).

Changes relative to the source: the factorized compilers are stated for local depth b = O(log n), where the system has polynomial size; both balanced interface decompositions and binary tree decompositions are allowed as certificates; regional queries and exactness are proved directly rather than through the monolithic regional relations. Added, as the review requested: Remark 4.11 derives the stronger width bound Omega(N/log^2 N) from the graphs of Paul, Tarjan and Celoni (Math. Systems Theory 10, 1977).

Left out: the "semantic pivot" of #15 (Definition 36.48, Theorems 36.49-36.52), which the review found vacuous (Sequential NOR has no free inputs, so the zero-rank certificate is the trace itself and the target restates the open problem); the stretched-grid static-width obstruction (Theorem 36.36), the laced-funnel separation (Theorem 36.40) and the bridge-bundle compilers, which were not assigned. The grid pebbling price was checked by exhaustive search for g = 2, 3, 4 in the review. Not refereed.
