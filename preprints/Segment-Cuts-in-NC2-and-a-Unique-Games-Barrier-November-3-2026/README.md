# [Segment Cuts in NC² and a Unique Games Barrier](paper.pdf)

**Author:** Generated Computers

**Date:** November 3, 2026

## Citation

```bibtex
@misc{GC:Segment-Cuts-in-NC2-and-a-Unique-Games-Barrier-November-3-2026,
  author = {{Generated Computers}},
  title = {{Segment Cuts in $\mathrm{NC}^2$ and a Unique Games Barrier}},
  howpublished = {Generated Computers preprint, manuscript 007b},
  year = {2026}
}
```


## Lean

Part of this paper is formalized in Lean 4 with Mathlib, in the [Lean library](../../lean/README.md). The scope is described in [`lean/docs/007.md`](../../lean/docs/007.md), and the main statements are in the Comparator challenge [`SegmentCutsUGBarrier.lean`](../../lean/ComparatorChallenges/SegmentCutsUGBarrier.lean). Every listed theorem is proved without `sorry` and uses only the axioms `propext`, `Quot.sound` and `Classical.choice`. Complexity-theoretic conclusions (logspace, NC, P-completeness and the like) are not formalized.

*Segment cuts and the Unique-Games barrier (007b).* The formalization proves the maximal-packing bound of Theorem 6.4 in hypergraph form: the union of a maximal family of pairwise disjoint `(L+1)`-sets meets every member, and its size is at most `(L+1)` times the size of any hitting set. It defines the guard–router expansion `R_d(H)` of Definition 7.3 without the virtual sink, and proves Theorem 7.5 (with the path lifting and core counting of Lemma 7.4) in both directions: the cores of a feasible set of `H` for length `k` are feasible for `K = k(2d+1)`, and the owners of a feasible set of `R_d(H)` for length `K` are feasible for `k`. Hence `dvd_K(R_d(H)) = dvd_k(H)`. This holds for every digraph, every `d ≥ 1`, every assignment of length-`d` words to the arcs, and every `k`. On the family `𝒩_k` of Theorem 8.6 it proves `scut_1 = dvd_2 = k + 1`, and that every feasible union of the classes `A` and `B` has at least `2k + 1` vertices. The UGC-conditional barrier (Svensson's theorem, quoted as Theorem 7.2, and Corollaries 7.7 and 7.9), the skeleton realization lemma (Lemma 7.8), the canonical expansion, the compilers, the NC² path-packing algorithm, the rank schedules, and the computation of the rank tuples of `𝒩_k` are not formalized.

## Sources

Rewritten from the following internal notes (document numbers of the 27 October 2026 corpus review):
- #17, Sequential NOR Structural Parallelization Compendium, Segment-Cut Hardness Barrier (`Sequential_NOR_Structural_Parallelization_Compendium_Segment_Cut_Hardness_Barrier_2026-09-01.pdf`): Part VII, Sections 32-36 and 44 (pp. 38-52, 75-76): Definitions 32.1-35.14, Theorems 32.2, 32.4, 33.2, 34.4, 34.5, 35.3, 35.5, 35.10, 35.13, 35.16, 36.3, 36.5, 44.2, Lemmas 33.3, 33.6, 33.10, 34.1, 34.2, 35.8, 35.15, 36.1, 44.1, Corollaries 32.6, 34.3, 35.11, 35.17, 35.18; Theorem 17.4 (block recovery, p. 24). Pages 1-37 repeat #18 and were used only for the definitions of Sequential NOR and the binary core.
- #07 (`Sequential_NOR_Structural_Parallelization_Compendium_Factorized_Regional_Relations_2026-09-02.tex`), Sections 32-36, which repeat the same material, used to check formulas.
- Svensson, Theory of Computing 9 (2013), Theorem 1.1, checked against the published paper.

## Status

Proved in full: the split-merge normal form (known P-complete, Greenlaw-Hoover-Ruzzo, included as a convenience), the branching-depth compiler for branching depth O(log n), the modulator compiler, the (L+1)-approximation of the segment-cut number in deterministic NC^2 by maximal path packing and Luby's algorithm, the guard-router reduction, the conditional barrier (assuming the UGC through Svensson's Theorem 1.1, whose completeness/soundness form and vertex-count convention were checked in the paper), its transfer to Sequential-NOR skeletons via the skeleton-realization lemma, the safety and exact NC^2 optimization of one-sided rank schedules, and the rank-anonymity family.

Changes relative to the source: the constructions are stated for an arbitrary normalized record system and specialized to Sequential NOR through the binary core (cited to manuscript 006f); the branching-depth compiler is proved only for b = O(log n), and the source's general bound (depth O(log^2 n + b)) is quoted without proof (Remark 5.4) because writing down a superpolynomial unfolding within that depth was not verified; the scope of the barrier is stated explicitly (hard instances have linear optimum, so the barrier does not reach the polylogarithmic regime in which the compilers are useful, and at most one logarithmic depth factor is at stake). A remark records that the guards are unnecessary (K = k(d+1) also works), as found in the review.

Left out: the two-sided, band, grid, guillotine, turn, oblique and piecewise-affine rank-schedule hierarchies of Sections 37-43 and the strictness families of Section 44 (except Theorem 44.2), including the budget-turn saturation identity. They are only summarized in Remark 8.5; every such schedule is a feasible segment cut, so path packing dominates them up to the factor L+1. The guard-router reduction was checked by brute force in the review (random DAGs with at most five vertices, k in {2,3}). Not refereed.
