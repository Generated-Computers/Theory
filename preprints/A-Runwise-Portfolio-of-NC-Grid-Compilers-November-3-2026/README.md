# [A Runwise Portfolio of NC Grid Compilers](paper.pdf)

**Author:** Generated Computers

**Date:** November 3, 2026

## Citation

```bibtex
@misc{GC:A-Runwise-Portfolio-of-NC-Grid-Compilers-November-3-2026,
  author = {{Generated Computers}},
  title = {{A Runwise Portfolio of NC Grid Compilers}},
  howpublished = {Generated Computers preprint, manuscript 009c},
  year = {2026}
}
```


## Lean

Part of this paper is formalized in Lean 4 with Mathlib, in the [Lean library](../../lean/README.md). The scope is described in [`lean/docs/009.md`](../../lean/docs/009.md), and the main statements are in the Comparator challenge [`RunwiseGridPortfolio.lean`](../../lean/ComparatorChallenges/RunwiseGridPortfolio.lean). Every listed theorem is proved without `sorry` and uses only the axioms `propext`, `Quot.sound` and `Classical.choice`. Complexity-theoretic conclusions (logspace, NC, P-completeness and the like) are not formalized.

**A runwise portfolio of NC grid compilers (009c).** The portfolio theorem (Theorem 3.2, an
`FNC^k` statement) is not formalized. Formalized are: the finite-portfolio lemma (Lemma 3.1) in
abstract form (compilers are maps from blocks to an optional trace function; the first-passing
portfolio passes iff some compiler passes and is sound if all are); the lower bound
`Γ ≥ min(g, d + 1)` (Lemma 4.1); `Γ ≤ 2` for the second run of Proposition 4.2 (`L` rows `I`
then `L` rows `Q`); and `Γ ≤ min(H, 1 + s)` for common cores (Proposition 5.1). The row facts of
Proposition 2.4 are the 009b theorems above. The full strictness statement (Proposition 4.2), in
particular membership in the collar class and the large-`M` parameter estimates, is not
formalized.

## Sources

Rewritten from the following internal notes (document numbers of the 27 October 2026 corpus review):
- #06 Flagship Finished Theorems (`SEQNOR_FLAGSHIP_FINISHED_THEOREMS_2026_09_07.pdf`), Sections 5–7:
  Lemma 6.1, Theorem 7.1 ("ACP-k"), Propositions 7.2–7.3; pp. 5–7. Its Theorem 3.1 (binary-core
  retraction) is the subject of manuscript 006f and is only cited here.

## Status

- Proved in full, relying on manuscripts 009a (threshold-reset composition) and 009b (the collar
  and Γ compilers): the finite-portfolio lemma, the runwise portfolio theorem (FNC^k for fixed
  k ≥ 2), the strictness of the runwise union over both global promises, and the containment of the
  common-core class in the Γ class.
- Main caveat: the grid normal form is not known to be P-hard, so the theorem is not known to cover
  hard instances.
- Changes relative to the source: the collar class is the one of 009b (greedy anchors, short gaps
  only), so the first run of the strictness example is rebuilt: the source used a long run of
  period-two rows accepted by the dropped long-gap clause; here it is a run of planted constant-image
  two-row anchors with three distinct cell words, whose Γ is bounded below by a segment count. The
  source's all-source validation of imported compilers is not needed because both arms are exact
  on their promises. Self-labels ("flagship", "strongest") are dropped.

Not refereed. No human referee has checked it yet; the proofs were developed with the assistance
of an AI system.
