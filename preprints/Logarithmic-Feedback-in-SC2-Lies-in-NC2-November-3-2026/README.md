# [Logarithmic Feedback in SC² Lies in NC²](paper.pdf)

**Author:** Generated Computers

**Date:** November 3, 2026

## Citation

```bibtex
@misc{GC:Logarithmic-Feedback-in-SC2-Lies-in-NC2-November-3-2026,
  author = {{Generated Computers}},
  title = {{Logarithmic Feedback in $\mathrm{SC}^2$ Lies in $\mathrm{NC}^2$}},
  howpublished = {Generated Computers preprint, manuscript 008d},
  year = {2026}
}
```



## Lean

Part of this paper is formalized in Lean 4 with Mathlib, in the [Lean library](../../lean/README.md). The scope is described in [`lean/docs/008.md`](../../lean/docs/008.md), and the main statements are in the Comparator challenge [`LogFeedbackBlock.lean`](../../lean/ComparatorChallenges/LogFeedbackBlock.lean). Every listed theorem is proved without `sorry` and uses only the axioms `propext`, `Quot.sound` and `Classical.choice`. Complexity-theoretic conclusions (logspace, NC, P-completeness and the like) are not formalized.

**008d (Logarithmic feedback in SC² lies in NC²).** Formalized: the unique-transcript lemma (Lemma `lem:unique`): for every entering state and data vector exactly one transcript has a successful forced run whose affine guard holds, and for it the block ends at `(q_{u,τ}, M_{u,τ}x + c_{u,τ})`; successful transcripts have one bit per feedback-sensitive stage and guards with one row per such stage, so there are at most `2^h` of them; and the transcript leaves form an exact affine decision summary. The forced run is defined stage by stage, which is equivalent to the segment recursion of the paper. Not formalized: Theorem `thm:block` and Corollary `cor:sparse` (NC² circuits, uniformity), Proposition `prop:mass` beyond the `2^h` count, and the examples.

## Sources

Rewritten from the following internal notes (document numbers of the 27 October 2026 corpus review):
- SC^2 Sparse-Feedback Block Compression (`SC2_Sparse_Feedback_Block_Compression_Draft.pdf`, document #13, 7 pp., with its LaTeX source): Lemma 3.1, Proposition 3.2, Theorem 4.1, Corollary 4.2, Sections 5–6. The same text is Component 11 (PDF pp. 277–284) of document #03.

## Status

- Proved in full: unique-transcript lemma, polynomial mass, the block theorem (uniform NC^2, final state and full trajectory), the corollary for feedback-sparse SPAI_2, and the examples.
- Corrected: the source gave Theorem 4.1 only as a "proof sketch with resource ledger" (reviewers' point); the proof is now complete, including uniformity and the trajectory step. The source imported "SPAI_2 is SC^2-complete" without proof (reviewers' point); it is now cited from the companion 008a, where it is proved, and the block theorem does not depend on it.
- Attributed: the construction is the standard enumeration of answer sequences of a bounded number of adaptive queries (cf. Beigel 1991); no new technique is claimed. The composition remark is stated as the difficulty of the general problem, not as a result.
- Not refereed.
