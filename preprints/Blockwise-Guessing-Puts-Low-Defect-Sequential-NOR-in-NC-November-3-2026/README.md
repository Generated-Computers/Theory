# [Blockwise Guessing Puts Low-Defect Sequential NOR in NC](paper.pdf)

**Author:** Generated Computers

**Date:** November 3, 2026

## Citation

```bibtex
@misc{GC:Blockwise-Guessing-Puts-Low-Defect-Sequential-NOR-in-NC-November-3-2026,
  author = {{Generated Computers}},
  title = {{Blockwise Guessing Puts Low-Defect Sequential NOR in NC}},
  howpublished = {Generated Computers preprint, manuscript 006e},
  year = {2026}
}
```



## Lean

Part of this paper is formalized in Lean 4 with Mathlib, in the [Lean library](../../lean/README.md). The scope is described in [`lean/docs/006.md`](../../lean/docs/006.md), and the main statements are in the Comparator challenge [`BlockwiseGuessing.lean`](../../lean/ComparatorChallenges/BlockwiseGuessing.lean). Every listed theorem is proved without `sorry` and uses only the axioms `propext`, `Quot.sound` and `Classical.choice`. Complexity-theoretic conclusions (logspace, NC, P-completeness and the like) are not formalized.

**006e (Blockwise guessing).** Formalized: bad shields and ranks (Definition 2.1), the candidate $Y(\gamma)$, prefix locality (Lemma 4.1) and true-prefix recovery (Corollary 4.2). The stage of Section 5 is defined explicitly, with branches, padding and validity bits, and the selection $\beta_{a+t}=\bigvee_\alpha(V_\alpha\wedge\alpha_t)$. We prove the unique-valid-branch lemma (Lemma 5.1). We also prove correctness of the schedule (Theorem 5.2, correctness part): on the promise $|H(j)|\le r$, after $\lceil r/g\rceil$ stages the recovered bits are the true bad-shield values and $Y(\beta)$ is the trace. Not formalized: circuit size and depth bounds, Corollaries 5.3 and 5.4, the pointer-doubling evaluator (Proposition 3.1), uniformity, and the abstract lifting theorem (Theorem 7.1).

## Sources

Rewritten from the following internal notes (document numbers of the 27 October 2026 corpus review):
- #20 Blockwise Causal Compilation for Sparse-Unshielded Sequential NOR (`Blockwise_Causal_Compilation_SeqNOR.pdf`), all of it: Proposition 3.1, Lemma 4.1, Corollary 4.2, Lemma 5.1, Theorem 5.2, Corollaries 5.3–5.4, Proposition 6.1, Example 8.1, §9 audit, §10 discussion.
- #18 Sequential NOR Structural Parallelization Compendium (`Sequential_NOR_Structural_Parallelization_Compendium.pdf`), §5: Theorem 5.4 (general causal block-lifting lemma) and Correction 32.2 (the baseline hierarchy is valid but superseded).
- #19 Sequential NOR Binary Core Compilation (`Sequential_NOR_Binary_Core_Compilation.pdf`), §3 (the same compiler in its residual-evaluator form).

## Status

All results are proved in full, including the unary residual evaluator, which the source only summarized and attributed to an earlier unpublished note; its proof is given here by pointer doubling over the four unary Boolean maps. The results are promise-class (parameterized) upper bounds, not unconditional results: polynomial size and depth O(log² n + r log n) when the number r of bad shields is bounded by a cap, hence NC^max(2,c+1) for r = O(log^c n). The method is the standard guess-and-check of O(log n) bits per block; the only problem-specific point is that each block has exactly one valid guess. As the source compendium itself notes, the bound is superseded for Sequential NOR by the binary-core compiler of manuscript 006f (depth O(log² n + r), NC^max(2,c), and logspace for r = O(log n)); the paper says so and keeps the result for its abstract block-lifting form, which needs only a shallow residual evaluator. Nothing was found false. The construction was checked exhaustively for all 46,233 parent arrays with n ≤ 8 and five block widths; this is a regression check only. Not refereed.

## Code

Checking scripts used for this manuscript are in [`verification/`](verification/): `check_core.py`. They are plain Python 3 with no dependencies outside the standard library unless the script says otherwise.
