# [Separator Speedups Would Put MCVP in NC](paper.pdf)

**Author:** Generated Computers

**Date:** November 3, 2026

## Citation

```bibtex
@misc{GC:Separator-Speedups-Would-Put-MCVP-in-NC-November-3-2026,
  author = {{Generated Computers}},
  title = {{Separator Speedups Would Put MCVP in NC}},
  howpublished = {Generated Computers preprint, manuscript 005a},
  year = {2026}
}
```



## Lean

Part of this paper is formalized in Lean 4 with Mathlib, in the [Lean library](../../lean/README.md). The scope is described in [`lean/docs/005.md`](../../lean/docs/005.md), and the main statements are in the Comparator challenge [`SeparatorSpeedups.lean`](../../lean/ComparatorChallenges/SeparatorSpeedups.lean). Every listed theorem is proved without `sorry` and uses only the axioms `propext`, `Quot.sound` and `Classical.choice`. Complexity-theoretic conclusions (logspace, NC, P-completeness and the like) are not formalized.

**005a (Separator speedups).** The formalization covers the combinatorics of the balanced interval tree on the stages `1, …, N`. It proves that the tree has height `⌈log₂ N⌉`, and it proves the constant-lag lemma: every node is assigned at most `c` of the edges `(s, s + c)`. It also proves the congestion lemma, the linear separator budget `∑_v |E_v| ≤ N - 1` and the bound `#heavy · B < N`. The dyadic-to-chronological frontier lemma is proved: in an all-low subtree of height `h`, every cut is crossed by at most `B h` edges. For the online separator transfer, the formalization proves the counting part. The recursion `Solve`, defined explicitly, makes at most `1 + 2 · #heavy · ⌈log₂ N⌉` calls whenever the low-subtree algorithm fails only at marked nodes. The padding definition, the padding-collapse theorem and the calibration corollary are not formalized. The same holds for the depth bounds and every complexity-class conclusion (MCP ∈ NC, P ⊆ SP).

## Sources

Rewritten from the following internal notes (document numbers of the 27 October 2026 corpus review):
- #34 Separator Padding Collapse and Interface Exponent (`old_stuff/Separator_Padding_Collapse_and_Interface_Exponent_20260820.pdf`), all of it: Definition 1, Lemma 2, Theorem 3, Corollary 4, Definition 5, Theorem 6, Corollary 7, Lemma 8, Conjecture 9, Theorem 10 (pp. 1-5).
- #32: setting (demanded reads, interval tree, linear budget) from Observable Frontier and Quadratic Incidence Barrier (`old_stuff/Observable_Frontier_and_Quadratic_Incidence_Barrier_20260820.pdf`), Section 6.

## Status

- **Correction found by the Lean formalization (3 November 2026):** the proof of the online transfer law claimed $`M < (N/B)h_N`$ for the number $`M`$ of marked nodes. This fails for $`N = 1`$, where $`M = h_N = 0`$. The proof now states $`M \le (N/B)h_N`$, which is what the bound of the theorem uses; the theorem is unchanged.
Proved in full: the constant-lag lemma, the congestion lemma and the padding-collapse theorem (under an explicit padding hypothesis on the evaluator, as in the source), the calibration corollary (its converse direction assumes polynomially bounded word length), the online separator transfer, the frontier lemma and the batched-composition proposition. The transfer, its corollary and the proposition are conditional on hypothetical low-subtree algorithms or combiners; class-level consequences (P in SP) are stated only as conditional implications through Reinhardt's transfer.

Changes relative to the source: the padding definition keeps only the conditions the proof uses, and a lemma shows that constant-lag padding chains satisfy the congestion condition; the online transfer is proved with an explicit recursion and the explicit bound O((1+(N/B)log N)(T_low+log N)) (the source's proof was a sketch); the low-subtree algorithm may simply report failure, and a validation step is added; the remark on padding stability is made precise. The source's suggested next step (batching many first-failure counterexamples) is shown not to work as stated in manuscript 005g.

Checks: the tree-counting statements were verified by brute force on random instances. The brute-force scripts used for the checks are not part of this repository. Not refereed.

## Code

Checking scripts used for this manuscript are in [`verification/`](verification/): `separator_checks.py`. They are plain Python 3 with no dependencies outside the standard library unless the script says otherwise.
