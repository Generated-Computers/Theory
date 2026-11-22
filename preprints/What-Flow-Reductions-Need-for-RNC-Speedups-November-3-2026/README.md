# [What Flow Reductions Need for RNC Speedups](paper.pdf)

**Author:** Generated Computers

**Date:** November 3, 2026

## Citation

```bibtex
@misc{GC:What-Flow-Reductions-Need-for-RNC-Speedups-November-3-2026,
  author = {{Generated Computers}},
  title = {{What Flow Reductions Need for RNC Speedups}},
  howpublished = {Generated Computers preprint, manuscript 003c},
  year = {2026}
}
```



## Lean

Part of this paper is formalized in Lean 4 with Mathlib, in the [Lean library](../../lean/README.md). The scope is described in [`lean/docs/003.md`](../../lean/docs/003.md), and the main statements are in the Comparator challenge [`FlowReductionsRNC.lean`](../../lean/ComparatorChallenges/FlowReductionsRNC.lean). Every listed theorem is proved without `sorry` and uses only the axioms `propext`, `Quot.sound` and `Classical.choice`. Complexity-theoretic conclusions (logspace, NC, P-completeness and the like) are not formalized.

**003c (flow reductions and RNC).** The main theorems of this manuscript are conditional parallel-complexity statements, and they are not formalized: the randomized flow transfer, the RNC transfer, NC verification and the PRAM cost of the Las Vegas conversion. The formalized parts are only the exact mathematical facts behind them. The first is cost-independent conservation (Proposition 7.1): the net outflows of all vertices sum to zero, and a gadget with no internal supplies has external outflow equal to external inflow. The second is the expectation `∑_{k≥1} k p (1−p)^{k−1} = 1/p` and the total probability `1` behind Corollary 6.2. The third is the exponent arithmetic of Theorem 4.1 and Corollary 4.2 (`√(S^α)·S^λ = S^{α/2+λ}`). The fourth is the three inequalities of the calibration proposition 4.4.

## Sources

Rewritten from the following internal notes (document numbers of the 27 October 2026 corpus review):
- *The Randomized Flow Escape: P in RNC, zero-error strict speedup, and the numerical-scale bottleneck* (`old_stuff/Randomized_Flow_Escape_RNC_and_RSP_20260822.pdf`, document #48): Definitions 1-2, Theorem 3 and Corollary 4 (ledger), Theorem 5 (RNC transfer), Theorem 6 and Corollary 7 (verification, Las Vegas), Lemma 8 (random costs), Sections 7 and 11 (audit and targets), pp. 2-8.

## Status

A ledger of conditional statements, as the review asked. The main transfer theorem is stated under an explicit hypothesis (a min-cost-flow solver with polynomial work and depth sqrt(N) L polylog), because the source's citation for it (a 2025-2026 parallel min-cost-flow paper) could not be verified. The RNC transfer for quasi-polynomial data is stated under a second hypothesis, the source's reading of Orlin and Stein (1993), which the reviewer flagged as unverified; for polynomially bounded data it holds unconditionally via randomized weighted matching (Mulmuley-Vazirani-Vazirani). Added, following the review: a calibration against the trivial depth-d evaluator (the flow route helps only if L = o(d/sqrt N); a hierarchy whose bit length tracks the depth gains nothing; the Goldschlager-Shaw-Staples reduction gives depth S^{3/2}). Proved in full and standard: NC verification of optimal flows and the Las Vegas conversion, and the conservation lemma. Left out: the audit of Stein-Wein's numerical parameters (the source could not access the paper either) and the discussion of 2026 strongly polynomial algorithms, whose citations could not be verified. BP-SP, ZP-SP and RSP are bookkeeping names, not standard classes. Not refereed.
