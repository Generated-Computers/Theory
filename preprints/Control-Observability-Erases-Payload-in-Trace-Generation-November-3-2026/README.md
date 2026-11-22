# [Control Observability Erases Payload in Trace Generation](paper.pdf)

**Author:** Generated Computers

**Date:** November 3, 2026

## Citation

```bibtex
@misc{GC:Control-Observability-Erases-Payload-in-Trace-Generation-November-3-2026,
  author = {{Generated Computers}},
  title = {{Control Observability Erases Payload in Trace Generation}},
  howpublished = {Generated Computers preprint, manuscript 005f},
  year = {2026}
}
```



## Lean

Part of this paper is formalized in Lean 4 with Mathlib, in the [Lean library](../../lean/README.md). The scope is described in [`lean/docs/005.md`](../../lean/docs/005.md), and the main statements are in the Comparator challenge [`ControlObservability.lean`](../../lean/ComparatorChallenges/ControlObservability.lean). Every listed theorem is proved without `sorry` and uses only the axioms `propext`, `Quot.sound` and `Classical.choice`. Complexity-theoretic conclusions (logspace, NC, P-completeness and the like) are not formalized.

**005f (Control observability).** The affine history machine over `ℚ` is defined as an explicit step function. Invalid addresses read `0`, a convention that normalized executions never use. The control-observability closure (C1)–(C3), demanded reads and control-live cells are defined. The theorem "control-observable state suffices" is proved in its two-execution form. Take two executions that agree at a cut `τ` on the control state, on the functionals of `L_τ`, on the external history and on the control-live cells. They then have the same addresses, branch bits and control states for the rest of the interval. For the balanced ladders `D_{r,w}`, the formalization proves three facts. Every vertex of layer `k` has Strahler rank `k`, its two predecessors are distinct, and there are exactly `2rw` edges. The linear separator budget and the counting part of the separator transfer are the 005a theorems. The least-closure lemma, the asymptotic corollary on `N/log²N` and all complexity statements are not formalized.

## Sources

Rewritten from the following internal notes (document numbers of the 27 October 2026 corpus review):
- #32 Observable Frontier and Quadratic Incidence Barrier (`old_stuff/Observable_Frontier_and_Quadratic_Incidence_Barrier_20260820.pdf`), all of it: the kernel of Section 1, Definition 1, Theorem 2, Corollary 3, Remark 4, Definitions 5-6, Theorem 7, Corollary 8, Theorem 9, Lemma 11, Definition 12, Theorem 13, Conjecture 15 (pp. 1-6).

## Status

Proved in full: the ladder construction and its corollary, the least-closure lemma (the source only asserted existence), the control-observable sufficiency theorem in a precise two-execution form and its payload-erasure corollary, the linear separator budget, and the separator transfer (conditional on a hypothetical compiler). The closure is identified as backward dynamic program slicing and linear observability; no novelty is claimed for it.

Left open: the source's control-observable frontier generator (Theorem 9) had only a proof architecture. Soundness, completeness, monotonicity in the epoch end and restart by trace triangularization go through, but the annotated state universe (row spaces and their values) is not known to be polynomial in the evaluator's word model, so the statement is given as an open problem. The observable-separator conjecture is stated together with the remark, proved in manuscript 005a, that under benign padding it already implies that MCP is in NC.

Checks: ladder identities for small r and w, and payload erasure on two runs of 400 random machines over the field with 101 elements. The brute-force scripts used for the checks are not part of this repository. Not refereed.

## Code

Checking scripts used for this manuscript are in [`verification/`](verification/): `kernel_checks.py`. They are plain Python 3 with no dependencies outside the standard library unless the script says otherwise.
