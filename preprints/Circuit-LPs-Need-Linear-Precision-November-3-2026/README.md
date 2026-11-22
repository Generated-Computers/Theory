# [Circuit LPs Need Linear Precision](paper.pdf)

**Author:** Generated Computers

**Date:** November 3, 2026

## Citation

```bibtex
@misc{GC:Circuit-LPs-Need-Linear-Precision-November-3-2026,
  author = {{Generated Computers}},
  title = {{Circuit LPs Need Linear Precision}},
  howpublished = {Generated Computers preprint, manuscript 003f},
  year = {2026}
}
```



## Lean

Part of this paper is formalized in Lean 4 with Mathlib, in the [Lean library](../../lean/README.md). The scope is described in [`lean/docs/003.md`](../../lean/docs/003.md), and the main statements are in the Comparator challenge [`CircuitLPPrecision.lean`](../../lean/ComparatorChallenges/CircuitLPPrecision.lean). Every listed theorem is proved without `sorry` and uses only the axioms `propext`, `Quot.sound` and `Classical.choice`. Complexity-theoretic conclusions (logspace, NC, P-completeness and the like) are not formalized.

**003f (circuit LPs).** The circuit LP of a monotone circuit is proved to have exactly one feasible point, the value vector. The Fibonacci OR-ladder point is proved for `n ≥ 2`: `x̃_0 = x̃_1 = 0`, `x̃_n = 1/2`, the box and lower OR constraints hold, and every upper OR constraint is violated by exactly `δ = 1/(2(F_{n+1}−1))`. It is also proved that `1/(2φ^n) ≤ δ ≤ φ^{-(n-1)}`. For the ladder matrix `T_m`, `det T_m = 1`, and the minor deleting the first row and last column has absolute value `F_m`. Simultaneous escape switching (Theorem 5.2 (i), (ii), (iv), (v)) is proved. So is the rank-biased bound. Start from a child of maximum Strahler rank at every OR gate. After `k ≥ sr(v)` rounds every true vertex `v` is outside the losing set. If all ranks are `≤ r`, then `L_r` is exactly the set of false vertices and there is no escape. Not formalized: the Latin-component contraction and the low-cyclomatic-excess compiler of Sections 2–3, the Hadamard upper bound, the rank-layer reachability lemma, and all PRAM depth claims.

## Sources

Rewritten from the following internal notes (document numbers of the 27 October 2026 corpus review):
- *Output-Conditioned Latin Closure: Low-excess A5 cores, the LP precision barrier, and a monotone strategy potential* (`old_stuff/Output_Conditioned_Latin_Core_and_LP_Precision_Barrier_20260820.pdf`, document #33): Definitions 1-2 and Theorem 3 (Latin contraction), Definition 4 and Theorem 5 (low excess), Theorem 7 (circuit LP), Theorems 8-9 (Fibonacci precision and subdeterminant), Definition 10 and Theorems 11-12 (escape switching), pp. 2-7.

## Status

- **Hypothesis made explicit after the Lean formalization (3 November 2026):** Theorem 4.2 needs $`n \ge 2`$ (for $`n \le 1`$ the quantity $`F_{n+1} - 1`$ is $`0`$). The hypothesis is now stated.
All included theorems are proved in full. The circuit LP is the Dobkin-Lipton-Reiss encoding and is attributed; the Fibonacci ladder is presented as a clean explicit instance of the known precision phenomenon (Dobkin-Lipton-Reiss 1979, Serna 1991), and the paper says plainly that it does not lower-bound every LP algorithm. The subdeterminant statement gains a matching Hadamard upper bound. Escape switching is attributed to policy iteration and strategy improvement (Howard, Hoffman-Karp, Voge-Jurdzinski), and its r+1 bound is said to match, not improve, the Strahler-rank evaluators of companion manuscripts 002a, 002b and 004g. Repairs: squaring gates are handled in the Latin graph; the Strahler rank is defined explicitly (the source's normalized semantic rank is undefined there), and a lemma shows that the ranks themselves are computed with r+1 reachability calls, which the source's depth bound silently assumed; a remark computes that the cyclomatic excess equals the total extra fanout, so the low-excess compiler covers only near-formulas. Left out: the residual-core corollary (Corollary 6), Conjecture 13 and its consequence (Theorem 14), which restate the open problem. Checked by computer: the Fibonacci point for n <= 39 and the minors for m <= 29 in exact arithmetic, escape switching on 3,000 random circuits (the bound r+1 is attained), the rank-layer lemma on 500 circuits, and Latin contraction over S_3 on 300 random components. Not refereed.

## Code

Checking scripts used for this manuscript are in [`verification/`](verification/): `check_33.py`. They are plain Python 3 with no dependencies outside the standard library unless the script says otherwise.
