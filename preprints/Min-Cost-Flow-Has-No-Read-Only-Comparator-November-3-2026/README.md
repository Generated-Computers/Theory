# [Min-Cost Flow Has No Read-Only Comparator](paper.pdf)

**Author:** Generated Computers

**Date:** November 3, 2026

## Citation

```bibtex
@misc{GC:Min-Cost-Flow-Has-No-Read-Only-Comparator-November-3-2026,
  author = {{Generated Computers}},
  title = {{Min-Cost Flow Has No Read-Only Comparator}},
  howpublished = {Generated Computers preprint, manuscript 003a},
  year = {2026}
}
```



## Lean

Part of this paper is formalized in Lean 4 with Mathlib, in the [Lean library](../../lean/README.md). The scope is described in [`lean/docs/003.md`](../../lean/docs/003.md), and the main statements are in the Comparator challenge [`MinCostFlowNoComparator.lean`](../../lean/ComparatorChallenges/MinCostFlowNoComparator.lean). Every listed theorem is proved without `sorry` and uses only the axioms `propext`, `Quot.sound` and `Classical.choice`. Complexity-theoretic conclusions (logspace, NC, P-completeness and the like) are not formalized.

**003a (no read-only comparator).** An open network has arbitrary finite arc and internal-vertex types, integral lower and upper bounds, integral (possibly negative) costs and fixed integral internal excesses. Its boundary function `Φ_G(b)` is defined as the least cost of a feasible integral flow with boundary `b` (`⊤` if there is none). The formalization proves the boundary exchange theorem: `Φ_G` satisfies the M-convex exchange axiom for every network with nonempty domain. It also proves the flow-level exchange behind it, by a conformal path-extraction lemma. Using only the exchange theorem, it proves that no network is a pass-through gadget, with context-independence condition (ii), whose table vanishes on the two all-equal states and is positive on every proper nonempty set of channels (no all-equal sensor, any `r ≥ 2`). In particular no network is a read-only comparator with table `|x − y|`. The crossbar remark is proved: the four-arc crossbar realizes `|x − y|` on the intended states, but its two crossed states cost `0`. The one-shot comparator identity is proved. So is the theorem that no submodular function on visible and auxiliary Boolean labels has the NAND relation, or any of its eight complemented versions, as its projected minimizer relation. The statement that graph-cut energies are submodular is not formalized, and neither is the "no local bridge" corollary as a separate statement. That corollary is the all-equal-sensor theorem applied to the residual program.

## Sources

Rewritten from the following internal notes (document numbers of the 27 October 2026 corpus review):
- *Read-Only Flow Comparison Is Impossible: The M-convex boundary barrier and the exact primal-dual frontier* (`old_stuff/M_Convex_Readonly_Flow_Barrier_20260822.pdf`, document #44), the whole note: Theorem 1 (one-shot comparator), Theorem 2 (boundary exchange), Theorem 3 (no read-only comparator), Corollary 4 (no all-equal sensor), Lemmas 5-6 and Theorem 7 (no cut/potential NAND gadget), Theorem 8 (no local bridge), Sections 7-10 (discussion), pp. 2-8.

## Status

All results are proved in full. The boundary exchange theorem (Theorem 3.1) is the network induction of M-convex functions from discrete convex analysis (Murota); it is attributed and included with an elementary flow-exchange proof. The no-go theorem for read-only comparators and the all-equal-sensor corollary are stated with an explicit context-independence condition (unintended boundary states cost more than the cheapest intended state); the source used this condition informally, and its proof of the all-equal sensor (Corollary 4) omitted the crossed states, which the rewritten proof treats. A remark shows by a four-arc crossbar that the condition cannot be dropped (reviewer observation). The no-submodular-NAND theorem is presented as a direct consequence of the lattice of submodular minimizers (Topkis; Kolmogorov-Zabih), not as new. The source's Theorem 8 appears as a corollary about the residual NAND program of the companion manuscript 003d. The source's reference to Iwata and Tanigawa (Discrete Applied Mathematics 82, 1998) could not be confirmed and was dropped; Hassin (2022) was dropped for the same reason. Checked by exhaustive enumeration: the exchange axiom and the absence of the comparator signature on 1,238 random networks with four terminals and at most two internal vertices, the crossbar table, and that no complementation of coordinates makes the NAND relation a lattice. Not refereed.

## Code

Checking scripts used for this manuscript are in [`verification/`](verification/): `check_44.py`. They are plain Python 3 with no dependencies outside the standard library unless the script says otherwise.
