# [P-Complete Equal-Flow Programs with Capacities at Most Two](paper.pdf)

**Author:** Generated Computers

**Date:** November 3, 2026

## Citation

```bibtex
@misc{GC:P-Complete-Equal-Flow-Programs-with-Capacities-at-Most-Two-November-3-2026,
  author = {{Generated Computers}},
  title = {{P-Complete Equal-Flow Programs with Capacities at Most Two}},
  howpublished = {Generated Computers preprint, manuscript 003d},
  year = {2026}
}
```



## Lean

Part of this paper is formalized in Lean 4 with Mathlib, in the [Lean library](../../lean/README.md). The scope is described in [`lean/docs/003.md`](../../lean/docs/003.md), and the main statements are in the Comparator challenge [`EqualFlowCapacityTwo.lean`](../../lean/ComparatorChallenges/EqualFlowCapacityTwo.lean). Every listed theorem is proved without `sorry` and uses only the axioms `propext`, `Quot.sound` and `Classical.choice`. Complexity-theoretic conclusions (logspace, NC, P-completeness and the like) are not formalized.

**003d (equal-flow programs).** Monotone fan-in-two circuits are given in topological order on `Fin n`, and their values are defined by recursion. The NAND normalization of alternating circuits is proved. So is the NAND polytope theorem: the convex hull in `ℝ³` of the four NAND triples equals the polytope cut out by `z + x ≥ 1`, `z + y ≥ 1`, `z + x + y ≤ 2` and the unit cube. The forcing lemma is proved. The residual NAND program is defined explicitly, with a star spanning tree on the occurrences of each gate; the paper allows any spanning tree. For alternating circuits the formalization proves items (iv) and (v) of the dyadic elimination theorem. The transcript point is feasible with cost `0`, every feasible point has cost `≥ 0`, and every feasible cost-`0` point equals the transcript point on all program variables. The hard-equality form is proved as well: the feasible point is unique and integral, and each gate's occurrences carry `b_u`. The cut-size bound is proved together with the weak max-flow/min-cut inequality it uses. Not formalized: the size bound and the coefficient bookkeeping (i)–(iii) of Theorem 4.2, which hold by inspection of the definition. Also not formalized: the explicit decomposition of Theorem 5.1 into `3g` two-vertex networks with capacities and supplies at most two, and logarithmic-space computability.

## Sources

Rewritten from the following internal notes (document numbers of the 27 October 2026 corpus review):
- *Compiling Away the Dyadic Flow Battery: Constant-scale NAND residuals, homologous fanout, and the exact ordinary-flow gap* (`old_stuff/Dyadic_Capacity_Elimination_20260822.pdf`, document #43): Theorem 1 (NAND normalization), Theorem 2 (NAND polytope), Definition 3 and Theorem 4 (dyadic elimination), Theorem 5 (gate-flow/homology factorization), Proposition 6 (cut-size bound), Definition 7 and Theorem 8 (bridge), pp. 2-7.

## Status

All included results are proved in full. As the review notes, the P-hardness of linear programming with {-1,0,1} coefficients is due to Dobkin, Lipton and Reiss (1979), and hardness of flow problems with extra coupling follows from equivalences of the kind given by Itai (1978); the paper presents the elimination as a refinement of that encoding that locates the non-network structure, not as a new hardness result. Repairs: input occurrences that feed gates of both types receive separate encoded constants; the factorization theorem now gives each equation its own two-vertex network, which makes the claimed bound of two on all supplies and capacities true (a single shared reservoir, as in the source, would have a large supply), and represents each occurrence by one arc per equation in which it appears. Left out as a theorem: the conditional ordinary-flow bridge (Theorem 8), whose premise, a read-only fanout gadget, is refuted by the companion manuscript 003a; it is discussed in the last section. Checked by computer: the vertices of the NAND polytope (exact enumeration) and the NAND normalization on 2,000 random alternating circuits. Not refereed.

## Code

Checking scripts used for this manuscript are in [`verification/`](verification/): `check_43.py`. They are plain Python 3 with no dependencies outside the standard library unless the script says otherwise.
