# [Fractional Covers Do Not Certify Sequential Hardness](paper.pdf)

**Author:** Generated Computers

**Date:** November 3, 2026

## Citation

```bibtex
@misc{GC:Fractional-Covers-Do-Not-Certify-Sequential-Hardness-November-3-2026,
  author = {{Generated Computers}},
  title = {{Fractional Covers Do Not Certify Sequential Hardness}},
  howpublished = {Generated Computers preprint, manuscript 003b},
  year = {2026}
}
```



## Lean

Part of this paper is formalized in Lean 4 with Mathlib, in the [Lean library](../../lean/README.md). The scope is described in [`lean/docs/003.md`](../../lean/docs/003.md), and the main statements are in the Comparator challenge [`FractionalCoversHardness.lean`](../../lean/ComparatorChallenges/FractionalCoversHardness.lean). Every listed theorem is proved without `sorry` and uses only the axioms `propext`, `Quot.sound` and `Classical.choice`. Complexity-theoretic conclusions (logspace, NC, P-completeness and the like) are not formalized.

**003b (fractional covers).** Carrier graphs are finite directed graphs with fusion pairs. Paths are nonempty arc chains, and weights are taken over the vertex set of a path. Only weak duality is formalized for the path-flow dual: every dual-feasible pair `(y, λ)` gives `∑ y_e ≤ d` for every primal-feasible `(x, d)`. Strong duality and the node-split flow form are not formalized. The two-path concentration theorem is proved as an exact finite averaging statement: some two paths in the support of `λ` are crossed by at least `D²/s` pairs, and some two paths carry crossing weight at least `D³/s²`. The incomparable case, with factor two, assumes that no support path contains both endpoints of a support pair. The factor-two example is formalized. For two unary rails with readouts containing a perfect matching, the formalization proves that the fractional catalyst load is exactly `h/2`, with matching primal and lower bounds. This covers both the matched-rail mirage and the complete readout grid. For the mirage, the least catalyst height is proved to be `⌈h/2⌉`. Not formalized: the matching and ladder corollaries (Lemma 4.1 and Corollaries 4.5–4.6, including the Erdős–Szekeres step), the `O(log h)` evaluation depth of the mirage and the conditional exponent arithmetic of Section 6.

## Sources

Rewritten from the following internal notes (document numbers of the 27 October 2026 corpus review):
- *The Path-Flow Dual Hack: Exact catalyst duality, path-pair concentration, and why a grid is not yet a compiler* (`old_stuff/Path_Flow_Dual_and_Grid_Mirage_20260822.tex` and `.pdf`, document #47): Theorem 2 (path-flow dual), Theorem 3 (node-flow certificate), Lemma 4, Theorem 5 and Corollaries 6-7 (concentration, crossing matching, ladder), Theorem 8 and the complete grid (mirage), Theorems 11-13 (exponent ledgers), pp. 2-8.

## Status

Proved in full: the exact LP dual, its node-split flow form, the fractional-matching lemma, two-path concentration, the crossing matching, the ordered ladder, the matched-rail mirage and the complete readout grid. **Correction:** the source assumed that the two parents of every fusion are incomparable; this is false for Sequential NOR, where the parents of every gate are comparable. The concentration bounds are now stated without the assumption, with half the source's constants (D^2/s, D^3/s^2, D^3/(2s^2), D^{3/2}/(sqrt 2 s)); the source's constants are kept as the incomparable case, and an example shows that the factor two is necessary. The mirage now also records that the integral catalyst height is ceil(h/2) (reviewer observation), so integral as well as fractional catalyst height is linear on circuits of logarithmic depth. The exponent ledgers 2/3, 3/4, 4/5 are kept only as conditional arithmetic about a hypothetical procedure, not as theorems. Left out: the rail-module contraction theorem (Theorem 9) and the closing conjecture, which rely on undefined notions (hard mass, the standard permanent-progress ledger, self-hosting). Checked in exact arithmetic: the mirage certificates and the integral height for h <= 8 (all 2^h covers), and the concentration bounds for 383 random DAGs with random feasible duals. Not refereed.

## Code

Checking scripts used for this manuscript are in [`verification/`](verification/): `check_47_41.py`. They are plain Python 3 with no dependencies outside the standard library unless the script says otherwise.
