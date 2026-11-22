# [Exponential-State Portals with Constant-Depth Transfer](paper.pdf)

**Author:** Generated Computers

**Date:** November 3, 2026

## Citation

```bibtex
@misc{GC:Exponential-State-Portals-with-Constant-Depth-Transfer-November-3-2026,
  author = {{Generated Computers}},
  title = {{Exponential-State Portals with Constant-Depth Transfer}},
  howpublished = {Generated Computers preprint, manuscript 005c},
  year = {2026}
}
```



## Lean

Part of this paper is formalized in Lean 4 with Mathlib, in the [Lean library](../../lean/README.md). The scope is described in [`lean/docs/005.md`](../../lean/docs/005.md), and the main statements are in the Comparator challenge [`StatePortals.lean`](../../lean/ComparatorChallenges/StatePortals.lean). Every listed theorem is proved without `sorry` and uses only the axioms `propext`, `Quot.sound` and `Classical.choice`. Complexity-theoretic conclusions (logspace, NC, P-completeness and the like) are not formalized.

**005c (Exponential-state portals).** For `M(x, y) = e` if `x = e` and `y` otherwise, the formalization proves two facts. The output vectors cover all of `G^t`, and the hard-coefficient capacity switch holds: the image has one element if `x = e`, and otherwise `|G|^t` elements (`60^t` for `A₅`). For ranked Horn systems, the rank-layer map `Φ(X) = Reach_{G(X)}(X ∪ Seed(X))` is proved monotone and to satisfy `Φ(𝓕_{<k}) = 𝓕_{≤k}` for `k ≥ 1`. The band corollary `Φ^B(𝓕_{<k}) = 𝓕_{≤k+B-1}` is also proved. A two-fact example confirms the paper's correction that the source's newly-derivable map is not monotone. The stopping rule of the one-shot criterion is proved: the first rank `K` with `min_{K' ≤ K}(K' + c_{K'}) ≤ K` is at most `min_K (K + c_K)`. Circuit size and depth, the symbolic and branching-program portal theorems, the composition-algebra theorem and the fanout-kernel compiler's depth bound are not formalized. The realization of `M` as an `A₅` term (Maurer–Rhodes) is not formalized either.

## Sources

Rewritten from the following internal notes (document numbers of the 27 October 2026 corpus review):
- #40 State Capacity Is Not the Portal Parameter (`old_stuff/State_Capacity_Is_Not_the_Portal_Parameter_20260821.pdf`), all of it: Theorems 1-2, Proposition 3, Definition 4, Theorem 5, Definition 6, Theorem 7, Theorem 8, Corollary 9, Definition 10, Theorem 11, Definition 12, Lemma 13, Theorem 14, Corollary 15, Theorem 16, Definition 17, Corollary 18, Theorem 19, Conjecture 20 (pp. 1-9).

## Status

Proved in full: the side-premise star and full-capacity A5 portals, the hard-coefficient switch, symbolic and branching-program portal composition, the rank-layer monotone circuit and its band corollary, composition-algebra chain collapse, the fanout-kernel compiler, the equality-assisted fanout bound, and the one-shot fanout criterion (with an added search over the rank K, which the source did not describe).

Corrections: the rank-layer transfer is stated for the map from facts of rank below k to facts of rank at most k; the source's map to the facts newly derivable at rank k is a set difference and is not monotone. The composition algebra is required to have a uniform polynomial size bound, without which prefix composition could blow up. A remark makes precise why a universal composition algebra for Horn systems cannot exist unless P is contained in NC. The combined transfer criterion (source Theorem 19) is proved for its fanout branch and only sketched for its portal branches. The fanout-height refinement is in manuscript 005e.

Checks: the A5 capacity switch (t=2), the formula-forest property and the fanout compiler on random A5 programs, and the layer operator on random Horn systems. The brute-force scripts used for the checks are not part of this repository. Not refereed.

## Code

Checking scripts used for this manuscript are in [`verification/`](verification/): `a5_checks.py`, `a5lib.py`, `fanout_checks.py`, `horn_checks.py`. They are plain Python 3 with no dependencies outside the standard library unless the script says otherwise.
