# [Menger's Theorem Inside One Strahler Layer](paper.pdf)

**Author:** Generated Computers

**Date:** November 3, 2026

## Citation

```bibtex
@misc{GC:Mengers-Theorem-Inside-One-Strahler-Layer-November-3-2026,
  author = {{Generated Computers}},
  title = {{Menger's Theorem Inside One Strahler Layer}},
  howpublished = {Generated Computers preprint, manuscript 005d},
  year = {2026}
}
```



## Lean

Part of this paper is formalized in Lean 4 with Mathlib, in the [Lean library](../../lean/README.md). The scope is described in [`lean/docs/005.md`](../../lean/docs/005.md), and the main statements are in the Comparator challenge [`MengerLayer.lean`](../../lean/ComparatorChallenges/MengerLayer.lean). Every listed theorem is proved without `sorry` and uses only the axioms `propext`, `Quot.sound` and `Classical.choice`. Complexity-theoretic conclusions (logspace, NC, P-completeness and the like) are not formalized.

**005d (Menger's theorem inside one Strahler layer).** Ranked Horn systems are defined with Horton–Strahler proof ranks. The rank-layer reachability lemma `𝓕_{≤k} = 𝓕_{<k} ∪ Reach_{G_k}(S_k)` (`k ≥ 1`) is proved in full, including the case that the source's proof skipped. The closure lemma `D ∩ R = lfp_R(D ∩ H)` is proved for every closed boundary `H` of a region `R`, with `lfp_R` defined as the least closed set. The side-premise star theorem is proved for its derivability pattern: the conclusions `C_i` are derivable exactly for the `i` whose `B_i` is derivable, so all `2^t` patterns occur. Menger's theorem is not in Mathlib, so the unary-spine Menger portal and its corollary are not formalized. Also not formalized are the forest-mass lemma, the `A₅` realization of the star and the portal compilation and complexity theorems.

## Sources

Rewritten from the following internal notes (document numbers of the 27 October 2026 corpus review):
- #38 Menger Unary Spine and Closed Proof Portals (`old_stuff/Menger_Unary_Spine_and_Closed_Proof_Portals_20260821.pdf`), all of it: Definitions 1-2, Lemma 3, Theorem 4, Corollary 5, Theorem 6 and its A5 realization, Definitions 7-9, Theorem 10, Corollary 11, Definition 12, Theorem 13, Definition 14, Theorem 15, Section 8, Theorem 16, Conjecture 17 (pp. 1-9).

## Status

Proved in full: the rank-layer reachability lemma, the forest-mass lemma, the unary-spine Menger theorem and its corollary, the side-premise star and its A5 realization, the closure lemma, polynomial-state closed-portal compilation, joint-lift composition, and polynomial-state rank-band collapse (in an abstract form with explicit state sets and band maps). The portal theorems are conditional on explicitly listed admissible state sets.

Corrections: the source's proof of the layer lemma skipped the case in which the lowest balanced node of a proof has premises of smaller minimum rank; a complete proof is given. The source's Corollary 5 was garbled and is restated as the plain Menger dichotomy. The A5 star uses two distinct nodes with equal values. The source called state capacity the useful parameter; here it is a sufficient condition, and manuscript 005c shows it is not necessary. The closed-portal surplus transfer (source Theorem 16) is reduced to the charging lemma of manuscript 005b and only sketched for its portal branch.

Checks: the layer lemma on 400 random Horn systems, max-flow against brute-force minimum vertex cut on 109 layers, and the A5 star for t=3. The brute-force scripts used for the checks are not part of this repository. Not refereed.

## Code

Checking scripts used for this manuscript are in [`verification/`](verification/): `a5_checks.py`, `a5lib.py`, `horn_checks.py`. They are plain Python 3 with no dependencies outside the standard library unless the script says otherwise.
