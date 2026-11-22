# [Inner Product Has Affine-Cover Number 2ᵐ](paper.pdf)

**Author:** Generated Computers

**Date:** November 3, 2026

## Citation

```bibtex
@misc{GC:Inner-Product-Has-Affine-Cover-Number-2-m-November-3-2026,
  author = {{Generated Computers}},
  title = {{Inner Product Has Affine-Cover Number $2^m$}},
  howpublished = {Generated Computers preprint, manuscript 008c},
  year = {2026}
}
```



## Lean

Part of this paper is formalized in Lean 4 with Mathlib, in the [Lean library](../../lean/README.md). The scope is described in [`lean/docs/008.md`](../../lean/docs/008.md), and the main statements are in the Comparator challenge [`InnerProductCover.lean`](../../lean/ComparatorChallenges/InnerProductCover.lean). Every listed theorem is proved without `sorry` and uses only the axioms `propext`, `Quot.sound` and `Classical.choice`. Complexity-theoretic conclusions (logspace, NC, P-completeness and the like) are not formalized.

**008c (Inner product has affine-cover number 2ᵐ).** Formalized in full: Theorem `thm:ip`. Every affine subspace (Mathlib `AffineSubspace`) contained in `H_m = {(a,b,a·b)}` has at most `2^m` points; the `2^m` affine subspaces `{(a,b,a·b) : b}` lie in `H_m`, cover it and are pairwise disjoint; and the affine-cover number (least number of affine subspaces inside `H_m` covering it) equals `2^m`. Also formalized: exact projection through a left nullspace (Lemma `lem:proj`) and the state-injectivity core of the INDEX bound (Proposition `prop:index`, for a node whose state determines acceptance together with the outside slots). Not formalized: the AU and ALVA languages and their NC³ theorems, the bag recursion of tree decompositions, Proposition `prop:tri`, Proposition `prop:bip`, and the vtree-automaton model itself.

## Sources

Rewritten from the following internal notes (document numbers of the 27 October 2026 corpus review):
- Sequential NOR to SC: Complete Research Compendium (`SEQNOR_main/Sequential_NOR_to_SC_Full_Research_Compendium_Draft.pdf`, document #03), Component 19 (PDF pp. 342–348; results SC-AU-1 to SC-AU-3): affine-union bag messages, AU-TD-CSP in NC^3 (p. 346), triangular half-graph witness, inner-product affine-cover barrier (p. 347).
- Same document, Component 20 (PDF pp. 349–355; results SC-HAV-1 to SC-HAV-3): affine-leaf vtree automata, ALVA-TD-CSP in NC^3, blockwise inner product (p. 353), retained-bank INDEX barrier.

## Status

- Proved in full: exact intersection and left-nullspace projection; the cap-checked AU-TD-CSP and ALVA-TD-CSP theorems (uniform NC^3, for supplied balanced decompositions of width and height O(log N)); the exact reachable-subset projection invariant; the affine-cover number cov(H_m) = 2^m of the graph of inner product (also checked exhaustively for m ≤ 3); the INDEX state lower bound; the treewidth bound and one-piece property of the triangular network.
- Sketched: existence of a balanced decomposition of width q+O(1) for the triangular network, and that the canonical ALVA construction stays within polynomial caps on blockwise inner product (a two-state automaton is proved to exist).
- Clarified: the triangular witness no longer fixes the source variables (otherwise all messages would be trivial); constraints and domains are given as affine unions; the SPAI corollaries are stated as recognizable restrictions with a supplied decomposition, citing the rank-factor network of the companion 008b. The affine-cover bound is presented as an application of the standard isotropic-subspace bound, without novelty claim.
- Not claimed: automatic construction of logarithmic-width decompositions, trajectory reconstruction, any bound for general networks.
- Not refereed.

## Code

Checking scripts used for this manuscript are in [`verification/`](verification/): `ip_check.py`. They are plain Python 3 with no dependencies outside the standard library unless the script says otherwise.
