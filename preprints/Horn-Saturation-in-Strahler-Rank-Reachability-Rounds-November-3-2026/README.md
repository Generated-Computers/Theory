# [Horn Saturation in Strahler-Rank Reachability Rounds](paper.pdf)

**Author:** Generated Computers

**Date:** November 3, 2026

## Citation

```bibtex
@misc{GC:Horn-Saturation-in-Strahler-Rank-Reachability-Rounds-November-3-2026,
  author = {{Generated Computers}},
  title = {{Horn Saturation in Strahler-Rank Reachability Rounds}},
  howpublished = {Generated Computers preprint, manuscript 002b},
  year = {2026}
}
```



## Lean

Part of this paper is formalized in Lean 4 with Mathlib, in the [Lean library](../../lean/README.md). The scope is described in [`lean/docs/002.md`](../../lean/docs/002.md), and the main statements are in the Comparator challenge [`HornStrahlerLayers.lean`](../../lean/ComparatorChallenges/HornStrahlerLayers.lean). Every listed theorem is proved without `sorry` and uses only the axioms `propext`, `Quot.sound` and `Classical.choice`. Complexity-theoretic conclusions (logspace, NC, P-completeness and the like) are not formalized.

**002b (Horn saturation).** A Horn system has a set of axioms and a finite list of rules $P\Rightarrow q$ with a finite set of premises. Derivation trees are an inductive family, and the rank of a tree is the Horton–Strahler combination of Definition 2.2 (the largest child rank, plus one if it is attained by two distinct premises). With $S_k$ the facts having a tree of rank at most $k$ and $S_{-1} = \emptyset$, the formalization proves the exact layer theorem (Theorem 4.1): $S_k$ is the set of facts reachable from the seeds $B_k$ in the graph $G_k$, both built from $S_{k-1}$; consequently the explicitly defined saturation iteration (start from $\emptyset$, one reachability layer per round) gives exactly $S_K$ after $K+1$ rounds. It also proves the stabilization corollary (Corollary 4.2, including $\sigma(q)\le|\mathcal F|-1$ for every derivable fact over a finite set of facts), the identification of the layers with the Boolean Newton operator $N(X) = Df_X^*(f(X))$ (Proposition 6.1, $S_k = N^{k+1}(\emptyset)$), the leaf bound $2^{\mathrm{rank}}\le\#\text{leaves}$ (Lemma 2.3(b)) and the round part of the few-leaves corollary (Corollary 5.3), and the truth-table lemma (Lemma 7.2): the truth-table system of a Boolean circuit of fan-in at most two derives exactly the true facts, each of proof rank at most the depth of its gate. The circuit depth and size bounds of the saturation algorithm (Theorem 5.1) and the equivalence of saturation rank with parallel depth (Theorem 7.3) are complexity statements and are not formalized; only their mathematical cores (the round count and Lemma 7.2) are. The examples of Section 3 are not formalized.

## Sources

Rewritten from the following internal notes (document numbers of the 27 October 2026 corpus review):
- #26, *Closest Results Toward P ⊆ SP — full proofs* (`Closest_Results_Toward_P_in_SP_Full_Proofs_20260820.pdf`),
  Appendix T (Definition T.1, Theorems T.2–T.3, Remark T.4, the truth-table part of Lemma T.5, Proposition
  T.12; PDF pp. 164–169) and Appendix U (Definition U.1, Theorem U.2, Corollary U.3, Proposition U.10; PDF
  pp. 171–175). In the internal numbering these are the "Phase 26" chapter and its successor.

## Status

Proved in full: the exact Strahler-layer theorem (S_k equals the set reachable from the seeds of S_{k-1}
along edges given by rules with a single premise outside S_{k-1}); the saturation algorithm with depth
O((K+1)(log²|F| + log‖R‖)) and polynomial size; stabilization after at most |F| layers; the few-leaves
corollary; the identification of the layers with Boolean Newton iterates; the truth-table lemma; and the
equivalence of saturation rank with parallel depth up to a factor O(log² N).

The layer theorem is presented, as the reviewers noted, as the Boolean-semiring case of the
tree-dimension characterization of Newton's method by Esparza, Kiefer and Luttenberger (J. ACM 2010), which
the source does not cite, and in relation to Datalog (Ullman–Van Gelder 1988, Afrati–Papadimitriou 1993).
The equivalence (Theorem U.2) is presented as a reformulation: a sublinear rank bound for a P-complete
problem is equivalent to a polynomial parallel speedup for it, which is open.

Corrected relative to the source: the second inclusion of Theorem T.2 assumed that every step of the rank-k
spine has exactly one premise outside S_{k-1}; the case of no premise outside is now handled through the
seeds. Theorem U.2 is stated for an arbitrary decision problem; the source's consequence "either statement
implies P ⊆ SP" depends on an internal transfer theorem and is not stated.

Left out: the literal-congruence calculus and its applications (Sections T.4–T.7, Theorems T.7, T.10,
Lemma T.9, Corollary T.8), which depend on internal constructions of other chapters; the extensional block
tabulation and its ceiling (Theorem U.4 onward), which is covered by manuscript 010e. Applications of
ranked saturation to equality calculi and layer circuits are in manuscripts 004a and 005c and are cited, not
repeated.

Checks: the layer theorem and the Newton-operator form were compared with an independent fixed-point
computation of the proof rank on about 25,000 random Horn systems with up to 30 facts; the examples were
checked as well. The scripts are not in this repository. Not refereed.
