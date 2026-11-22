# [Newton's Method Evaluates Circuits in Strahler-Rank Rounds](paper.pdf)

**Author:** Generated Computers

**Date:** November 3, 2026

## Citation

```bibtex
@misc{GC:Newtons-Method-Evaluates-Circuits-in-Strahler-Rank-Rounds-November-3-2026,
  author = {{Generated Computers}},
  title = {{Newton's Method Evaluates Circuits in Strahler-Rank Rounds}},
  howpublished = {Generated Computers preprint, manuscript 002a},
  year = {2026}
}
```



## Lean

Part of this paper is formalized in Lean 4 with Mathlib, in the [Lean library](../../lean/README.md). The scope is described in [`lean/docs/002.md`](../../lean/docs/002.md), and the main statements are in the Comparator challenge [`NewtonStrahlerRounds.lean`](../../lean/ComparatorChallenges/NewtonStrahlerRounds.lean). Every listed theorem is proved without `sorry` and uses only the axioms `propext`, `Quot.sound` and `Classical.choice`. Complexity-theoretic conclusions (logspace, NC, P-completeness and the like) are not formalized.

**002a (Newton's method).** An affine–product circuit over $\mathbb F_2 = $ `ZMod 2` is a list of constant gates, affine gates $x_i = c_i + \sum_{j\in A(i)} x_j$ and product gates $x_i = x_{p(i)}x_{q(i)}$ with $p(i)\ne q(i)$, all parents preceding the gate. The Lean development defines the residual $F$, the formal Jacobian $J(x)$, the exact Newton map $N(x) = x + J(x)^{-1}F(x)$ (with Mathlib's matrix inverse), and the Horton–Strahler rank $\rho$ by the recursion of Definition 3.2. It proves that $J(x)$ is unit lower triangular ($\det J(x) = 1$), that the value vector exists and is unique, that $N(x) = x$ exactly at the value vector, the exact error identity $J(x)e^+ = Q(e)$ (Lemma 3.1), and the Newton–Strahler theorem (Theorem 3.4): from any start, after $t$ steps every gate of rank $< t$ is exact, so $\rho(C)+1$ steps give the value vector. It also proves the valid-layering form of Remark 3.5(ii) (the rank is the smallest valid layering, and any valid layering bounded by $K$ certifies $K+1$ rounds). For gates of higher degree (Section 6), it defines triangular Boolean systems with arbitrary gate functions, the multilinear derivative $\partial_S$ (as the $\mathbb F_2$ finite difference $\sum_{T\subseteq S} g(x_S := 1_T)$, which is the formal derivative of the algebraic normal form; this identification is standard and is not itself proved in Lean), the Taylor remainder and the corrected Taylor rank of Definition 6.3, and proves the multilinear Taylor identity (Lemma 6.1), the exact error identity $J(x)e^+ = R(x,e)$ (Theorem 6.2) and the Taylor-rank contraction (Theorem 6.5). Affine gates with an empty input set are allowed (they are constant gates). The depth and size accounting (Lemma 4.1, Theorem 4.2, Corollary 4.3, Theorem 7.4) is not formalized; neither are the affine–product normal form (Lemma 2.2), the derivation-tree characterization of the rank (Proposition 3.7), the reduction to the integer Newton map (Remark 3.8), the multiplexer lemmas of Section 7, the examples of Section 5 and the rank-frontier quotient of Section 8.

## Sources

Rewritten from the following internal notes (document numbers of the 27 October 2026 corpus review):
- #26, *Closest Results Toward P ⊆ SP — full proofs* (`Closest_Results_Toward_P_in_SP_Full_Proofs_20260820.pdf`),
  Appendix Q (Lemma Q.1, Lemma Q.2, Theorem Q.3, Theorem Q.4, Corollary Q.5, the examples of Q.6–Q.7,
  Lemma Q.7 and Theorem Q.8; PDF pp. 143–149) and Appendix R (Lemma R.1, Theorem R.2, Definition R.3,
  Lemma R.4, Theorem R.5, Section R.5.1, Lemma R.6, Theorem R.7, Remark R.8, Lemma R.9 and Theorem R.10;
  PDF pp. 150–156). In the internal numbering these appendices are the "Phase 23" and "Phase 24" chapters.

## Status

Proved in full: the exact one-step error identity J(x)e⁺ = Q(e) over GF(2); the Newton–Strahler
theorem (from any start, gates of rank < t are exact after t steps, so ρ+1 steps evaluate the circuit);
the triangular-solve lemma and the depth/size accounting (depth O((ρ+1) log² n), size O((ρ+1) n³ log n));
the extension to arbitrary gates through the multilinear Taylor identity and the Taylor rank; sparse
Jacobian rows and the rank formula for compressed multiplexers, and the compressed evaluator; the
rank-frontier quotient for a supplied layering.

Added for positioning (with proofs): the rank is the maximal Esparza–Kiefer–Luttenberger dimension of a
skeleton (derivation) tree; the GF(2) Newton map is the reduction mod 2 of the integer Newton map, so the
zero-start case also follows from the semiring theory, granting a counting identity that we checked by
computer but do not prove. The source never cites Esparza–Kiefer–Luttenberger (J. ACM 2010); the paper
presents the GF(2) form as an exact characteristic-two variant of their analysis.

Corrected relative to the source: (1) the Taylor rank (Definition R.3) gave rank ≥ 1 to every gate without
nonlinear terms under the stated convention max ∅ = 0; the definition now separates that case. (2) The
multiplexer rank formula (Lemma R.6) is exact only when the selector bits are distinct and disjoint from
the data range; these hypotheses are now part of the model, and the formula is an upper bound otherwise.
(3) The rank-frontier quotient (Theorems Q.8, R.10) needs the rank layering; we state it for a supplied
valid layering, since computing ρ is a sequential recurrence not known to be in NC.

Left out: the consequences "ρ(C) = O(n^{1−ε}) for MCP ⇒ P ⊆ SP" (Theorems Q.4, R.7, Corollary Q.9), which
depend on an internal transfer theorem; the paper states only the per-family speedup and says that no
P-complete family with sublinear rank is known. The "junction portfolio" (Q.9), the hard-core descriptions
(Q.10, R.9) and the trivial witness statement (Proposition R.11) are not reproduced.

Checks: exhaustive over all affine–product circuits with at most six gates (3,846,816 circuits with six
gates) and all starting vectors; random circuits for the extensions; the scripts are not in this
repository. Not refereed.
