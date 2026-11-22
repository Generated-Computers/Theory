# [P-Complete A₅ Circuits Invisible to Solvable Groups](paper.pdf)

**Author:** Generated Computers

**Date:** November 3, 2026

## Citation

```bibtex
@misc{GC:P-Complete-A5-Circuits-Invisible-to-Solvable-Groups-November-3-2026,
  author = {{Generated Computers}},
  title = {{P-Complete $A_5$ Circuits Invisible to Solvable Groups}},
  howpublished = {Generated Computers preprint, manuscript 004b},
  year = {2026}
}
```



## Lean

Part of this paper is formalized in Lean 4 with Mathlib, in the [Lean library](../../lean/README.md). The scope is described in [`lean/docs/004.md`](../../lean/docs/004.md), and the main statements are in the Comparator challenge [`InvisibleToSolvable.lean`](../../lean/ComparatorChallenges/InvisibleToSolvable.lean). Every listed theorem is proved without `sorry` and uses only the axioms `propext`, `Quot.sound` and `Classical.choice`. Complexity-theoretic conclusions (logspace, NC, P-completeness and the like) are not formalized.

**004b (invisible to solvable groups).** Every element of $A_5$ is a commutator (explicit table).
The commutator tower $R_{g,d}$ is defined in the free group $F(P,Q)$ and proved to evaluate to $g$
and to lie in $F^{(d)}$ (Theorem 4.2(i),(ii)); substituting it for the constants of an $A_5$ circuit
keeps every value and puts every node into $F^{(d)}$ (Theorem 5.1, semantic part). Proved in general:
$G^{(d)}\le\gamma_{2^d}(G)$ (Lemma 2.1, via a three-subgroup lemma modulo a normal subgroup), shadow
annihilation for solvable images of derived length $\le d$ and nilpotent images of class $<2^d$
(Theorem 6.1), and that a finite solvable group of order $<2^d$ has trivial $d$-th derived subgroup
(Corollary 6.2, Remark 6.3(1)). The two-generator normal form (Theorem 3.1) is formalized with a
library of 60 nodes (size $s+60$). Not formalized: the node count $64+240d$ of the shared tower as an
explicit program (Theorem 4.2(iii)), logspace constructibility, and the P-completeness of
$\mathrm{Deep}_c$ (Theorem 5.2) as a complexity statement.

## Sources

Rewritten from the following internal note (document numbers of the 27 October 2026 corpus review):
- #35, *The Deep Perfect Core: two generators, linear size, and the annihilation of solvable and
  nilpotent shadows* (`old_stuff/Deep_Perfect_Core_and_Shadow_Annihilation_20260821.pdf`), the whole
  note: Def 1, Thm 2 (p. 2); Def 4, Thm 5 (p. 3); Thms 6–7 (pp. 3–4); Lemma 8, Cor 9 (p. 4);
  Thm 10, Cor 11 (p. 5); Prop 12 (pp. 5–6); Section 8 (p. 6); Lemma 14 (p. 7).

## Status

Proved in full: the two-generator normal form (Thm 3.1), the shared commutator tower with an
explicit size bound 64 + 240d (Thm 4.2), the deep perfect reduction (Thm 5.1), P-completeness of
the deep-core promise problem with the explicit constant c = 1/305 (Thm 5.2), exponential lower
central depth (Cor 5.3), and shadow annihilation for solvable images of derived length ≤ d and
nilpotent images of class < 2^d (Thm 6.1, Cor 6.2).

Changes relative to the source: the consequence "P ⊆ SP" claimed in Cor 3 and Thm 7 of the
source relies on a strict transfer from another note and is not claimed; Thm 5.2 states
P-completeness instead. "Every node lies deep" is made precise: every node coming from the original
circuit lies in F^(d); the lower tower levels do not. The note's Cor 11(ii) (nilpotent case) is
subsumed by the solvable case for polynomial-size images, which is said; the remark that the proof
covers every solvable image of order < 2^d is read off from the proof. Every element of A_n being a
commutator is attributed to Ore (1951) as well as to Liebeck–O'Brien–Shalev–Tiep (2010). Omitted:
the collision-shrink transfer criterion (Thm 15, a conditional statement in terms of an undefined
"liftable kernel") and Conjecture 16; the collision question is treated in companion manuscript
004a.

Computer checks (script `verification/check_a5.py`): generation of A5 by (12345), (123) with words of
length ≤ 6, every element a commutator, and the tower values for d ≤ 6.

Not refereed.
