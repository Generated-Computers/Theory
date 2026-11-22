# [Finding Pigeonhole Collisions in A₅ Is P-Complete](paper.pdf)

**Author:** Generated Computers

**Date:** November 3, 2026

## Citation

```bibtex
@misc{GC:Finding-Pigeonhole-Collisions-in-A5-Is-P-Complete-November-3-2026,
  author = {{Generated Computers}},
  title = {{Finding Pigeonhole Collisions in $A_5$ Is P-Complete}},
  howpublished = {Generated Computers preprint, manuscript 004a},
  year = {2026}
}
```



## Lean

Part of this paper is formalized in Lean 4 with Mathlib, in the [Lean library](../../lean/README.md). The scope is described in [`lean/docs/004.md`](../../lean/docs/004.md), and the main statements are in the Comparator challenge [`PigeonholeCollisionsA5.lean`](../../lean/ComparatorChallenges/PigeonholeCollisionsA5.lean). Every listed theorem is proved without `sorry` and uses only the axioms `propext`, `Quot.sound` and `Classical.choice`. Complexity-theoretic conclusions (logspace, NC, P-completeness and the like) are not formalized.

**004a (pigeonhole collisions).** The Maurer–Rhodes theorem is proved in full generality: every
function $G^k\to G$ of a finite simple nonabelian group is given by a group term with constants.
From it: the 61-probe selector for $A_5$ (61 fixed unary terms whose values at any $x$ contain
exactly one equal pair, $\{0, j+1\}$ for $x=g_j$; Theorem 3.2), the fact that any colliding pair
determines $x$ (core of Corollary 3.4), and predicate-complete equality (Theorem 3.5). The
universal-collision count is formalized: $N$ nodes with value tables over a context set $X$ contain
at least $(N-60^{|X|})/2$ disjoint pairs equal in every context (Theorem 4.2, Corollary 4.3). The
value/equality calculus (R1)–(R6) is defined as an inductive predicate and proved sound and complete
for well-formed programs (Theorem 5.1). The Boolean gadget lemma (Lemma 2.2) is formalized as a
compilation of Boolean circuits into $A_5$ multiplication circuits of size at most $17s$ and then,
via the two-generator normal form, into constant-free programs over $P\mapsto p$, $Q\mapsto q$. Not
formalized: the P-hardness claims as complexity statements, the depth bounds of ranked saturation
(Theorem 6.2), the spine lemma, component collapse (Theorem 6.4) and the conditional surplus law
(Section 7).

## Sources

Rewritten from the following internal notes (document numbers of the 27 October 2026 corpus review):
- #37, *Equality Saturation Is Predicate-Complete: the 61-probe barrier, ranked exact closure, and
  the semantic compression surplus law* (`old_stuff/Equality_Saturation_Predicate_Completeness_and_Surplus_Law_20260821.pdf`),
  the whole note: Thms 1–2, Cor 3, Thm 4 (pp. 2–3); Def 5, Thm 6, Cor 7 (pp. 3–4); the calculus and
  Thm 8 (pp. 4–5); Thm 9 (p. 5); Def 10, Thm 11, Remark 12, Thms 13–14 (p. 6); Def 15, Thm 16,
  Cor 17 (p. 7); Section 9 (p. 8).
- #29, *A5 Is the Strict Core* (`old_stuff/A5_Strict_Core_and_Reconvergence_Frontier_20260820.pdf`),
  Lemma 2 and Thm 3 (p. 2): the concrete NOT/AND gadget elements used in the gadget lemma.
- #35, *The Deep Perfect Core* (`old_stuff/Deep_Perfect_Core_and_Shadow_Annihilation_20260821.pdf`),
  Lemma 14 (p. 7): the linear collision matching quoted in the introduction.

## Status

Proved in full: the 61-probe selector and the P-hardness of the collision search problem
(Thm 3.2, Cor 3.4), predicate-complete equality (Thm 3.5), context-signature contraction and its
two-anchor corollary (Thm 4.2, Cor 4.3), soundness and completeness of the value/equality calculus
and P-completeness of its full closure (Thm 5.1, Prop 5.2), rank-K saturation in depth
O((K+1) log^2 n) (Thm 6.2, with an explicit spine lemma), exact component collapse (Thm 6.4), and
the surplus law (Thm 7.2, Cor 7.3), which is a conditional statement whose hypothesis is open. The
selector rests on the Maurer–Rhodes theorem (quoted, not reproved); the probe terms were not
computed.

Changes relative to the source: the surplus law is stated with an explicit depth bound
O(n^{1-ε} log^{c+2} n) for A5 evaluation; the source's conclusion "P ⊆ SP" is not claimed and the
transfer to all of P is discussed only in a remark (via Pippenger–Fischer), as a reduction to the
open hypothesis. Of the three alternatives in the source's hypothesis, only the collapse-surplus
branch is kept; the "ancestrally liftable kernel" branch refers to a notion not defined in the
source. The exponent corollary is restricted to α − β < 1 with an explicit log exponent. Sorting in
Thm 6 was replaced by pairwise comparison. Section 9 of the source ("no density argument can
lower-bound the surplus") is kept only as an informal remark. Conjecture 18 (an open target) is
omitted. The layered-reachability idea of Thm 6.2 is the special case of the companion manuscript
002b and of the Strahler-rank analysis of Esparza–Kiefer–Luttenberger (2010), which are cited.

Computer checks (script `verification/check_a5.py`, permutations of five points): the probe colorings, the
generation of A5 by (12345), (123) with words of length ≤ 6, the gadget identities, and, on random
two-generator programs with up to five nodes, soundness, completeness and the equality of the
layered procedure with the least Strahler rank of every fact.

Not refereed.
