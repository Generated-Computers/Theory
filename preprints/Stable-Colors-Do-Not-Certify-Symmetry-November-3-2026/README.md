# [Stable Colors Do Not Certify Symmetry](paper.pdf)

**Author:** Generated Computers

**Date:** November 3, 2026

## Citation

```bibtex
@misc{GC:Stable-Colors-Do-Not-Certify-Symmetry-November-3-2026,
  author = {{Generated Computers}},
  title = {{Stable Colors Do Not Certify Symmetry}},
  howpublished = {Generated Computers preprint, manuscript 004h},
  year = {2026}
}
```



## Lean

Part of this paper is formalized in Lean 4 with Mathlib, in the [Lean library](../../lean/README.md). The scope is described in [`lean/docs/004.md`](../../lean/docs/004.md), and the main statements are in the Comparator challenge [`StableColors.lean`](../../lean/ComparatorChallenges/StableColors.lean). Every listed theorem is proved without `sorry` and uses only the axioms `propext`, `Quot.sound` and `Classical.choice`. Complexity-theoretic conclusions (logspace, NC, P-completeness and the like) are not formalized.

**004h (stable colors).** The Frucht graph (LCF code above) is cubic and asymmetric; on its colored
incidence graph one refinement round keeps the two classes, while the only color-preserving
automorphism is the identity (Theorem 3.1). Rotations of $D^q$ are transitive on positions and have at
least $|D|^q/q$ orbits (Theorem 4.1, lower bound via Burnside's lemma; the exact necklace formula is
not formalized). The symmetric shell with an $A_5$ selector (existing by Maurer–Rhodes) is
$S_q$-equivariant and its response is constant $e$ or the identity according to $g$, so it decides a
compiled Boolean circuit (Theorem 5.1). Equivariance under transpositions along a connected graph
implies full $S_q$-equivariance (Theorem 6.4, connected case). Not formalized: Lemma 6.3 (vertex
permutations as certificates), the component version of Theorem 6.4, and the orbit-table and
swap-wreath compilers.

## Sources

Rewritten from the following internal notes (document numbers of the 27 October 2026 corpus review):
- #42, *Color Refinement Is Not Exchangeability* (`old_stuff/Color_Refinement_Is_Not_Exchangeability_20260822.pdf`),
  all of it: Theorem 1 (Frucht incidence barrier, p. 2), Theorem 2 (cyclic orbits, p. 3),
  Theorem 3 (hard-coefficient symmetric shell, pp. 3–4), Definitions 4–5 and Theorem 6 (swap
  forests, pp. 4–5), Section 5.1 (certificate checking), Theorem 7 and Corollary 8 (orbit tables,
  pp. 5–6), Theorem 10 (symbolic version, folded into a remark), Definition 11 and Theorem 12
  (swap-wreath compiler, p. 8), Section 9 (three obstructions, p. 7). Review: `C/reviews/r05.txt`
  (item 42).

## Status

- Proved in full: all included statements. As the review says, Theorems 3.1, 4.1 and 5.1 are
  folklore symmetry facts and Theorem 6.4 is the standard fact that transpositions along a connected
  graph generate the symmetric group; the paper presents them as stress tests, not as new results.
  The orbit-table and swap-wreath compilers are bookkeeping; their point is that the coefficient
  depth is charged explicitly.
- Made precise: the definition of a certified transposition (a label- and order-preserving vertex
  permutation fixing coefficient inputs and constants) and a proof that it yields equivariance
  (Lemma 6.3); the exact orbit count of the cyclic action (necklace formula); the existence of the
  A5 selector via Maurer–Rhodes 1965 (the source says "polynomial completeness" without a reference);
  the swap-wreath decomposition with explicit construction, application and leaf depths.
- Noted: the work exponent of the orbit table is (|E|−1) per bulk component, at least 59 for A5
  records, as the review points out.
- Checks: the Frucht graph (LCF code [−5,−2,−4,2,5,−2,2,5,−2,−5,4,2]) is cubic and asymmetric
  (exhaustive backtracking) and refinement of its incidence graph stops after one round with
  classes of sizes 12 and 18; the orbit bound for small d and q.
- Left out: Theorem 13 (height-or-certified-swap transfer to P ⊆ SP) and Conjecture 14, which are
  conditional restatements of the open problem and depend on the strict A5 transfer whose RAM-time
  version is not established (see 004g). The source's citation of Kiefer–McKay on the number of
  refinement rounds is not reproduced, since its bibliographic details could not be verified here.

Not refereed. No human referee has checked it yet; the proofs were developed with the assistance
of an AI system.

## Code

Checking scripts used for this manuscript are in [`verification/`](verification/): `frucht_strahler.py`. They are plain Python 3 with no dependencies outside the standard library unless the script says otherwise.
