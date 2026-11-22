# [Every Hypergraph Is an A₅ Proof-Support System](paper.pdf)

**Author:** Generated Computers

**Date:** November 3, 2026

## Citation

```bibtex
@misc{GC:Every-Hypergraph-Is-an-A5-Proof-Support-System-November-3-2026,
  author = {{Generated Computers}},
  title = {{Every Hypergraph Is an $A_5$ Proof-Support System}},
  howpublished = {Generated Computers preprint, manuscript 005b},
  year = {2026}
}
```



## Lean

Part of this paper is formalized in Lean 4 with Mathlib, in the [Lean library](../../lean/README.md). The scope is described in [`lean/docs/005.md`](../../lean/docs/005.md), and the main statements are in the Comparator challenge [`HypergraphA5.lean`](../../lean/ComparatorChallenges/HypergraphA5.lean). Every listed theorem is proved without `sorry` and uses only the axioms `propext`, `Quot.sound` and `Classical.choice`. Complexity-theoretic conclusions (logspace, NC, P-completeness and the like) are not formalized.

**005b (Every hypergraph is an A5 proof-support system).** Collision blocks, essential support and edge products are defined for an arbitrary group. The 61-probe selector lemma is proved for `A₅`, together with its analogue with `|G| + 1` probes for every finite group. The explicit selector uses only the identity and constant maps, so each probe is visibly a group term. The realization theorem is proved for every selector and every nontrivial group. Each block has exactly one colliding pair, that pair determines the edge product `a_e`, and the essential support of the block's collision function is exactly the edge `e`. Part (i) of the star-transversal barrier is also proved: as one anchor varies, the colliding pair takes `|G|` (that is, 60) distinct values. The charging lemma is proved over the reals, including both the phase count and the depth bound `λ n^{1-ε}/(1-ε)`. The following are not formalized: the size count of the construction, the support-redundancy proposition, parts (ii) and (iii) of the star barrier, the surplus transfer, and all complexity statements. Terms are represented by the functions they induce.

## Sources

Rewritten from the following internal notes (document numbers of the 27 October 2026 corpus review):
- #39 Proof-Support Hitting Sets Do Not Lift (`old_stuff/Proof_Support_Hitting_Sets_Do_Not_Lift_20260821.pdf`), all of it: Theorem 1, Theorem 3, Corollary 4, Theorem 5, Definitions 6-7, Theorem 8, Corollary 9, Definition 10, Theorem 11, Theorem 13, Proposition 14, Conjecture 15 (pp. 1-9).
- #37: the 61-probe selector and ranked saturation come from Equality Saturation Is Predicate-Complete (`old_stuff/Equality_Saturation_Predicate_Completeness_and_Surplus_Law_20260821.pdf`), cited through companion manuscript 004a.

## Status

Proved in full: support-overlap redundancy, the hypergraph realization theorem, the star-transversal barrier, logarithmic ancestor-cut compilation, the liftable-cut compiler, a charging lemma and an abstract surplus transfer. The source's qualified-cut surplus transfer is reduced to the abstract transfer; its portal branch (logarithmic ancestor cuts that remove hard mass) needs a generalized program model with table modules and is only sketched. The source's Proposition 14 is an informal meta-statement and is presented as a remark. Class-level consequences are mentioned only as conditionals through the strict A5 transfer of manuscript 004g; nothing is claimed about P in SP.

Checks: the selector, the essential-support claim and the star barrier were verified by brute force over A5 (with the selector terms replaced by the functions they induce). The brute-force scripts used for the checks are not part of this repository. Not refereed.

## Code

Checking scripts used for this manuscript are in [`verification/`](verification/): `a5_checks.py`, `a5lib.py`. They are plain Python 3 with no dependencies outside the standard library unless the script says otherwise.
