# [Batching First Failures Cannot Beat One Prefix](paper.pdf)

**Author:** Generated Computers

**Date:** November 3, 2026

## Citation

```bibtex
@misc{GC:Batching-First-Failures-Cannot-Beat-One-Prefix-November-3-2026,
  author = {{Generated Computers}},
  title = {{Batching First Failures Cannot Beat One Prefix}},
  howpublished = {Generated Computers preprint, manuscript 005g},
  year = {2026}
}
```



## Lean

Part of this paper is formalized in Lean 4 with Mathlib, in the [Lean library](../../lean/README.md). The scope is described in [`lean/docs/005.md`](../../lean/docs/005.md), and the main statements are in the Comparator challenge [`BatchingFirstFailures.lean`](../../lean/ComparatorChallenges/BatchingFirstFailures.lean). Every listed theorem is proved without `sorry` and uses only the axioms `propext`, `Quot.sound` and `Classical.choice`. Complexity-theoretic conclusions (logspace, NC, P-completeness and the like) are not formalized.

**005g (Batching first failures).** Local machines are formalized as step functions whose value at step `t` depends only on earlier configurations. The first-failure validator lemma is proved: the least local-check failure is the first-failure boundary, and the recomputed successor there is exact. The same-anchor batch collapse is proved as a set identity: the steps certified by a family of candidates equal those certified by the candidate with the largest first-failure boundary. The black-box two-round barrier is proved: no one-round algorithm with fewer than `|Y|` non-adaptive queries computes `R(L(x))` for all oracles. The round count of the low-junction transducer is the generic round lemma of 005e, applied with the junctions as `H`. Not formalized: the depth and work bounds, the parametric cut composition, and the conditional corollaries.

## Sources

Rewritten from the following internal notes (document numbers of the 27 October 2026 corpus review):
- #31 First-Failure Batching, Exact Anchor Barrier (`old_stuff/First_Failure_Batching_Exact_Anchor_Barrier_20260820.pdf`), all of it: Definition 1, Theorem 2, Corollaries 3-4, Proposition 5, Theorem 6, Definition 7, Theorem 8, Corollary 9, Definition 10, Theorem 11, Corollary 12, Conjecture 13, Theorem 14, Section 7 (pp. 1-7).

## Status

Proved in full: the first-failure validator lemma (implicit in the source), same-anchor batch collapse and its corollaries, the black-box two-round barrier, parametric cut composition, and the low-junction transducer (with an explicit depth bound). All results are elementary. The low-junction transducer is a special case of the semantic Strahler compiler of manuscript 004g. The source's Proposition 5 (interaction-identity instability) is an informal observation and is presented as a remark. The statements about the conjectured cut combiner, including the source's Theorem 14, are conditional implications and are presented as such; nothing is claimed about P in SP. Not refereed.
