# [A P-Complete Problem in Square-Root Space](paper.pdf)

**Author:** Generated Computers

**Date:** November 3, 2026

## Citation

```bibtex
@misc{GC:A-P-Complete-Problem-in-Square-Root-Space-November-3-2026,
  author = {{Generated Computers}},
  title = {{A P-Complete Problem in Square-Root Space}},
  howpublished = {Generated Computers preprint, manuscript 006c},
  year = {2026}
}
```



## Lean

Part of this paper is formalized in Lean 4 with Mathlib, in the [Lean library](../../lean/README.md). The scope is described in [`lean/docs/006.md`](../../lean/docs/006.md), and the main statements are in the Comparator challenge [`SquareRootSpace.lean`](../../lean/ComparatorChallenges/SquareRootSpace.lean). Every listed theorem is proved without `sorry` and uses only the axioms `propext`, `Quot.sound` and `Classical.choice`. Complexity-theoretic conclusions (logspace, NC, P-completeness and the like) are not formalized.

**006c (Square-root space).** Formalized: Theorem 6.1 in three parts. We construct the instance with reset set $\{1\}\cup S$. We prove that the reset sets of length-$n$ instances are exactly the subsets of $\{1,\dots,n\}$ containing $1$, and that there are $2^{n-1}$ of them. Also formalized: the counterexample of Section 4 to the source's embedding claim (no Sequential NOR graph has two vertices with the same two distinct in-neighbours), the subdivision embedding of Lemma 4.3, and the fan-out normalization of Theorem 5.1. For Theorem 5.1 the construction is written with explicit indices. We prove that it is a parent array of length $S_n+3n-1\le 3n^2+2n+1$ with the same output bit, in which every position is a parent at most twice. The lengths $4,12,23,37,54,74,97$ for $n\le7$ are checked. Not formalized: the time bound $O(n\log^3n)$ and the space bound $O(\sqrt n\log^2n)$ (Theorem 3.1, Corollary 3.3), Williams' simulation, the pebbling results (Lemma 4.2, Theorem 4.4), the easy floor, Corollaries 6.2 and 6.3, and Section 2.

## Sources

Rewritten from the following internal notes (document numbers of the 27 October 2026 corpus review):
- #25, "Nine Attacks on P ⊆ quasiNC" (`nine_attacks_quasiNC_with_addenda.pdf`):
  Addendum A (Lemma A.1, Theorems A.2-A.3), Addendum B (Proposition B.1 and the pebbling
  ceiling B.2), Addendum D (Theorem D.1, Theorem D.2 quoted, Corollary D.3), Addendum E
  (Theorem E.1, Corollaries E.2-E.3), Addendum H (Theorem H.1, Lemma H.3, Corollary H.4;
  Theorem H.6 only as a remark).
- #24, "seqnor (2): base note" (`seqnor (2).pdf`), Section 5, the remark on the
  square-root baseline.

## Status

- Proved in full, quoting Williams (STOC 2025), Paul, Tarjan and Celoni (1977) and
  Hopcroft, Paul and Valiant (1977): Sequential NOR runs in time O(n log^3 n) on a
  multitape machine and in space O(√n log^2 n) (Theorem 3.1, Corollary 3.3). Also proved:
  the easy floor; the pebbling ceiling of Ω(n/log n) for value-opaque algorithms; fan-out
  normalization to fan-out two; the surjectivity of reset sets and its two counting
  corollaries; and the standard consequences of P ⊆ PolyL.
- Corrections:
  - Theorem D.1 of the source (time O(n log^2 n)) assumed random access inside a block on
    a multitape machine. It is replaced by the recursive evaluation that Williams
    sketches for circuits, crediting Pippenger. This gives O(n log^3 n), so the space
    bound becomes O(√n log^2 n) instead of O(√n log^{3/2} n).
  - The pebbling argument of B.2 claimed that every in-degree-2 DAG is a subgraph of a
    Sequential NOR DAG on the same vertices. This is false (counterexample in Section 4).
    It is repaired by one subdivision per edge, at twice the length (Lemma 4.3), together
    with the fact that subdivision does not lower the pebbling number (Lemma 4.2).
  - Corollary E.3 used a count of n^2 + n arithmetic progressions in [1, n]. That count is
    too small (there are 330 for n = 16); with the correct bound 2n^3 the conclusion
    Ω(n/log n) is unchanged.
- Attribution: fan-out-two P-completeness of circuit value is known (Greenlaw, Hoover and
  Ruzzo); Theorem 5.1 is its Sequential NOR analogue. The pebbling barrier is classical
  (Cook 1974, Cook and Sethi 1976, Paul, Tarjan and Celoni 1977).
- Remarks only: the exact list reduction (Theorem H.6) and the compiler/normalization
  duality (Lemma H.3).
- Left out:
  - the nine attempts themselves (Sections 2-6);
  - the conditional transport-or-shatter compiler (Addendum C), whose completeness
    hypothesis is equivalent to the target;
  - the nondeterminism remarks (Addendum I), which are Savitch's theorem;
  - the numerical tables on random instances, now treated rigorously in manuscript 001a.
- Checks: the fan-out construction was checked on all parent arrays with n <= 7 and on 300
  random ones with 8 <= n <= 30. The surjectivity family was checked for all n <= 11.
- Not refereed.
