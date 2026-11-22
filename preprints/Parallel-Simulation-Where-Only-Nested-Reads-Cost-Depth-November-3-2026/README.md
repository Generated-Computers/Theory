# [Parallel Simulation Where Only Nested Reads Cost Depth](paper.pdf)

**Author:** Generated Computers

**Date:** November 3, 2026

## Citation

```bibtex
@misc{GC:Parallel-Simulation-Where-Only-Nested-Reads-Cost-Depth-November-3-2026,
  author = {{Generated Computers}},
  title = {{Parallel Simulation Where Only Nested Reads Cost Depth}},
  howpublished = {Generated Computers preprint, manuscript 010a},
  year = {2026}
}
```


## Lean

Part of this paper is formalized in Lean 4 with Mathlib, in the [Lean library](../../lean/README.md). The scope is described in [`lean/docs/010.md`](../../lean/docs/010.md), and the main statements are in the Comparator challenge [`GlobalTableIteration.lean`](../../lean/ComparatorChallenges/GlobalTableIteration.lean). Every listed theorem is proved without `sorry` and uses only the axioms `propext`, `Quot.sound` and `Classical.choice`. Complexity-theoretic conclusions (logspace, NC, P-completeness and the like) are not formalized.

**Parallel simulation (010a).** The global table operator `ℋ` is formalized, together with its prefix-composition form (`ℋ(Z)_t = (F_t ∘ ⋯ ∘ F_1)(C_0)`) and the read-adaptivity rank. The main theorem (Theorem 4.2) is proved in full: for every candidate transcript and every `r`, every stage of rank `≤ r` is exact after `r + 1` applications. Lean drops the hypothesis `Z_0 = C_0`, which is not needed. Also proved are the unique fixed point (Lemma 4.3, with a horizon) and the correctness of the stopping rule (Corollary 4.4). For the copy program, Proposition 5.1 is proved in full: `a(t) = ⌊(t−1)/d⌋`, the iterate from the all-zero candidate is exact on `[0, N]` iff `N ≤ r d`, the first exact round is `A_N + 1`, and `C*_t = (t, H_in[(t−1) mod d])`. The costs of Lemma 3.2 and Corollary 4.4, the doubling remark and the conditional consequence for `P ⊆ SP` are not formalized.

## Sources

Rewritten from the following internal notes (document numbers of the 27 October 2026 corpus review):
- #26, Closest Results Toward P ⊆ SP — full proofs (`Closest_Results_Toward_P_in_SP_Full_Proofs_20260820.pdf`),
  Appendix O (Lemma O.1, Theorem O.2, Corollary O.3, Sections O.4–O.5; PDF pp. 133–136), with the
  machine conventions of Appendix N.2 (PDF p. 126).

## Status

- Proved in full: the cost of one application of the global table operator (O(N·S_N) work,
  O(log N) depth on a CREW PRAM), the main theorem (after r+1 applications every stage of
  read-adaptivity rank ≤ r is exact), and the copy example (A_N = ⌊(N−1)/d⌋, exactly A_N+1
  rounds from the all-zero candidate, constant-depth direct evaluation).
- Added routine steps: the real execution is the unique fixed point of the operator, which gives a
  stopping rule (at most A_N+2 applications) without knowing A_N; an overflow configuration keeps
  tables on hypothetical configurations inside the universe (the notes leave this implicit); the
  PRAM model is stated explicitly (the notes' O(log N · polyloglog N) depth is the bit-level form).
- Conditional only: a sublinear bound on A_N for Reinhardt's evaluator would give P ⊆ SP via
  manuscript 010d. This is stated as a reduction of one open problem to another; no bound on A_N
  is proved, and the copy example shows none follows from the append-only structure.
- The doubling remark (exact tables on d independent configurations have S_N^d entries) is an
  observation about exact tables, not a lower bound.
- Checks: simulation on 3,000 random small machines and on copy programs of lag 2–6.

Not refereed. No human referee has checked it yet; the proofs were developed with the assistance
of an AI system.

## Code

Checking scripts used for this manuscript are in [`verification/`](verification/): `copy_program.py`, `table_iteration.py`. They are plain Python 3 with no dependencies outside the standard library unless the script says otherwise.
