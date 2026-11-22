# [Four Barriers to Speeding Up Circuit Evaluation](paper.pdf)

**Author:** Generated Computers

**Date:** November 3, 2026

## Citation

```bibtex
@misc{GC:Four-Barriers-to-Speeding-Up-Circuit-Evaluation-November-3-2026,
  author = {{Generated Computers}},
  title = {{Four Barriers to Speeding Up Circuit Evaluation}},
  howpublished = {Generated Computers preprint, manuscript 010e},
  year = {2026}
}
```


## Lean

Part of this paper is formalized in Lean 4 with Mathlib, in the [Lean library](../../lean/README.md). The scope is described in [`lean/docs/010.md`](../../lean/docs/010.md), and the main statements are in the Comparator challenge [`FourBarriers.lean`](../../lean/ComparatorChallenges/FourBarriers.lean). Every listed theorem is proved without `sorry` and uses only the axioms `propext`, `Quot.sound` and `Classical.choice`. Complexity-theoretic conclusions (logspace, NC, P-completeness and the like) are not formalized.

**Four barriers (010e).** Lean proves the extensional-summary barrier (Proposition 5.1). For the feature-dimension barrier it proves Lemma 4.2 (`c` and `τ` generate `S_m`), Theorem 4.4 (an invariant subspace containing a nonconstant function has dimension `≥ m − 1`) and Theorem 4.3 in both the linear (`r ≥ m − 1`) and affine (`r ≥ m − 2`) forms, over every field and every `m ≥ 2`. For the fixed-lag copy barrier, synchronous correction with radius `L` (Definition 2.1) is formalized for general machines. Theorem 2.2(a) is proved: the candidate value at relative stage `t` is `1` iff `t ≤ (r+1)d`, so the block is exact after `r` rounds iff `m ≤ (r+1)d`, which is `χ_L = ⌈m/d⌉ − 1`. Theorem 2.2(b) is proved as the lower bound `Σ_j ⌈m_j/d⌉ ≥ ⌈N/d⌉` over every partition, attained by blocks of length `d`; the minimum over `(B, σ)` is not written as a Lean definition. For the identity-padding barrier, affine–product circuits over `𝔽₂`, the multiplicative Strahler rank and exact Newton iteration are formalized. Proved are Lemma 3.1 (`z·z = z`), the ladder's values and ranks, and Theorem 3.2 in full (exact Newton delay: `z_k` is exact exactly from step `ρ(z_k) + 1 = k + 1` on). Proposition 2.3 (residue formula for the copy program) is the 010a statement `copy_real`. The padding construction (Theorem 3.3, Corollary 3.4), the block-matrix compiler (Proposition 4.1), Corollary 4.5, and the four-Russians Theorem 5.2 and Corollary 5.3 are not formalized.

## Sources

Rewritten from the following internal notes (document numbers of the 27 October 2026 corpus review):
- #26, Closest Results Toward P ⊆ SP — full proofs (`Closest_Results_Toward_P_in_SP_Full_Proofs_20260820.pdf`):
  Appendix P, Lemma P.1, Theorems P.2–P.3, Corollary P.4, Proposition P.5 (PDF pp. 137–139);
  Appendix S, Lemma S.1, Theorem S.2, Theorem S.4, Corollary S.5, Corollary S.8, Proposition S.9
  (PDF pp. 158–162), with the definitions of Q.2–Q.4 and Q.8 (PDF pp. 143–147); Appendix V,
  Definition V.1, Theorem V.2, Lemma V.7, Theorems V.8–V.9, Corollary V.10 (PDF pp. 177–182);
  Appendix U, Theorem U.4, Corollary U.5, Remark U.6, Lemma U.7, Corollary U.8 (PDF pp. 173–175);
  barrier summaries §§8.2–8.6 (PDF pp. 27–28).
- #28, Closest Results Toward P ⊆ SP — summary (`Closest_Results_Toward_P_in_SP_20260820.pdf`),
  §6.3 (PDF p. 19).

## Status

- Proved in full; all statements are elementary.
- Fixed-lag copy: the notes use a "correction rank" defined in a note that is not in the corpus.
  It is defined here from its use (synchronous correction with radius L), and P.1–P.3 are proved
  for that definition, with the exact value ⌈N/d⌉ for the multiscale rank.
- Identity padding: stated for affine–product circuits with the multiplicative Strahler rank; the
  extension to compact multiplex circuits with the Taylor rank is a remark (the appended gates obey
  the same rank recurrence). Explicit constants for the padding parameters (m ≥ 2^10).
- Feature dimension: V.8–V.9 are attributed to the classical structure of the permutation module of
  the symmetric group (Sagan 2001 for characteristic zero); the proofs here work over every field.
- Four-Russians: attributed to Arlazarov, Dinic, Kronrod and Faradzev (1970). Corrected relative to
  #28 §6.3: the speedup holds for explicit bounded fan-in circuits on a PRAM only, does not apply to
  compact multiplex (MCP) circuits (as #26 Remark U.6 already says), and for block length
  log N/log log N its work is N^{1+Θ(1/log log N)}, not O(N); the O(N)-work claim is not proved.
- Left out: the saturation-rank equivalence (U.2, in manuscript 002b), the functional-forest and
  junction compilers (P.6–P.10) and the certified-congruence quotient theorem (S.7), apart from a
  remark.
- Checks: Newton delay on ladders of length ≤ 11, padding rank/frontier on circuits with up to 8
  ladders, the correction rank of the copy program for radii ≤ 4 and N < 40 over all block
  partitions.

Not refereed. No human referee has checked it yet; the proofs were developed with the assistance
of an AI system.

## Code

Checking scripts used for this manuscript are in [`verification/`](verification/): `copy_program.py`, `correction_rank.py`, `padding.py`. They are plain Python 3 with no dependencies outside the standard library unless the script says otherwise.
