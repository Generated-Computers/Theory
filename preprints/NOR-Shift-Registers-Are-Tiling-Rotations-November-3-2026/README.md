# [NOR Shift Registers Are Tiling Rotations](paper.pdf)

**Author:** Generated Computers

**Date:** November 3, 2026

## Citation

```bibtex
@misc{GC:NOR-Shift-Registers-Are-Tiling-Rotations-November-3-2026,
  author = {{Generated Computers}},
  title = {{NOR Shift Registers Are Tiling Rotations}},
  howpublished = {Generated Computers preprint, manuscript 010b},
  year = {2026}
}
```


## Lean

Part of this paper is formalized in Lean 4 with Mathlib, in the [Lean library](../../lean/README.md). The scope is described in [`lean/docs/010.md`](../../lean/docs/010.md), and the main statements are in the Comparator challenge [`NORTilingRotation.lean`](../../lean/ComparatorChallenges/NORTilingRotation.lean). Every listed theorem is proved without `sorry` and uses only the axioms `propext`, `Quot.sound` and `Classical.choice`. Complexity-theoretic conclusions (logspace, NC, P-completeness and the like) are not formalized.

**NOR shift registers (010b).** The tiling-rotation theorem is formalized in full. This covers Lemma 2.2 (uniform-lag sequences are wavefronts), Lemma 3.2 (unique cyclic extension, `π` injective on tilings), Lemma 3.3 (two-sweep landing in the cyclic `10`/`100` tilings), Theorem 3.4 (`F_D(π w) = π(ρ w)` and `F_D^{D+1}(F_D^2 x) = F_D^2 x`) and Corollary 3.5 (`x_i = w_{(i+3) mod (D+1)}` for `i ≥ 2D`). Periodicity `x_{i+D+1} = x_i` is proved from `i ≥ 2D − 1` on, one index earlier than the paper states. Also proved are the complement-conjugation Lemma 4.1, the collapse Lemma 4.2 for `P`, `Q`, `A` and `F³ = F²` for all six collapsing rules, and Lemma 5.1 (non-affine iff `NOR(u⊕a, v⊕b)⊕c`, with a unique triple). The polarity-gauge conjugacy Theorem 5.3 is proved for uniform-lag grids in reading order: the gauged slab is a homogeneous `H`-wavefront. So is the optimality part of Proposition 5.6 (the greedy gauge cover is minimal). The prefix-scan Lemma 2.3, the linear-work/log-depth compilers (Corollaries 3.6, 5.4, Theorems 4.3, 5.5), the affine case of Theorem 4.3, the computation of `e_H(a)` and the P-completeness remark are not formalized.

## Sources

Rewritten from the following internal notes (document numbers of the 27 October 2026 corpus review):
- #26, Closest Results Toward P ⊆ SP — full proofs (`Closest_Results_Toward_P_in_SP_Full_Proofs_20260820.pdf`),
  Appendix D: Lemmas D.1–D.2, Theorem D.3, Corollary D.4, Lemma D.5, Theorem D.6 (PDF pp. 58–61),
  and the polarity-gauge results Lemma D.7, Definition D.8, Theorem D.9, Corollary D.10,
  Theorem D.11, Proposition D.12 (PDF pp. 62–64).

## Status

- Proved in full: two-sweep landing in the cyclic tilings by 10 and 100, the tiling-rotation
  theorem (preperiod ≤ 2, period dividing D+1), the linear-work O(log)-depth NOR compiler, the
  classification of all sixteen homogeneous rules, unique NOR polarity of the eight non-affine
  gates, polarity-gauge conjugacy, the gauge-cover compiler and the minimality of the greedy cover.
- Changes: the notes assume D ≥ 3; the proofs here cover all D ≥ 1 (D = 1 by direct computation,
  the landing proof works for D ≥ 2). Added the sequence form: x_{i+D+1} = x_i for all i ≥ 2D,
  for arbitrary first D values (a direct consequence of the rotation theorem). The P-completeness of
  Sequential NOR is justified by an explicit four-step simulation of a NOR gate. The optimality
  argument of Proposition D.12 is written out (monotonicity of the reach function).
- Scope: the results concern homogeneous and gauge-consistent grids only; no bound on the number of
  gauge pieces of a general instance is claimed.
- Checks: exhaustive for all rows of width D ≤ 14 (rotation, landing, orbit structure, collapse of
  the six rules) and D ≤ 12 (periodicity of the lag sequence); polarity lemma by enumeration.
- Prior work: the recurrence is a two-tap feedback shift register (Golomb 1967); we found no
  reference for the tiling description, but it may be known (literature search pending).

Not refereed. No human referee has checked it yet; the proofs were developed with the assistance
of an AI system.

## Code

Checking scripts used for this manuscript are in [`verification/`](verification/): `lag_sequence.py`, `wavefront.py`. They are plain Python 3 with no dependencies outside the standard library unless the script says otherwise.
