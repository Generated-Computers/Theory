# [A Reset Normal Form for a P-Complete Problem](paper.pdf)

**Author:** Generated Computers

**Date:** November 3, 2026

## Citation

```bibtex
@misc{GC:A-Reset-Normal-Form-for-a-P-Complete-Problem-November-3-2026,
  author = {{Generated Computers}},
  title = {{A Reset Normal Form for a P-Complete Problem}},
  howpublished = {Generated Computers preprint, manuscript 006b},
  year = {2026}
}
```



## Lean

Part of this paper is formalized in Lean 4 with Mathlib, in the [Lean library](../../lean/README.md). The scope is described in [`lean/docs/006.md`](../../lean/docs/006.md), and the main statements are in the Comparator challenge [`ResetNormalForm.lean`](../../lean/ComparatorChallenges/ResetNormalForm.lean). Every listed theorem is proved without `sorry` and uses only the axioms `propext`, `Quot.sound` and `Classical.choice`. Complexity-theoretic conclusions (logspace, NC, P-completeness and the like) are not formalized.

**006b (Reset normal form).** Reset sets are represented by their indicator on positive positions, with the virtual reset $-1$ built into $\mathrm{pred}_R$. Formalized: the reset-predecessor normal form (Theorem 3.1), the event-queue form (Proposition 3.2), and the fact that $R^\star$ is a fixed point of the reset operator $\Phi$ and its unique one (Proposition 3.3, mathematical part). Also formalized: the first-disagreement lemma (Lemma 3.4), $R_t=R^\star$ for all $t\ge n$ (Corollary 3.5), the non-monotonicity example for $\Phi^2$ (Remark 3.6(b), checked by `decide` on the stated instance), and realizable traces (Theorem 3.7, the construction only, not the Fibonacci count). Not formalized: Borodin's theorem and Corollary 2.3, the $\mathrm{NC}^1$ circuit bounds of Proposition 3.3, the compilers of Section 4, the barriers of Section 5, and the computed (unproved) round count of Remark 3.6(a).

## Sources

Rewritten from the following internal notes (document numbers of the 27 October 2026 corpus review):
- #21, "Toward P ⊆ quasiNC (dossier)" (`P_in_quasiNC_research_dossier.pdf`), Theorem 1.3,
  Corollary 1.4, Section 2.2 and Sections 16-17 (Theorems 16.1-16.4, Proposition 16.2,
  Lemma 17.1, Theorems 17.2-17.5 and 17.7, Corollary 17.6).
- #25, "Nine Attacks on P ⊆ quasiNC" (`nine_attacks_quasiNC_with_addenda.pdf`), Section 5.1
  (reset fixed point, first disagreement, non-monotonicity of Φ²), Lemma H.5, Theorem H.6
  (as a remark only) and Section 15.4 (slow iteration example).

## Status

- Proved in full: quasiNC = PolyL under polylog-space uniformity (Theorem 2.2). This is
  Borodin's 1977 theorem scaled up; the source labelled it "Derived". Also proved in full:
  the reset-predecessor and event-queue normal forms, the reset operator (unique fixed
  point, NC^1 evaluation, first-disagreement lemma), the active-one and live-error
  compilers, the baseline-portfolio corollary, one-checkpoint amplification, and the
  last-use barrier.
- Corrections: the source states size O(n log n) for one application of the reset
  operator. The selection step needs O(n^2 log n), still polynomial with depth O(log n).
  The slow-iteration family j_i = max(0, i-2) needs ⌈n/3⌉ rounds from {-1}. This is
  computed for n <= 300, not proved; the source's ⌊n/3⌋+2 counts one more round.
- Presented as remarks only, being restatements of the target: live-error completeness
  (#21 Theorem 17.4) and the exact list reduction (#25 Theorem H.6).
- Left out: the survey and programme sections of #21 (Sections 3-15 and 18-26).
- Checks: the normal forms, the fixed-point uniqueness, the first-disagreement lemma and
  the Φ² example were checked exhaustively for all parent arrays with n <= 8. For n <= 7
  the check covered all candidate sets, on a sample of arrays.
- Not refereed.
