# [Three NC Compilers for Sequential NOR Grids](paper.pdf)

**Author:** Generated Computers

**Date:** November 3, 2026

## Citation

```bibtex
@misc{GC:Three-NC-Compilers-for-Sequential-NOR-Grids-November-3-2026,
  author = {{Generated Computers}},
  title = {{Three NC Compilers for Sequential NOR Grids}},
  howpublished = {Generated Computers preprint, manuscript 009b},
  year = {2026}
}
```


## Lean

Part of this paper is formalized in Lean 4 with Mathlib, in the [Lean library](../../lean/README.md). The scope is described in [`lean/docs/009.md`](../../lean/docs/009.md), and the main statements are in the Comparator challenge [`ThreeNCGridCompilers.lean`](../../lean/ComparatorChallenges/ThreeNCGridCompilers.lean). Every listed theorem is proved without `sorry` and uses only the axioms `propext`, `Quot.sound` and `Classical.choice`. Complexity-theoretic conclusions (logspace, NC, P-completeness and the like) are not formalized.

**Three NC compilers for Sequential NOR grids (009b).** The three compilers (Theorems 3.4, 4.7,
5.3) and the anchor-image computation are not formalized. Formalized are: the bounds
`1 ≤ Γ ≤ min(H, W + 1)` (Lemma 3.1); Example 3.5(b) in its corrected form `Γ = min(H, W + 1)` for
alternating rows; the row facts that `(0^W, 0)` is the identity on Fibonacci words and
`(0^{W-1}1, 0)` an involution (the two injective rows of Proposition 4.5; the "only these two"
direction is not formalized), and that the pair `(1010⋯, 0)`, `(1^W, 1)` maps every Fibonacci
word to `0101⋯` (Example 5.4); the INDEX gadget (its last value is `y_t`) and Proposition 6.1(a)
and (c): a one-pass evaluator has at least `2^m` states after the payload, a context-independent
associative summary (semigroup or monoid) has at least `2^m` elements, and for `d × d` matrices
over a finite semiring `K` with `|K| ≥ 2`, `2^m ≤ |K|^{d²}` and `d ≥ √(m / log₂|K|)` (the bound
as corrected in the paper). Proposition 6.1(b) (randomized, Fano), Lemmas 4.1–4.2 (greedy
normalization, `T³ = T`), Proposition 4.3, Theorem 4.4, Proposition 4.6, the common-core
compiler, Lemma 5.1, Proposition 6.2 and Proposition 6.3 are not formalized.

## Sources

Rewritten from the following internal notes (document numbers of the 27 October 2026 corpus review):
- #05 30-Page Most Important Results (`SEQNOR_30_PAGE_MOST_IMPORTANT_RESULTS_2026_09_07.pdf`),
  Sections 7.7–7.11 (Lemma 7.5, Theorems 7.6, 7.7, 7.10, Lemmas 7.8–7.9; "V201", "V203", "V204",
  "V206") and Sections 9.1–9.3 (Theorems 9.1–9.2, the equality quotient), pp. 21–25, 28–29.
- #08 Detailed Proof Compendium (`SEQNOR_DETAILED_PROOF_COMPENDIUM_2026_09_07.pdf`), native proof
  papers "V203" (pp. 920–925), "V204" (pp. 926–930) and "V206" (pp. 936–945).
- #16 Best Post-Corpus Results (`BEST_POST_CORPUS_SEQNOR_RESULTS_2026-09-02.pdf`), Section 7
  (UFR-1–UFR-7 and UFR-10 barriers), pp. 10–11.
- Check scripts: `verification/fibonacci_row_checks.py` (T^3 = T, the stability criterion and count, the
  rank recurrence and its minimum, injective rows, the atom factorization, for W ≤ 10; the
  constant two-row block for W ≤ 12) and `verification/gamma_index_checks.py` (INDEX gadget for m ≤ 5,
  Γ of alternating rows, Γ ≤ min(H, W+1)).

## Status

- Proved in full: the row-partition (Γ) compiler, depth O(log^2 M + Q log M) when Γ ≤ Q, and
  O(log M) for bounded Γ (Theorem 3.4), with the arbitrary-α extension; the Fibonacci-carrier
  algebra (greedy normalization, T^3 = T, the rank recurrence and ρ(B) ≥ 2^{⌈W/2⌉}, the stable-row
  criterion with count 2F_{W+1} + 4F_W, the injective rows, the atom factorization); the
  common-core compiler in FNC^2 and the high image of its row blocks; the anchor–collar theorem
  (Theorem 5.3) including the computation of anchor images by truncated word lists; the barriers
  (INDEX, full transformation monoid, equality quotient).
- Main caveat: the grid normal form is not known to be P-hard, so the compilers cover a class not
  known to contain hard instances.
- Changes relative to the source: (1) The anchor–collar theorem is stated with a greedy anchor
  rule and only short gaps. The source selects anchors through an earlier rule (V200/V201) and
  allows long period-two gaps through a period-two compiler (V192); both rest on finite case
  analyses that are not reproduced in the corpus, so they are left out. With short gaps only, the
  proof gives depth O(log^2 M + L log M), i.e. FNC^k for every fixed k ≥ 2 (the source states
  k ≥ 3 because of the period-two branch). (2) The source's claim that alternating constant rows
  have Γ = H is corrected to Γ = min(H, W+1). (3) The matrix-summary bound d ≥ m / log|K| of #05
  Theorem 9.1 is corrected to d ≥ sqrt(m / log|K|) (as #16 states; the counting gives only the
  square root). (4) The SeqNOR realization of the transformation-monoid generators, asserted in the
  source without proof, is replaced by a truth-table construction of O(m^2 2^m) coordinates.
  (5) The source's dense-payload example needs identity shields because of its selection rule; the
  greedy rule does not.
- The barriers are folklore (Kremer–Nisan–Ron; Howie) and are not circuit lower bounds.
  Self-scores ("6.6/10" etc.) and "accepted/verified" labels are dropped.

Not refereed. No human referee has checked it yet; the proofs were developed with the assistance
of an AI system.
