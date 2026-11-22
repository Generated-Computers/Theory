# [Homogeneous Sequential NOR Grids Lie in NC¹](paper.pdf)

**Author:** Generated Computers

**Date:** November 3, 2026

## Citation

```bibtex
@misc{GC:Homogeneous-Sequential-NOR-Grids-Lie-in-NC1-November-3-2026,
  author = {{Generated Computers}},
  title = {{Homogeneous Sequential NOR Grids Lie in $\mathrm{NC}^1$}},
  howpublished = {Generated Computers preprint, manuscript 009a},
  year = {2026}
}
```


## Lean

Part of this paper is formalized in Lean 4 with Mathlib, in the [Lean library](../../lean/README.md). The scope is described in [`lean/docs/009.md`](../../lean/docs/009.md), and the main statements are in the Comparator challenge [`HomogeneousNORGrids.lean`](../../lean/ComparatorChallenges/HomogeneousNORGrids.lean). Every listed theorem is proved without `sorry` and uses only the axioms `propext`, `Quot.sound` and `Classical.choice`. Complexity-theoretic conclusions (logspace, NC, P-completeness and the like) are not formalized.

**Homogeneous Sequential NOR grids lie in NC¹ (009a).** The NC¹ compiler (Theorem 4.6), the
threshold-reset composition theorem (Theorem 5.2), Corollary 5.3, the embedding into Sequential
NOR (Proposition 3.4), the affine-product normal form and the degree bounds of Section 6 are not
formalized; no circuit, depth or uniformity statement is formalized. Formalized are the exact grid
facts the compilers rest on: active rows output words without adjacent ones (Lemma 3.1), a reset
row computes `L_i ∧ ⋀_{t ≤ j}(N_t ⊕ β_{i,t})` and outputs a threshold word (Lemma 3.2), the
orientation example (Remark 3.3), and for homogeneous templates: zero columns are threshold resets
with the stated closed form (Lemma 4.1), diagonal collapse `X_{i,j} = X_{i-1,j-1}` in dense slabs,
its iteration and the consequence that every slab cell copies a cell of rows 1–2 or columns
`c, c+1` (Lemma 4.2), no vertical `000` (Lemma 4.3, also for `i = 2`), and the closure of the
transfer class `𝒢_H` under composition with `|𝒢_H| ≤ 80` for `H ≥ 3` (Lemma 4.5 and the count in
Lemma 4.4). The classification of transfers (Lemma 4.4(a)–(d)) is not formalized.

## Sources

Rewritten from the following internal notes (document numbers of the 27 October 2026 corpus review):
- #05 30-Page Most Important Results (`SEQNOR_30_PAGE_MOST_IMPORTANT_RESULTS_2026_09_07.pdf`),
  Chapter 5 (grid normal form, Lemmas 5.1–5.2, Theorem 5.3 "V169"), Section 6.3 (Theorem 6.6,
  Lemma 6.7, the fresh-control chain; "V153"), Section 7.5 (Theorem 7.4, "V194"); pp. 13–21.
- #08 Detailed Proof Compendium (`SEQNOR_DETAILED_PROOF_COMPENDIUM_2026_09_07.pdf`), native proof
  papers "V169" (pp. 877–882) and "V194" (pp. 895–900), which call themselves author theorem
  candidates.
- #05 Chapter 2 and #06 Theorem 3.1 for the four-coordinate NOR gadget used in Proposition 3.4
  (the full treatment is manuscript 006f).
- Check script: `verification/homogeneous_template_checks.py` (exhaustive check of Lemmas 4.1–4.4 for
  H ≤ 5, W ≤ 6, transfer classification for H ≤ 6, closure of the 80-map set for H ≤ 8).

## Status

- Proved in full: the homogeneous-template compiler in depth O(log H + log W) (Theorem 4.6) with
  all its lemmas (zero columns reset, diagonal collapse, no vertical 000, the 80 transfer types and
  their closure); the threshold-reset composition theorem (Theorem 5.2) for any active-run compiler;
  the corollary that grids whose maximal active runs are homogeneous are in FNC^2 (Corollary 5.3);
  the embedding of the grid into Sequential NOR (Proposition 3.4); the affine-product normal form,
  the affine-product criterion, the degree bound and the exact multiplicative complexity of the NOR
  chain (Section 6).
- Main caveat: the grid normal form embeds into Sequential NOR, but no document proves that it is
  P-hard (the corpus has only a bare assertion). The compilers therefore cover a class that is not
  known to contain hard instances (Remark 3.5).
- Changes relative to the source: the composition theorem is stated for an arbitrary active-run
  compiler; its application in the source to period-two active runs (V192) is left out, because
  that compiler rests on a large finite case analysis (a 400000(H+1)^2-machine cover) that is not
  reproduced in the corpus. The source's response-mass accounting is replaced by ordinary circuit
  size. The affine-product form is presented as the standard XOR–AND form, and the degree bound is
  attributed to Schnorr (via Boyar–Peralta–Pochuev). Self-scores and "accepted/verified" labels of
  the source are dropped.
- Left out: the query-private-pair density remark of #05 p. 18 (no theorem is claimed there).

Not refereed. No human referee has checked it yet; the proofs were developed with the assistance
of an AI system.
