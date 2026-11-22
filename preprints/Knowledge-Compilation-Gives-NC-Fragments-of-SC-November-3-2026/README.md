# [Knowledge Compilation Gives NC Fragments of SC](paper.pdf)

**Author:** Generated Computers

**Date:** November 3, 2026

## Citation

```bibtex
@misc{GC:Knowledge-Compilation-Gives-NC-Fragments-of-SC-November-3-2026,
  author = {{Generated Computers}},
  title = {{Knowledge Compilation Gives NC Fragments of SC}},
  howpublished = {Generated Computers preprint, manuscript 008b},
  year = {2026}
}
```



## Lean

Part of this paper is formalized in Lean 4 with Mathlib, in the [Lean library](../../lean/README.md). The scope is described in [`lean/docs/008.md`](../../lean/docs/008.md), and the main statements are in the Comparator challenge [`KnowledgeCompilationLadder.lean`](../../lean/ComparatorChallenges/KnowledgeCompilationLadder.lean). Every listed theorem is proved without `sorry` and uses only the axioms `propext`, `Quot.sound` and `Classical.choice`. Complexity-theoretic conclusions (logspace, NC, P-completeness and the like) are not formalized.

**008b (Knowledge compilation gives NC fragments of SC).** Formalized: leaf pullback and leaf conjunction of affine atoms (Lemmas `lem:leafpull`, `lem:leafand`), including singular maps, with the rank bound `rank(BM) ≤ rank B`; conjunction of decomposable nodes and preservation of determinism (Lemma `lem:vtops`); the transfer-pullback identity with pairwise disjoint terms (Lemma `lem:transfer`); the equality barrier (Proposition `prop:pfeq`: an accepting piece row inside the diagonal forces full column rank, and covering the diagonal of `𝔽₂ⁿ × 𝔽₂ⁿ` needs `2ⁿ` rectangles); the residual-state core of the ordered-equality barrier (Proposition `prop:ordeq`); the one-rectangle bound `|A||B| ≤ 2^{n-1}` for inner product (Lemma `lem:rect`); the count `(2ⁿ-1)2^{n-1}` of pairs with `a·b = 1`; and the inner-product barrier (Proposition `prop:vtip`: at least `2ⁿ-1` rectangles). Not formalized: the generic hierarchy theorem and the six class theorems (PF, Path, VT, AVP, SepTR, RF-TW) with their depth bounds, the canonical cap-checked algorithms, the selected-row-parity and other gain families, the separator construction and the `K_{n,n}` barrier, and the treewidth claims.

## Sources

Rewritten from the following internal notes (document numbers of the 27 October 2026 corpus review):
- Sequential NOR to SC: Complete Research Compendium (`SEQNOR_main/Sequential_NOR_to_SC_Full_Research_Compendium_Draft.pdf`, document #03), Components 13–18 (PDF pp. 295–341; results SC-FOR-1–4, SC-PATH-1–5, SC-VT-1–5, SC-AVP-1–5, SC-ST-1–6, SC-RF-1–4): the piecewise two-bank, path-message, fixed-vtree, vtree-portfolio, separator-transfer and rank-factor compilers with their witnesses and barriers.
- Same document, synthesis p. 9 and Component 14, Lemma 1.1 (p. 307), for the two-bank question.

## Status

- Proved in full: a generic cap-checked hierarchy theorem; exactness of every pullback, conjunction, projection and merge operation; the six class theorems (PF, VT, AVP, SepTR in uniform NC^3; Path in NC^{k+1}; RF-TW in NC^2); the selected-row-parity separation of PF from the low-rank compiler; the bank-match gain and ordered-equality barrier for Path; the equality, inner-product (one-rectangle) and component-containment barriers; the K_{n,n} separator barrier.
- Sketched: that the canonical cap-checked algorithms stay within their caps on the VT, AVP, SepTR and RF-TW gain witnesses (the source relied on finite runs), and the treewidth claims for the broadcast and triangular RF examples. Small representations are proved to exist in each case.
- Corrected: the source states on p. 9 that the two-bank theorem strictly extends the one-basis language, and in Component 14 (Lemma 1.1) that a two-bank factorization gives no asymptotic enlargement. Both are partly right: the direct-sum identity shows the split itself adds nothing (a two-bank piece is a one-bank piece of rank r1+r2), while per-piece bases do give a strict gain over one basis per entering state (selected-row parity, proved here). The paper states this resolution. The approved-macro probe-interaction generator is described abstractly, and the AVP theorem is stated for any NC^2 candidate generator; the RF execution network is specified concretely (only syntactically possible probe blocks get selector variables).
- Not claimed: trajectory reconstruction for PF/Path/VT/SepTR; any coverage of general SPAI_k. All witness computations are easy by other means (reviewers' remark), so these are representation separations only.
- Not refereed.
