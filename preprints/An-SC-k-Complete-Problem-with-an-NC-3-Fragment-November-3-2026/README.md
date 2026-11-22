# [An SCᵏ-Complete Problem with an NC³ Fragment](paper.pdf)

**Author:** Generated Computers

**Date:** November 3, 2026

## Citation

```bibtex
@misc{GC:An-SC-k-Complete-Problem-with-an-NC-3-Fragment-November-3-2026,
  author = {{Generated Computers}},
  title = {{An $\mathrm{SC}^k$-Complete Problem with an $\mathrm{NC}^3$ Fragment}},
  howpublished = {Generated Computers preprint, manuscript 008a},
  year = {2026}
}
```



## Lean

Part of this paper is formalized in Lean 4 with Mathlib, in the [Lean library](../../lean/README.md). The scope is described in [`lean/docs/008.md`](../../lean/docs/008.md), and the main statements are in the Comparator challenges [`SCkCompleteSPAI.lean`](../../lean/ComparatorChallenges/SCkCompleteSPAI.lean), [`LogFeedbackBlock.lean`](../../lean/ComparatorChallenges/LogFeedbackBlock.lean). Every listed theorem is proved without `sorry` and uses only the axioms `propext`, `Quot.sound` and `Classical.choice`. Complexity-theoretic conclusions (logspace, NC, P-completeness and the like) are not formalized.

**008a (An SCᵏ-complete problem with an NC³ fragment).** Formalized: the correctness of the configuration encoding behind the hardness half of Theorem `thm:complete` (a machine that reads, writes and moves on a bit tape is simulated step by step by a time-invariant SPAI instance; its matrices are diagonal and differ from the identity in at most one diagonal entry); exactness of the transcript leaves (Lemma `lem:leaf`, shared with 008d); the feedback-free case of Proposition `prop:feedbackfree` (the block acts as `x ↦ (q, Mx + c)` with `q, M, c` independent of the data); pair exactness (Lemma `lem:pairs`); exact syndrome recompression (Theorem `thm:recompress`): if every pair-guard row lies in the row space of a full-row-rank `B_u`, then the `2^{ρ_u}` syndrome leaves are exact; and the invariant-observation-space reduction of Proposition `prop:invariant`. Not formalized: the Turing-machine normal form, padding and logspace computability of the reduction, the membership half, Corollary `cor:equiv`, the canonical hierarchy `LR` with its NC³ bound (Theorem `thm:lr`), all depth and uniformity statements, and the examples.

## Sources

Rewritten from the following internal notes (document numbers of the 27 October 2026 corpus review):
- Sequential NOR to SC: Complete Research Compendium (`SEQNOR_main/Sequential_NOR_to_SC_Full_Research_Compendium_Draft.pdf`, document #03), Component 10 (PDF pp. 269–276; component identifier C10): definition of SPAI_2, Theorems 3.1–3.2 and Corollary 3.3 (completeness), Proposition 4.1 (quasipolynomial baseline), Theorem 5.1 (feedback-free iteration).
- Same document, Component 12 (PDF pp. 285–294; results SC-LR-1 to SC-LR-5): Theorem 1.1 (parameterized SPAI_k), Lemma 2.2, Definition 3.1, Theorem 4.1 (recompression), Definition 5.1 and Theorem 5.2 (LR-SPAI in NC^3), Corollary 5.3, Proposition 6.1 (invariant observation space), Section 7 (examples).

## Status

- Proved in full: SC^k-completeness of SPAI_k (stage-dependent and time-invariant, hardness already with diagonal matrices), the feedback-free NC^2 theorem, the transcript-leaf lemma, exact syndrome recompression, the NC^3 theorem for the total language LR-SPAI_{k;c0,c1} with trajectory reconstruction, the invariant-observation-space NC^2 proposition, and both examples.
- The completeness proof, which the source gave as a sketch, is written out (padding and machine normal form included). As the reviewers noted, it is the standard configuration encoding: the hard instances are diagonal, so the affine structure is not used. It is presented as a normal form, not as a new result. The reformulation "SC^k ⊆ NC^j iff SPAI_k ∈ NC^j" (j ≥ 2) is stated as a restatement of an open problem.
- Corrected or clarified: the canonical blocks, tree and uniformity across block counts are made explicit; canonical bases are RREF, which removes the right-inverse step.
- Not claimed: the reviewers suggest the depth can likely be reduced to NC^2; this is mentioned as an open remark only. The source's finite audits were not re-run; instead the leaf and merge constructions were checked against direct simulation on 150 random small instances (no violation).
- Not refereed.

## Code

Checking scripts used for this manuscript are in [`verification/`](verification/): `lr_check.py`. They are plain Python 3 with no dependencies outside the standard library unless the script says otherwise.
