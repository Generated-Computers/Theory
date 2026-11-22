# [Exact Cut Contraction for P-Complete Sequential Circuits](paper.pdf)

**Author:** Generated Computers

**Date:** November 3, 2026

## Citation

```bibtex
@misc{GC:Exact-Cut-Contraction-for-P-Complete-Sequential-Circuits-November-3-2026,
  author = {{Generated Computers}},
  title = {{Exact Cut Contraction for P-Complete Sequential Circuits}},
  howpublished = {Generated Computers preprint, manuscript 011b},
  year = {2026}
}
```

## Lean

Part of this paper is formalized in Lean 4 with Mathlib, in the [Lean library](../../lean/README.md). The scope is described in [`lean/docs/011.md`](../../lean/docs/011.md), and the main statements are in the Comparator challenge [`ExactCutContraction.lean`](../../lean/ComparatorChallenges/ExactCutContraction.lean). Every listed theorem is proved without `sorry` and uses only the axioms `propext`, `Quot.sound` and `Classical.choice`. Complexity-theoretic conclusions (logspace, NC, P-completeness and the like) are not formalized.

**Exact cut contraction (011b).** Binary-table sequential circuits (Definition 2.2) are formalized with values defined by recursion. Theorem 4.1 (exact cut externalization) is formalized in full as a correctness statement. For a cut `b` and given prefix values `x_0, …, x_b`, the explicitly constructed contracted circuit `C/b` (one gate per internal gate, parents `π'_r = ρ(π_{h_r})`, tables `G'_r(u,v) = G_{h_r}(Φ_{h_r-1}(u), Φ_{π_{h_r}}(v))`) has a valid shape on `q(b)` gates, and its values satisfy `y_r = x_{h_r}`. The suffix values are recovered as `x_i = Φ_i(y_{ρ(i)})` for every `i ∈ [b,n]`, so they are determined by the contracted instance. Also formalized: the enumeration of internal gates and `q(b) = |{i > b : π_i > b}|`; the crossing-area identity and its averaging consequence (Lemma 5.2); and the padding counterexample (Proposition 5.3), the finite statement that refutes the source's claim that quadratic total edge span gives an efficient parallel regime. The latter says that `C'` followed by `m` gates reading `x_0` has total span at least `n²/4`, a top cut with `q = 0` and `(b/n)^γ + (q/n)^γ = 2^{-γ} < 1`, and `C'` as its prefix. Its Sequential NOR version is included. Proposition 3.1 (Sequential NOR equals the lexicographically-first greedy maximal independent set, stated as the unique solution of the greedy recursion) and Lemma 3.3 (jump rule) are also formalized. Not formalized: all costs (the `O(n)`-work, `O(log n)`-depth construction, the `O(1)`-depth recovery), the cut-norm recursion (Theorem 5.1) and Corollary 5.4, which are statements about work and depth, and Section 6 (register stack machines, linear algebraic circuits, elimination rounds, Conjecture 6.7). No statement about P, EP or NC is formalized.

## Sources

Rewritten from the following internal notes (document numbers of the 27 October 2026 corpus review):
- #01, From Stable Semisort to P vs EP
  (`Semisort/From_Stable_Semisort_to_P_vs_EP_Research_Dossier (1).pdf`). Used: Section 1.2 and
  Chapters 6–8 (background on KRS classes and Reinhardt's register stack machine, condensed to one
  section); Chapter 9 (Lemmas 9.1, 9.2); Chapter 10 (Theorems 10.1, 10.2, Section 10.4);
  Chapter 15 (Theorems 15.1, 15.2, Definition 15.3, Theorem 15.4); Chapter 18 (Conjecture 18.3,
  Section 18.4). PDF pages 8, 18–23, 25–28, 36–37, 42–43.
- #04, QuasiNC Consolidated Results
  (`SEQNOR_main/Sequential_NOR_QuasiNC_Consolidated_Results_2026-09-07.pdf`), Appendix A.1,
  Theorem A.1 (p. 29): the greedy-MIS representation.

## Status

- Proved in full: Sequential NOR = lexicographically-first greedy MIS (Proposition 3.1; source
  9.1 and #04 A.1), the jump rule (Lemma 3.3; source 9.2), exact cut externalization with
  reconstruction (Theorem 4.1; source 10.1), the cut-norm recursion (Theorem 5.1; source 10.2),
  the crossing-area identity (Lemma 5.2; source 10.4), trace-resolved RSM computations as linear
  algebraic circuits (Theorem 6.3) and the equivalence of indexed and general fan-in-two LACs
  (Proposition 6.2) (together source 15.1), elimination rounds and controlled fill (Lemma 6.5,
  Corollary 6.6; source 15.2–15.4, whose proof was only an idea). Proposition 6.4 (LACs are in NC
  with polynomial work) is a standard fact, included because the source and the review rely on it.
- Stated as a conjecture: work-efficient sublinear-depth evaluation of indexed LACs
  (Conjecture 6.7; source 18.3). The route of source 18.4 is described in Remark 6.8 without any
  claim; its "trace compression" premise is not formulated.
- Corrected: source §10.4 claims that quadratic total edge span gives an EP regime. This is false
  as an inference (Proposition 5.3: any circuit followed by gates reading x_0 has span ≥ n²/4 and
  a perfect top cut, but an unrestricted prefix). The paper proves the corrected hereditary
  version (Corollary 5.4). Theorem 5.1 states explicitly that the cut condition must hold on every
  prefix and residual in the recursion and that cuts must be computable; the source's statement
  left this implicit. Theorem 4.1's cost is O(log n) depth (source), with reconstruction in O(1)
  depth given the residual's values.
- Attribution: lexicographically-first MIS is P-complete by Cook (1985); the identity of
  Proposition 3.1 is presented as an observation, not as a new hardness result. Cut
  externalization is presented as partial evaluation. The RSM is Reinhardt's (1997); his
  completeness theorems are mentioned but not restated.
- Left out: the survey material of #01 (Chapters 1–8 apart from the background section; the
  summary of the semisort note in Chapters 2–4, which is manuscript 011a), and the results of
  Chapters 11–14 and 16 (two-scale blocking, MCP stage monoid, trace certification, frontier
  scans, microblock tabulation), which are not part of this manuscript.
- Checks: `verification/check_seqnor.py` (exhaustive for n ≤ 8; cut externalization on 46,391
  circuit–cut pairs; crossing-area identity; the counterexample's numbers) and
  `verification/check_lac.py` (LAC-to-indexed conversion, trace-to-LAC over Z on random RSM programs,
  the nilpotent-inverse identity, elimination rounds). Run with `python3 verification/<name>.py`.
- Nothing here bears on P versus EP. Not refereed.
