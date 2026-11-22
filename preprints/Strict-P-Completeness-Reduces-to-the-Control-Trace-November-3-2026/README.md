# [Strict P-Completeness Reduces to the Control Trace](paper.pdf)

**Author:** Generated Computers

**Date:** November 3, 2026

## Citation

```bibtex
@misc{GC:Strict-P-Completeness-Reduces-to-the-Control-Trace-November-3-2026,
  author = {{Generated Computers}},
  title = {{Strict P-Completeness Reduces to the Control Trace}},
  howpublished = {Generated Computers preprint, manuscript 010d},
  year = {2026}
}
```


## Lean

Part of this paper is formalized in Lean 4 with Mathlib, in the [Lean library](../../lean/README.md). The scope is described in [`lean/docs/010.md`](../../lean/docs/010.md), and the main statements are in the Comparator challenge [`ControlTrace.lean`](../../lean/ComparatorChallenges/ControlTrace.lean). Every listed theorem is proved without `sorry` and uses only the axioms `propext`, `Quot.sound` and `Classical.choice`. Complexity-theoretic conclusions (logspace, NC, P-completeness and the like) are not formalized.

**Control trace (010d).** Normalized register–stack machines are formalized as append-only machines. Registers are indexed by an arbitrary finite type with designated registers `x_0, x_1, x_2, x_3`, and the row-0-zero condition is not needed. Proposition 2.4 (control-trace sufficiency) is proved: `q_t` is the prefix composition of `δ(·, b_t)`, and acceptance depends only on the control trace. Theorem 3.1 (triangularization) is proved: given the address–control trace, the register values satisfy `y = L y + d`, with `L` and `d` built from the trace and the known numbers, and `L` strictly lower triangular in time. Lemma 3.2 (nilpotent doubling) is proved in any ring. Theorem 3.3 (payload reconstruction) is proved as the identity `y = S_R d`, valid for every `R` with `N ≤ 2^R`. Fact 4.1 (Reinhardt), Theorem 4.2 (the conditional transfer), Proposition 5.3 (MCP/USIARV), the `O(1)`-nonzeros-per-row count, the PRAM costs and the integer bit bound are not formalized.

## Sources

Rewritten from the following internal notes (document numbers of the 27 October 2026 corpus review):
- #26, Closest Results Toward P ⊆ SP — full proofs (`Closest_Results_Toward_P_in_SP_Full_Proofs_20260820.pdf`),
  Appendix A: Definitions A.1–A.2, Proposition A.3, Theorem A.5, Lemma A.6, Theorem A.7 with the
  exact-integer qualification, Theorem A.8, Definitions A.9 and A.12, Theorems A.10 and A.13,
  Remark A.11 (PDF pp. 34–39); Theorem 1.1 (PDF p. 10).

## Status

- Proved in full (machine model only): control-trace sufficiency, trace triangularization and
  payload reconstruction by nilpotent doubling, with an explicit O(M+β) bit bound over the integers
  (the notes give the weaker O(M(b + log M))).
- Conditional: the trace-revelation transfer (Theorem A.8) and the equivalence of MCP and USIARV
  (Theorem A.13) depend on Reinhardt's strict-sequential framework, stated here as a black-box Fact
  in the form the notes use it. We did not re-derive it from Reinhardt (1997). In particular the
  reduction USIARV ≤ MCP rests on Reinhardt's simulation of a fixed machine by linear-size MCP
  circuits and is unchecked, as is the normalization of Reinhardt's machines into the form used here
  (Theorem A.10 in the notes).
- The AP and EP versions of the transfer are described in a remark only, because their
  qualifications (termination prediction, log-cost model) could not be checked.
- This is a reformulation of the open problem, presented as such: USIARV is the problem decided by
  the fixed evaluator, and no progress on P ⊆ SP is claimed.

Not refereed. No human referee has checked it yet; the proofs were developed with the assistance
of an AI system.
