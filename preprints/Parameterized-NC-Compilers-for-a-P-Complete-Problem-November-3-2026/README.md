# [Parameterized NC Compilers for a P-Complete Problem](paper.pdf)

**Author:** Generated Computers

**Date:** November 3, 2026

## Citation

```bibtex
@misc{GC:Parameterized-NC-Compilers-for-a-P-Complete-Problem-November-3-2026,
  author = {{Generated Computers}},
  title = {{Parameterized NC Compilers for a P-Complete Problem}},
  howpublished = {Generated Computers preprint, manuscript 007a},
  year = {2026}
}
```


## Lean

Part of this paper is formalized in Lean 4 with Mathlib, in the [Lean library](../../lean/README.md). The scope is described in [`lean/docs/007.md`](../../lean/docs/007.md), and the main statements are in the Comparator challenge [`ParameterizedNCCompilers.lean`](../../lean/ComparatorChallenges/ParameterizedNCCompilers.lean). Every listed theorem is proved without `sorry` and uses only the axioms `propext`, `Quot.sound` and `Classical.choice`. Complexity-theoretic conclusions (logspace, NC, P-completeness and the like) are not formalized.

*Parameterized NC compilers (007a).* For a Sequential NOR parent array and a horizon `n`, the formalization proves that the true reset mask is the unique fixed point of the map `Φ_j` (Lemma 3.2), and the greedy phase-repair theorem (Theorem 3.6): if the error of a proposal has `k` switches on `1, …, n`, then after normalizing the first bit, `k` rounds of `T_j` give the true mask and no earlier round does. For a normalized binary core it proves that the interaction cover `C(j)` meets every binary record (Lemma 4.5, for the paper's side rule and for every other side rule), that relative to the cover values every record outside the cover is a unary map of one earlier non-cover variable or of the virtual root, determined by cover values below the gate (Lemma 4.5), and the corrected residual evaluator of Theorem 4.6: every residual value `y_k(X)` equals the ordered ancestry product `h_{k,m} ∘ ⋯ ∘ h_{k,1}` applied to `1`. It also checks the counterexample of Remark 4.7: on the two-stage chain, `y₂ = ¬c₁ ∧ ¬c₂` is not a constant or a signed copy of a single variable. The binary-core compression, the block-lifting lemma, the circuit size and depth bounds, and all other compilers of the paper (core depth, formula cores, sharing, interface tables, treewidth, repair, live intervals, elimination orders) are not formalized. The paper proves the second clause of Lemma 4.5 ("depends on at most one value in `C(j)`") as stated, but it fails when both sources of a gate outside the cover lie in the cover. The Lean statement says "cover values below `k`" instead, which agrees with the "at most two values" used in the proof of Theorem 4.6.

## Sources

Rewritten from the following internal notes (document numbers of the 27 October 2026 corpus review):
- #18 Sequential NOR Structural Parallelization Compendium (`Sequential_NOR_Structural_Parallelization_Compendium.pdf`), 28 August 2026: Lemma 2.1, Proposition 2.2, Section 6 (Lemma 6.1, Corollary 6.2, Theorem 6.3, Proposition 6.4, Corollary 6.5), Theorems 9.1, 10.2, 11.3, Lemma 14.1, Theorems 14.2, 15.1, 15.2, Theorems 17.4 and 18.1/18.3 (as tools), Sections 19-29, Examples 30.4-30.5, the correction ledger of Section 32 and the problems of Section 34 (pp. 6-7, 11-12, 14-35).
- #06 SEQNOR flagship finished theorems (`SEQNOR_FLAGSHIP_FINISHED_THEOREMS_2026_09_07.pdf`), Section 4 (p. 4): the corrected proof of the interaction-cover compiler.

## Status

- **Correction found by the Lean formalization (3 November 2026):** Lemma 4.5 claimed that the unary map of a record outside $`C(j)`$ depends on at most one value in $`C(j)`$. This is false when both sources of a gate outside $`C(j)`$ lie in $`C(j)`$. Example: $`z_1, z_2`$ constant, $`z_3 = \mathrm{NOR}(z_1, z_2)`$, $`z_4 = \mathrm{NOR}(z_2, z_1)`$; the tie rule gives $`C(j) = \{1, 2\}`$, and $`z_3`$ depends on both. The lemma now says "at most two values". The proof of Theorem 4.6 uses only this weaker form, so the theorem is unchanged.
All results are conditional (promise) compilers for Sequential NOR; none places the unrestricted
problem in NC. Proved in full: greedy phase repair (exactly k rounds for k switches) and its
corollaries; the core-depth, formula-core, interaction-cover, sharing-count, sharing-depth and
sharing-frontier compilers; the interface-table recurrence and its formula expansion; the
balanced-interval compiler; the relevant-core treewidth compiler (NC^2) and the full-core one
(logspace); the cotree feedback-cover compilers; exact dynamic programs for the canonical and
adaptive interface repair numbers and the adaptive repair compiler; the live-interval optimizer,
fixed-frontier compiler, one-step factor-three comparisons, min-cost flow formulation and
O(log^3 n) deterministic optimizer, farthest-right greedy multicover, its batched version, and the
unit-deficit property of core intervals; occurrence certificates; the order-defect modulator,
fill computation and compiler. Imported modules are stated as Facts with citations: Boolean
formula value in NC^1 (Buss), the logspace theorems of Elberfeld-Jakoby-Tantau, logspace in NC^2
(Borodin), and balanced tree decompositions (Bodlaender; Bodlaender-Hagerup).

Corrected relative to the source: (1) the source proof of the interaction-cover compiler claims
that the residual compresses to signed copies of single cover variables; this is false (a chain
y_r = y_0 AND NOT c_1 ... AND NOT c_r is a counterexample, already noted in #06) and is replaced
by per-stage chain products over a precomputed ancestry matrix; (2) per-block formula evaluation
in O(log n) depth is justified by building formula strings once (Euler tour) and using Buss's
evaluator; (3) where the source invokes Jansen-Sarma balancing to construct formulas in NC^2, the
formulas are built directly from a balanced decomposition, and the depth D_bal of the imported
balancing step is kept explicit; an unconditional bound one logarithmic factor weaker is also
given (modulator and order-defect compilers); (4) Theorems 23.2 and 23.4, only sketched in the
source, are proved by an explicit dynamic program; (5) the residual of the fixed-q cotree
parameter has primal treewidth at most q+2 (the source's q+1 refers to the dependency graph);
(6) shortest-path extraction in the flow optimizer uses a cost perturbation to avoid zero cycles.
The randomized RNC^2 optimizer via Lingas-Persson is recorded only as a remark, because its
hypotheses were not checked. Left out: the three-round paired-forest theorem (Section 3), material
covered by companion manuscripts (binary-core compression, block compiler, list completion and
universality: 006f; segment cuts: 007b), the general macro systems of Section 17, Theorems
18.4-18.6, the list-completion variants of Sections 16 and 18, and the portfolios of Sections
30-31. Regression checks (not proofs): phase repair on 20,000 random instances with n <= 12; the
corrected cover evaluator, the unit-deficit property and greedy optimality on random small
instances. Not refereed.
