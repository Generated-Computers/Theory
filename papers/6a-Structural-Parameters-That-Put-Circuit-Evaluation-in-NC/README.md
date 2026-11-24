# [Structural Parameters That Put Circuit Evaluation in NC](paper.pdf)

**Author:** Generated Computers

**Date:** November 24, 2026

## Citation

```bibtex
@misc{GC:paper-6a,
  author = {{Generated Computers}},
  title = {{Structural Parameters That Put Circuit Evaluation in NC}},
  howpublished = {Generated Computers, 2026},
  year = {2026}
}
```

## Abstract

Circuit evaluation is P-complete, also over the group $`A_5`$ and for the recurrence Sequential NOR, so polylogarithmic depth is not expected in general. We study structural parameters that bound the depth of exact parallel evaluation with polynomial work and put evaluation in NC when they are small. Three of them count marked nodes on a directed path. If $`H_{\mathrm{aff}}`$ is the largest number of non-affine gates on a path of a Boolean circuit with explicit truth tables, the complete trace is computed by logspace-uniform circuits of depth $`O(\log^2 L+(H_{\mathrm{aff}}+1)\log L)`$, with all regions and matrices extracted from the syntax. If $`H`$ is a catalyst cover of a circuit of unary maps and binary fusions, the depth is $`O((\mathrm{cht}(H)+1)\log^2 n)`$, where $`\mathrm{cht}(H)`$ is the largest number of cover nodes on a path, and the path-charging relaxation of the best height has integrality gap at most two, which is tight. If $`d(C)`$ is the largest number of reused nodes on a path of a straight-line program, the depth is $`O((d(C)+1)\log^2 n)`$. For the undirected wire graph, a feedback vertex set of size $`h`$ gives depth $`O((h+1)\log^2 s)`$, and one of size $`O(\mathrm{cp}(C)\log s)`$ is constructed, so every circuit is evaluated in depth $`O((\mathrm{cp}(C)+1)\log^3 s)`$, where $`\mathrm{cp}(C)`$ is the maximum number of vertex-disjoint cycles; for $`A_5`$ we classify the root equations of ready cycles exactly. For circuits of absorbing and exceptional gates, a polynomial bound on the number of union profiles at the canonical cuts of a balanced tree is recognized automatically and gives depth $`O(\log^2 N)`$.

For append-only machines that read their own history, we show that global table iteration computes the execution in $`O((A_N+2)\log N)`$ depth, where $`A_N`$ is the nesting depth of internal reads, and that executions whose internal live frontier is bounded by a constant are in NC; trajectories of a group action with $`K`$ sparse exceptions are computed in polylogarithmic depth with work polynomial in the number of steps and $`K`$. Most parameters come with an example on which they are large but evaluation is easy; none of them measures hardness. All theorems are proved in full; the statements that reduce a polynomial speedup for P to a bound on one of the parameters are conditional, and one conjecture and one problem on copy descriptors for $`A_5`$ are left open.

## Main results

Theorem numbers refer to [paper.pdf](paper.pdf). Table 1 of the paper compares all parameters.

- **Theorem A** (affine phases; Theorems 3.4, 3.6, 3.7, Corollary 3.8): complete trace of tagged circuits in logspace-uniform depth $`O(\log^2 L+(H_{\mathrm{aff}}+1)\log L)`$, hence $`\mathrm{FNC}^{\max\{2,c+1\}}`$ for $`H_{\mathrm{aff}}=O(\log^c L)`$. Proved in full.
- **Theorem B** (catalyst height; Theorems 4.6, 4.12, Corollary 4.14): depth $`O((\mathrm{cht}(H)+1)\log^2 n)`$ for a supplied catalyst cover; $`d^*\le\chi\le 2d^*`$, tight; NC-checkable certificate. Proved in full.
- **Theorem C** (fanout height; Theorem 5.3, Corollary 5.8): depth $`O((d(C)+1)\log^2 n)`$; for $`A_5`$ programs $`O((\Psi(C)+1)\log^2 n)`$. Proved in full. Copy-context normal form, exact rank 60 of copy tensors and the low-copy-debt compiler (Proposition 5.9, Proposition 5.11, Theorem 5.13): proved in full.
- **Theorem D** (disjoint cycles; Theorems 6.3, 6.6, Corollary 6.7): depth $`O((h+1)\log^2 s)`$ with a feedback set of size $`h`$; constructive feedback set of size $`\mathrm{cp}(C)(2\lceil\log_2 s\rceil+1)`$; depth $`O((\mathrm{cp}(C)+1)\log^3 s)`$. Proved in full. Stress family (Theorem 6.10): proved in full.
- **Theorem E** ($`A_5`$ root domains; Theorems 6.14, 6.15, 6.18): sizes $`\{0,3,4,5,60\}`$ and $`\{0,1,16\}`$; bulk contraction of disjoint ready cycles. Proved in full, and checked exhaustively by computer.
- **Theorem F** (union profiles; Theorem 7.8): the promise $`\nu_{\mathrm{cut}}\le (N+2)^C`$ is recognized and the trace computed in logspace-uniform depth $`O(\log^2 N)`$. Proved in full. Remark 7.13 lists statements of earlier notes that are **not proved** here and are not used.
- **Theorem G** (nested reads; Theorem 8.7, Lemma 8.8, Corollary 8.9): global table iteration, $`O((A_N+2)NS_N)`$ work and $`O((A_N+2)\log N)`$ depth. Proved in full. Copy program with linear rank and constant depth (Proposition 8.10): proved in full.
- **Theorem H** (constant frontier; Theorem 8.17, Corollary 8.18, Theorem 8.22, Proposition 8.23): compact-frontier epoch generator; constant-frontier executions in NC; minimal greedy epoch cover. Proved in full.
- **Theorem I** (moving frames; Theorem 9.6, Corollaries 9.8, 9.9): sparse-event compiler independent of the state-space size. Proved in full; Corollary 9.8 assumes block decompositions that we do not know how to produce.
- **Conditional / open**: the reductions to $`\mathrm{P}\subseteq\mathrm{SP}`$ or to polynomial speedups (Sections 4.5, 5.2, 8.4, 10.2) are conditional and their hypotheses are not claimed; Problem 10.1 and Conjecture 10.2 are open.

## Consolidated from

| Preprint | Sections of this paper |
|---|---|
| [Few Nonlinear Gates per Path Put Circuits in NC](../../preprints/Few-Nonlinear-Gates-per-Path-Put-Circuits-in-NC-November-3-2026/paper.pdf) | 1, 2.4, 3, 10.1, 10.4 |
| [Circuit Evaluation in Depth Governed by Catalyst Height](../../preprints/Circuit-Evaluation-in-Depth-Governed-by-Catalyst-Height-November-3-2026/paper.pdf) | 1, 4, 10 |
| [Fanout Height Bounds Parallel Evaluation Depth](../../preprints/Fanout-Height-Bounds-Parallel-Evaluation-Depth-November-3-2026/paper.pdf) | 1, 2.3, 5, 10.3, Appendix A |
| [Few Disjoint Cycles Give Sublinear-Depth Circuit Evaluation](../../preprints/Few-Disjoint-Cycles-Give-Sublinear-Depth-Circuit-Evaluation-November-3-2026/paper.pdf) | 1, 2.1, 2.2, 2.3, 6, 10 |
| [Few Union Profiles Put Circuit Evaluation in NC²](../../preprints/Few-Union-Profiles-Put-Circuit-Evaluation-in-NC2-November-3-2026/paper.pdf) | 1, 2.1, 7, 10 |
| [Parallel Simulation Where Only Nested Reads Cost Depth](../../preprints/Parallel-Simulation-Where-Only-Nested-Reads-Cost-Depth-November-3-2026/paper.pdf) | 1, 2.1, 8.1–8.4, 10 |
| [Constant-Frontier Computations Are in NC](../../preprints/Constant-Frontier-Computations-Are-in-NC-November-3-2026/paper.pdf) | 1, 2.1, 8.5–8.7, 9, 10 |

## Lean

Parts of the constituent results are formalized in Lean 4 with Mathlib in the [Lean library](../../lean/README.md); complexity-theoretic conclusions (NC, logspace uniformity, depth bounds) are not formalized in any of them.

- [`lean/docs/003.md`](../../lean/docs/003.md) (flow circuits; catalyst height, `CatalystHeightCompiler.lean`): covers, heights and fractional certificates; the factor-two rounding theorem with tightness; the "if" direction of the path-potential lemma; the combinatorial core of the catalyst-height compiler and joint composition; the accumulator and the two-register lower bound. PRAM depth bounds are not formalized.
- [`lean/docs/004.md`](../../lean/docs/004.md) ($`A_5`$ programs; few disjoint cycles, `FewDisjointCycles.lean`): the descriptor algebra, the cycle monodromy bijection and the full $`A_5`$ root-domain classification. The stress family, the feedback-set construction and the compilers are not formalized.
- [`lean/docs/005.md`](../../lean/docs/005.md) (portals; fanout height, `FanoutHeight.lean`): the round structure of the fanout-height compiler, the bound by $`|H|`$ on acyclic graphs, and the Sequential NOR proposition. Equality-assisted redirection and the tensor-network part are not formalized.
- [`lean/docs/007.md`](../../lean/docs/007.md) (structural compilers; union profiles, `FewUnionProfiles.lean`): absorbing elimination, the composition lemma of the union-profile compiler, correctness of the root run, the three union-closure bounds and the matching example. The circuit construction and depth bounds are not formalized.
- [`lean/docs/008.md`](../../lean/docs/008.md) (SC ladder family; affine phases, `FewNonlinearGates.lean`): the triangular product identity, the algebraic core of the region-matrix theorem, and the boundary lemma for the non-affine depth. Extraction, the ladder and the macro grammar are not formalized.
- [`lean/docs/010.md`](../../lean/docs/010.md) (tabulation; `GlobalTableIteration.lean`, `ConstantFrontier.lean`): the global table iteration theorem (without the hypothesis $`Z_0=C_0`$), the unique fixed point and stopping rule, and the copy program in full; for constant frontier, exactness of reachable nodes, the path–frontier equivalence, monotonicity, restartability, packing, minimality of the greedy cover, the moving-frame conjugation lemma, one link of the event chain and the cycle-plus-transposition formula. Graph-size bounds, Boolean matrix squaring and all depth bounds are not formalized.

## Notes on the merge

- **Structure.** The seven introductions were merged into one introduction with a comparison table (Table 1) and nine lettered main theorems. Shared material is defined once in Section 2: models of parallel computation and the PRAM primitives (P1)–(P3), circuits over a finite domain, the wire graph, cyclomatic excess, the Strahler rank, multiplication circuits and $`A_5`$ programs, and Sequential NOR. The two copies of the append-only machine definition (nested reads and constant frontier) were merged into Definition 8.1. Results are grouped by theme: path-height parameters (Sections 3–5), undirected cycles (Section 6), interface counting (Section 7), machines (Sections 8–9). In Section 6 the feedback-set compilers now precede the stress family.
- **Removed.** Repeated introductions, definitions of Sequential NOR (three copies), repeated model and cost conventions, organization paragraphs, the status footnotes of the preprints, and the separate "Computational checks" section of the fanout preprint (now Appendix A). The fanout preprint's open-problems section moved to Section 10.3, together with a short collection of limits (10.1), conditional statements (10.2) and open questions (10.4), each pointing to the place where the original text keeps it.
- **Errors fixed.** (1) In the nested-reads preprint, the sentence "The map $`\wr`$ is injective" used the LaTeX wreath-product symbol `\wr` instead of the write-address map `\wri`; corrected (Section 8.1). (2) A displayed formula in the proof of Theorem 8.7 was broken out of an overfull line; no content change.
- **Computer checks.** The disjoint-cycles preprint reported the feedback-set check on 600 random graphs with at most 10 vertices; the script as distributed tests 400 random multigraphs with 3 to 11 vertices, and Appendix A now describes what the script does. The final brute-force step of `graphchecks.py` was not rerun to completion (see `verification/README.md`).
- **Cross-group citations** (no results were moved inline; the cited results are either black boxes of several pages or are already restated where needed): group 3 (Newton-type correction, related work); group 4 (strict transfer for $`A_5`$, Strahler rank and the Strahler-rank compiler, the portal-chain and pair-fusion compilers, ranked equality saturation, opening $`A_5`$ cycles, the hypergraph charging argument); group 5 (P-completeness of Sequential NOR, binary-core normal form); group 6b (fanout-kernel compiler and fanout-collision deficit, transfer tables, the control-trace transfer statement); group 7a (dual of the catalyst relaxation and matched rails, interface-counting compilers, the lower bound for invariant linear features of the cycle and transposition, barriers); group 7b (escape switching, output-conditioned instances, low-excess compiler). The matched-rail example and the escape-switching procedure were already restated in full in the constituents and stay so.
- **Status labels.** Remark 7.13 (statements of earlier notes without proof) keeps its label; Problem 10.1 and Conjecture 10.2 remain open problems; the catalyst "corridor-or-catalyst" transfer is still discussed but not stated as a theorem (Section 4.5); all conditional consequences say so in the text.
- **Title.** Kept as the group title. The PRAM results are stated as "in NC" in the usual sense that an explicit algorithm with polynomial work and polylogarithmic depth gives NC circuits (Section 2.1).
