# [Circuit Evaluation by Flows and Linear Programs](paper.pdf)

**Author:** Generated Computers

**Date:** November 24, 2026

## Citation

```bibtex
@misc{GC:paper-7b,
  author = {{Generated Computers}},
  title = {{Circuit Evaluation by Flows and Linear Programs}},
  howpublished = {Generated Computers, 2026},
  year = {2026}
}
```

## Abstract

Maximum flow and linear programming are P-complete because circuits can be written as flows and linear programs, and their parallel algorithms are governed by the size of the numbers involved. We study which numbers a flow or LP encoding of circuit evaluation really needs. The reduction of Goldschlager, Shaw and Staples gives the $`i`$-th gate capacity $`2^i`$; these numbers both enforce the truth tables and let one true gate supply several uses. After a complementation by gate type every gate of an alternating monotone circuit is a NAND gate, whose graph has the convex hull $`z+x\ge1`$, $`z+y\ge1`$, $`z+x+y\le2`$; splitting every use into its own occurrence gives a linear program of linear size with coefficients in $`\{-1,0,1\}`$, bounds and right-hand sides in $`\{0,1,2\}`$, and the circuit transcript as unique optimum. Equivalently, the circuit is a disjoint union of two-vertex networks with capacities and supplies at most two, coupled only by disjoint equal-flow sets. This coupling cannot be removed locally: boundary functions of min-cost-flow networks are M-convex, so no network of any size or data passes two binary channels through while charging $`|x-y|`$, unless some crossed or broken channel state costs no more than the cheapest intended one, and no network is an all-equal sensor on $`r\ge2`$ channels; dually, no submodular (graph-cut) energy has the NAND relation as its projected minimizers. For the classical circuit LP of Dobkin, Lipton and Reiss, the Fibonacci OR ladder has a point with output $`\tfrac12`$ violating no constraint by more than $`\delta=1/(2(F_{n+1}-1))=\Theta(\varphi^{-n})`$, and a minor of absolute value $`F_{n-1}`$, so standard interior-point guarantees need linear precision even there.

We also record, conditionally and labelled as such, what a flow reduction would need for a randomized parallel speedup. Under the hypothesis that min-cost flow is solvable with high probability in depth $`\tilde O(\sqrt N\,L)`$, an NC reduction to networks with $`N\le S^\alpha`$ vertices and bit length $`L\le S^\lambda`$ gives depth $`S^{\alpha/2+\lambda}`$ up to polylogarithmic factors, which beats the trivial evaluator only if $`\alpha/2+\lambda<1`$; the classical reduction gives $`S^{3/2}`$. A reduction from a P-complete problem with polynomial size and logarithmic bit length would give P ⊆ RNC, and with polylogarithmic bit length it would do so under a second stated hypothesis; optimal flows are verifiable in NC, so such algorithms become zero-error; random costs cannot replace the fanout role of large capacities. Two further exact tools are included: Latin contraction and a low-excess compiler for multiplication circuits over a finite group, and simultaneous escape switching, which decides a monotone circuit in at most $`r+1`$ reachability rounds from a rank-biased start, $`r`$ the Strahler rank. No reduction with the parameters needed for a speedup is known, and no class inclusion is claimed.

## Main results

- **Theorem 3.1** (NAND normalization of alternating circuits) — proved in full.
- **Theorem 3.2** (NAND polytope) and **Lemma 3.3** (forcing) — proved in full.
- **Theorem 3.5** (dyadic elimination: residual NAND program with coefficients in $`\{-1,0,1\}`$, bounds and right-hand sides in $`\{0,1,2\}`$, unique optimum = transcript) — proved in full; a refinement of the Dobkin–Lipton–Reiss encoding, not a new hardness result.
- **Theorem 3.7** (two-vertex gate networks with capacities and supplies at most two, coupled by disjoint equal-flow sets) — proved in full.
- **Proposition 3.8** (cut-size bound for local capacity replacement) — proved in full.
- **Theorem 4.1** (boundary exchange: boundary functions of networks are M-convex) — proved in full; Murota's network induction, with an elementary proof.
- **Theorem 4.4** (no read-only comparator) and **Corollary 4.5** (no all-equal sensor, $`r\ge2`$) — proved in full, under the explicit context-independence condition (ii) of Definition 4.3; **Remark 4.7** (crossbar) shows the condition cannot be dropped.
- **Corollary 4.9** (no local ordinary-flow bridge for the equal-flow sets) — proved in full.
- **Theorem 4.11** (no submodular / graph-cut NAND gadget) — proved in full; a direct consequence of the lattice of submodular minimizers.
- **Theorem 5.1** (circuit LP, Dobkin–Lipton–Reiss), **Theorem 5.2** (Fibonacci precision, $`n\ge2`$), **Theorem 5.3** (Fibonacci subdeterminant, with Hadamard upper bound) — proved in full; an explicit instance of a known phenomenon, not a lower bound for every LP algorithm.
- **Theorem 6.5** (randomized flow transfer) and **Corollary 6.6** — **conditional** on Assumption 6.3 (square-root-depth min-cost-flow solver).
- **Proposition 6.8** (calibration against the trivial evaluator) — proved in full (statements about the depth bound of Assumption 6.3).
- **Theorem 6.9** (RNC transfer) — proved in full for logarithmic bit length; the polylogarithmic case is **conditional** on Assumption 6.4.
- **Theorem 6.10** (NC verification of optimal flows) — proved in full, standard; **Corollary 6.11** (Las Vegas conversion) — proved in full; its ZP-SP consequence is conditional on Assumption 6.3.
- **Proposition 6.12** (random costs do not clone flow) — proved in full.
- **Theorem 7.3** (Latin-component contraction) and **Theorem 7.5** (low-excess compiler) — proved in full.
- **Theorem 7.8** (simultaneous escape switching), **Lemma 7.10** (rank layers by reachability), **Theorem 7.11** (rank-biased escape bound $`r+1`$) — proved in full; the bound matches, and does not improve, Strahler-rank evaluators of other papers of the collection.

## Consolidated from

| Preprint | Sections of this paper |
| --- | --- |
| [P-Complete Equal-Flow Programs with Capacities at Most Two](../../preprints/P-Complete-Equal-Flow-Programs-with-Capacities-at-Most-Two-November-3-2026/paper.pdf) | 1, 2.1–2.2, 3, 4.2 (end: the remaining coupling), 8.1 |
| [Min-Cost Flow Has No Read-Only Comparator](../../preprints/Min-Cost-Flow-Has-No-Read-Only-Comparator-November-3-2026/paper.pdf) | 1, 2.3, 4, 8.1 |
| [Circuit LPs Need Linear Precision](../../preprints/Circuit-LPs-Need-Linear-Precision-November-3-2026/paper.pdf) | 1, 2.4, 5, 7 |
| [What Flow Reductions Need for RNC Speedups](../../preprints/What-Flow-Reductions-Need-for-RNC-Speedups-November-3-2026/paper.pdf) | 1, 2.2–2.4, 6, 8.2 |

## Lean

All four constituents belong to family 003, [flow circuits](../../lean/docs/003.md) (Comparator challenges `EqualFlowCapacityTwo.lean`, `MinCostFlowNoComparator.lean`, `CircuitLPPrecision.lean`, `FlowReductionsRNC.lean`). Formalized: NAND normalization, the NAND polytope, forcing, items (iv)–(v) of the dyadic elimination theorem and its hard-equality form, and the cut-size bound (Section 3); the boundary exchange theorem, no all-equal sensor / no read-only comparator, the crossbar, the one-shot comparator and the no-submodular-NAND theorem (Section 4); the uniqueness of the circuit-LP solution, the Fibonacci point and the ladder minors (Section 5); and simultaneous escape switching (items (i), (ii), (iv), (v)) and the rank-biased bound (Section 7). For Section 6 only the exact facts behind the conditional statements are formalized (cost-independent conservation, the geometric expectation, the exponent arithmetic and the calibration inequalities). Not formalized: the size and coefficient bookkeeping and the explicit two-vertex decomposition of Theorem 3.7, Latin contraction, the low-excess compiler, the Hadamard bound, the rank-layer lemma, and all complexity-theoretic and PRAM claims.

## Notes on the merge

- **Removed as duplication:** the four introductions (merged into one, with one related-work section), the repeated description of the Goldschlager–Shaw–Staples reduction and its two "jobs" (now Section 2.2), the repeated definitions of monotone and alternating circuits (now Section 2.1, with the value of a vertex written $`t_v`$ throughout; the escape-switching section used $`\mathrm{val}(v)`$), the two parallel-model paragraphs (merged in Section 2.4), the min-cost-flow instance definition (Section 2.3), the section "The remaining coupling" of the equal-flow preprint (its content is merged with the "Consequence for the equal-flow coupling" subsection of Section 4.2; its two reasons are kept), and the "Open targets" section, now Section 8.2. Status footnotes and `TODO` comments of the preprints were removed; no review appendices were present.
- **Notation changed to avoid clashes:** the network of Section 4 is now $`\mathcal N`$ with boundary function $`\Phi_{\mathcal N}`$ (it was $`G`$, which in Section 7 is the finite group). Citations of the constituent preprints became internal references; references to "the source note" became "an earlier internal note of this collection".
- **Genuine errors fixed:** in the proof of Lemma 7.10 (rank layers), "we descend through ancestors of $`v`$" was corrected to "descendants" (the argument moves from a vertex to a child). No other errors were found.
- **Cross-group citations:** the semantic Strahler rank, the transfer of a polynomial speedup for $`A_5`$ circuits to all of P, and the Strahler-rank evaluators are cited from group 4 (*A5 Circuits Between NC2 and P-Completeness*) and group 3 (*Newton's Method, Horn Saturation and Strahler Rank*); these results are longer than a page and are not reproduced. Nothing was moved inline.
- **Status labels that matter:** Theorem 6.5, Corollary 6.6 and the ZP-SP part of Corollary 6.11 are conditional on Assumption 6.3, whose attribution to recent work is unverified; the polylogarithmic case of Theorem 6.9 is conditional on Assumption 6.4 (an unverified reading of Orlin and Stein, 1993). Theorem 4.4 and Corollary 4.5 need the context-independence condition (ii). The conditional "bridge" theorem of an earlier note is not stated, because its premise is refuted by Corollaries 4.5 and 4.9. BP-SP, ZP-SP and RSP are bookkeeping names, not standard classes. Theorem 5.2 needs $`n\ge2`$.
