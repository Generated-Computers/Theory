# [NC Fragments of SC and Control-Trace Reductions](paper.pdf)

**Author:** Generated Computers

**Date:** November 24, 2026

## Citation

```bibtex
@misc{GC:paper-6b,
  author = {{Generated Computers}},
  title = {{NC Fragments of SC and Control-Trace Reductions}},
  howpublished = {Generated Computers, 2026},
  year = {2026}
}
```

## Abstract

We study which parts of a sequential computation carry its hardness: the adaptive choices that steer it, or the payload that is carried along once the choices are fixed. For $`\mathrm{SC}^k`$ we use Single-Probe Affine Iteration ($`\mathrm{SPAI}_k`$), in which a polynomial controller reads one bit per stage from a data vector of $`\lceil\log N\rceil^k`$ bits that evolves by controller-selected affine maps; it is $`\mathrm{SC}^k`$-complete, by the standard configuration encoding. Without feedback from the probed bits the run is in logspace-uniform $`\mathrm{NC}^2`$; with at most $`C\log N`$ feedback-sensitive stages it is still in $`\mathrm{NC}^2`$, trajectory included. Block summaries with affine guards merge exactly, with $`2^\rho`$ leaves when the surviving guard rows have rank $`\rho`$, so the total language that rejects whenever a merge rank exceeds $`c_1\log N`$ is in $`\mathrm{NC}^3`$. Richer guard languages from knowledge compilation give further total, cap-checked languages in $`\mathrm{NC}^2`$, $`\mathrm{NC}^3`$ or $`\mathrm{NC}^{k+1}`$, with separating families and barriers; these are separations of representations, and that the canonical algorithms stay within their caps on the vtree, portfolio, separator and rank-factor witnesses is only sketched.

For P, Sequential NOR runs in time $`O(n\log^3n)`$ on a multitape machine and hence, by Williams' simulation, in space $`O(\sqrt n\log^2n)`$; value-storing algorithms need $`\Omega(n/\log n)`$ pebbles on some instances, reset sets admit no short candidate list, and fan-out normalizes to two. For a register–stack machine in normalized form the sign bits determine acceptance, and given the read addresses the register values solve a sparse unit triangular system in polylogarithmic depth; conditionally on Reinhardt's transfer theorem, used as a black box, producing the control trace of his linear-time evaluator with polynomial work and depth $`n^{1-\varepsilon}`$ would give $`\mathrm{P}\subseteq\mathrm{SP}`$. A backward control-observability closure shows that the control-live cells and closure forms suffice to continue the trace, all other cells being payload; balanced ladders show that rank $`R`$ does not force $`\Omega(R^2)`$ read incidences. Finally, exponential boundary-state capacity is compatible with constant-depth transfer, every rank layer of a Horn system is a monotone $`O(\log^2N)`$-depth circuit, and straight-line programs with $`h`$ fanout nodes evaluate in depth $`O((h+1)\log^2n)`$. A separator transfer and two conjectures are conditional or open; no class collapse is claimed.

## Main results

Numbers refer to `paper.pdf`.

- Theorem 3.3 and Corollary 3.5: $`\mathrm{SPAI}_k`$ is $`\mathrm{SC}^k`$-complete (hardness with diagonal, time-invariant instances); $`\mathrm{SC}^k\subseteq\mathrm{NC}^j`$ iff $`\mathrm{SPAI}_k\in\mathrm{NC}^j`$ ($`j\ge2`$). Proved in full; a restatement of the machine model, not claimed as new.
- Proposition 3.7: feedback-free iteration in $`\mathrm{NC}^2`$. Proved in full.
- Theorem 4.5, Corollary 4.6, Lemma 4.9: one block of $`C\log N`$ feedback-sensitive stages in $`\mathrm{NC}^2`$ with trajectory; transcript leaves. Proved in full.
- Theorem 5.3, Theorem 5.6, Proposition 5.9: exact syndrome recompression; the cap-checked language $`\mathrm{LR}\text{-}\mathrm{SPAI}_{k;c_0,c_1}`$ in $`\mathrm{NC}^3`$ with trajectory; invariant observation space gives $`\mathrm{NC}^2`$. Proved in full.
- Theorem 6.3 and Theorems 6.7, 6.14, 7.6, 7.14, 7.19, 7.23: generic hierarchy theorem and the six rungs (PF, VT, AVP, SepTR in $`\mathrm{NC}^3`$; Path in $`\mathrm{NC}^{k+1}`$; RF-TW in $`\mathrm{NC}^2`$). Proved in full.
- Propositions 6.8, 6.9, 6.11, 6.15, 6.16, 7.7, 7.10, Lemma 7.12, Examples 7.16 (a), 7.21 (a): direct sum, selected-row parity separation, bank match, and the equality, ordered-equality, inner-product, component-containment and $`K_{n,n}`$ barriers. Proved in full. Acceptance of the VT, AVP, SepTR and RF-TW gain witnesses by the canonical cap-checked algorithm (Remark after Proposition 7.7, Examples 7.15, 7.20, 7.24, 7.25): **sketch**.
- Theorem 8.2, Corollary 8.4: Sequential NOR in time $`O(n\log^3 n)`$ (multitape) and space $`O(\sqrt n\log^2 n)`$, quoting Williams (2025). Proved in full.
- Theorem 8.8 (pebbling ceiling, quoting Paul–Tarjan–Celoni), Theorem 8.9 (fan-out normalization), Theorem 8.11 and Corollaries 8.12–8.13 (reset sets), Proposition 8.1 (consequences of $`\mathrm{P}\subseteq\mathrm{PolyL}`$). Proved in full.
- Theorem 1.1 = Proposition 9.4, Theorems 9.5, 9.7: control-trace sufficiency, triangularization, payload reconstruction. Proved in full.
- Theorem 1.2 = Theorem 9.9 and Proposition 9.13: trace-revelation transfer and MCP ≡ USIARV. **Conditional** on Fact 9.8 (Reinhardt's results, used as a black box and not re-derived).
- Theorem 10.2, Corollary 10.3 (ladders), Lemma 10.6, Theorem 10.8, Corollary 10.9 (control observability, payload erasure), Lemma 10.12 (separator budget). Proved in full. Theorem 10.14: **conditional** on a hypothetical separator compiler. Problem 10.11: **open**. Conjecture 10.15: **conjecture** (miscalibrated, see the remark after it).
- Theorems 11.2, 11.3, Proposition 11.4, Theorems 11.6, 11.8, 11.9, Corollary 11.10, Theorem 11.12, Theorems 11.15, 11.17, Corollaries 11.16, 11.18. Proved in full. The combined transfer criterion (Section 11.7): fanout branch proved, portal branches **sketch**. Conjecture 11.19: **conjecture**.

## Consolidated from

| Preprint | Sections of this paper |
|---|---|
| [An SCᵏ-Complete Problem with an NC³ Fragment](../../preprints/An-SC-k-Complete-Problem-with-an-NC-3-Fragment-November-3-2026/paper.pdf) | 1, 2 (Lemmas 2.2–2.3), 3, 4.3, 5, App. A |
| [Logarithmic Feedback in SC² Lies in NC²](../../preprints/Logarithmic-Feedback-in-SC2-Lies-in-NC2-November-3-2026/paper.pdf) | 1, 4 (4.1, 4.2, 4.4, 4.5) |
| [Knowledge Compilation Gives NC Fragments of SC](../../preprints/Knowledge-Compilation-Gives-NC-Fragments-of-SC-November-3-2026/paper.pdf) | 1, 6, 7, 12 |
| [A P-Complete Problem in Square-Root Space](../../preprints/A-P-Complete-Problem-in-Square-Root-Space-November-3-2026/paper.pdf) | 1, 8, App. A |
| [Strict P-Completeness Reduces to the Control Trace](../../preprints/Strict-P-Completeness-Reduces-to-the-Control-Trace-November-3-2026/paper.pdf) | 1 (Theorems 1.1–1.2), 9 |
| [Control Observability Erases Payload in Trace Generation](../../preprints/Control-Observability-Erases-Payload-in-Trace-Generation-November-3-2026/paper.pdf) | 1, 2 (Definition 2.1), 10, 12, App. A |
| [Exponential-State Portals with Constant-Depth Transfer](../../preprints/Exponential-State-Portals-with-Constant-Depth-Transfer-November-3-2026/paper.pdf) | 1, 11, 12, App. A |

## Lean

Parts of the constituent results are formalized in Lean 4 with Mathlib, in the [Lean library](../../lean/README.md); complexity-theoretic conclusions (logspace, NC, P-completeness, depth and uniformity bounds) are not formalized.

- [`lean/docs/008.md`](../../lean/docs/008.md) (SC ladder): the configuration encoding behind the hardness half of Theorem 3.3, exactness of transcript leaves (Lemma 4.9) and the unique-transcript lemma (Lemma 4.3), the feedback-free case of Proposition 3.7, pair exactness (Lemma 5.1), exact syndrome recompression (Theorem 5.3), the invariant-observation-space reduction (Proposition 5.9); and from the ladder the leaf pullback and conjunction lemmas (7.2, 7.3), Lemma 7.4, the transfer-pullback identity (Lemma 7.18), the equality, ordered-equality and inner-product barriers (Propositions 6.11, 6.16, 7.10, Lemma 7.9). The NC theorems, the class theorems of the rungs and the examples are not formalized.
- [`lean/docs/006.md`](../../lean/docs/006.md) (Sequential NOR normal forms): the reset-set surjectivity Theorem 8.11 and its count, the counterexample to the source's embedding claim, the subdivision embedding (Lemma 8.7) and the fan-out normalization (Theorem 8.9) with explicit indices. Time and space bounds, Williams' simulation and the pebbling results are not formalized.
- [`lean/docs/010.md`](../../lean/docs/010.md) (tabulation and frontier methods): control-trace sufficiency (Proposition 9.4), triangularization (Theorem 9.5), nilpotent doubling (Lemma 9.6) and the payload identity of Theorem 9.7. Fact 9.8, Theorem 9.9, Proposition 9.13, the PRAM costs and the integer bit bound are not formalized.
- [`lean/docs/005.md`](../../lean/docs/005.md) (portals, separators and frontiers): the two-execution form of Theorem 10.8 and the ladder facts of Theorem 10.2 (the linear separator budget and the counting part of the separator transfer are covered by theorems formalized for another paper of family 005); the capacity switch of Proposition 11.4 and the covering of Theorem 11.3(iv), monotonicity and the layer identity of Theorem 11.9 with its band corollary, and the stopping rule of Corollary 11.18. Lemma 10.6, Corollary 10.3, the symbolic, branching-program, composition-algebra and fanout-compiler depth bounds, and the Maurer–Rhodes realization of $`M`$ are not formalized.

## Notes on the merge

- **Removed as duplicates.** The four separate definitions of $`\mathrm{SPAI}_k`$ and of feedback-sensitive stages (one definition in Section 3); the three statements of the transcript-leaf lemma (the knowledge-compilation preprint's "proof idea" version is dropped and its extra sentence on the form of guard rows added to Lemma 4.9, where the proof shows it); the repeated lists of standard parallel facts (one copy, Lemmas 2.2–2.3); the duplicate statement of control-trace sufficiency in the control-observability preprint (now a reference to Proposition 9.4); the per-preprint introductions, organization paragraphs and related-work sections (merged into Section 1); the repeated definitions of the Horton–Strahler rule (Definition 2.1). The unique-transcript argument is kept both in Lemma 4.3 and in the proof of Lemma 4.9, because the two constructions (segment recursion and forced runs over arbitrary intervals) differ.
- **Removed review material.** A sentence attributing a depth conjecture to "the reviewers of the source notes" (remark after Corollary 5.7) was rephrased without the attribution; status footnotes of the preprints were replaced by the single consolidation footnote. The computational-check sections of two preprints, and the computer-check paragraph of the square-root-space preprint, moved to Appendix A.
- **Inlined from other groups.** The rank-layer reachability lemma (Lemma 11.1) with its proof, from *Menger's Theorem Inside One Strahler Layer* (group 3); it is used in the proof of Theorem 11.9. The live-width space argument (Proposition "live" of *Two Pages Suffice for P-Completeness*, group 5) is written out in the proof of Proposition 8.5, adapted to the definition of live sets used there (which includes the cut position itself).
- **Cross-group citations.** Group 3 (closed portals; Horn saturation), group 4 (ranked $`A_5`$ saturation and equality graphs $`E_K`$, the strict transfer for $`A_5`$, the surplus charging argument), group 5 (reset normal form, $`\mathrm{P}\subseteq\mathrm{quasiNC}`$ equivalence, live width), group 6a (constant-frontier generator, trace generators, fanout height), group 7a (separator speedups put MCP in NC; batching; generic barriers), note N3 (logarithmic-width bag messages).
- **Genuine inconsistency fixed.** The control-trace preprint uses MCP for Reinhardt's circuit value problem for compact circuits with multiplex-select gates, while the control-observability preprint expanded MCP as "the monotone circuit value problem". The merged paper uses MCP only in the sense of Fact 9.8 throughout Sections 9–10; no statement changes, since every statement about MCP there is about the fixed evaluator of Fact 9.8. No mathematical errors were found otherwise.
- **Small edits.** Overfull lines were fixed by rewording (Example 7.24, the heading of Section 7.4, Appendix A). Section 7.4 is titled "Rank-factor networks of fixed treewidth" (was "execution graphs").
- **Status labels that matter.** Theorem 9.9 and Proposition 9.13 are conditional on Fact 9.8; Theorem 10.14 is conditional on a hypothetical compiler; Conjectures 10.15 and 11.19 and Problem 10.11 are open; acceptance of the ladder's vtree, portfolio, separator and rank-factor witnesses and the portal branches of Section 11.7 are sketches. Corollary 3.5 and Proposition 9.13 are reformulations of open problems, not progress on them.
