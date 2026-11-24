# [Barriers to Speeding Up Circuit Evaluation](paper.pdf)

**Author:** Generated Computers

**Date:** November 24, 2026

## Citation

```bibtex
@misc{GC:paper-7a,
  author = {{Generated Computers}},
  title = {{Barriers to Speeding Up Circuit Evaluation}},
  howpublished = {Generated Computers, 2026},
  year = {2026}
}
```

## Abstract

We study why natural strategies for speeding up circuit evaluation in parallel fail, and what their success would imply, and we classify each barrier as unconditional (for a measure or a restricted model), conditional, or a reduction. Unconditionally: the fixed-lag copy program has correction rank $`\lceil N/d\rceil`$ but constant depth; padding any circuit of size $`m`$ to size at most $`2m`$ raises the multiplicative Strahler rank to $`\Omega(m/\log^2 m)`$ and the rank-frontier width to $`\Omega(\log^2 m)`$, and exact GF(2) Newton iteration needs $`k+1`$ rounds on a ladder of length $`k`$; prefix-OR programs have moral treewidth $`\Omega(\sqrt n)`$ or complete curvature yet logarithmic depth; matched unary rails have fractional catalyst load $`h/2`$ yet depth $`O(\log h)`$; exact invariant linear features of two generators of $`S_{2^q}`$ need dimension $`2^q-1`$ and exact summaries of $`q`$ independent bits need $`2^q`$ states; every predecessor-preserving unfolding of $`M`$ vertices and primal treewidth $`w`$ of a circuit $`C`$ of indegree two gives $`\mathrm{Peb}(C)\le 2(w+1)(\lceil\log_2 M\rceil+1)+1`$, so polynomial-size such unfoldings of grid instances of Sequential NOR of length $`N`$ have treewidth $`\Omega(\sqrt N/\log N)`$; and validating any batch of candidate continuations from one exact boundary certifies only the farthest single prefix, while one-round black-box composition of restartable children is impossible. Conditionally on the Unique Games Conjecture and $`\mathrm{P}\ne\mathrm{NP}`$, the segment-cut number of fan-out-two expansions of Sequential NOR has no constant-factor polynomial-time approximation at logarithmic target length, although a factor $`L+1`$ is achieved in deterministic $`\mathrm{NC}^2`$; the hard instances have linear optimum. As a reduction, if the fixed evaluator of a strictly sequential P-complete problem admits benign padding, an algorithm solving all low-congestion subtrees of its balanced interval tree in polylogarithmic depth would place that problem, and hence MCVP, in $`\mathrm{NC}`$.

On the positive side we prove promise compilers for Sequential NOR (branching depth, segment cuts, tail-factorized systems of fixed treewidth), the four-Russians speedup with $`O(n2^{O(b)})`$ work and $`O((n/b)\log b+b+\log n)`$ depth on a PRAM, which is a logarithmic-factor speedup that does not apply to compact multiplex circuits and does not have linear work, and composition theorems for the interval-tree route that are implications from hypothetical low-subtree algorithms or cut combiners. None of these results bears on whether $`\mathrm{P}=\mathrm{NC}`$.

## Main results

Theorem numbers refer to [paper.pdf](paper.pdf). Table 1 of the paper classifies every barrier.

- **Fixed-lag copy** (Theorem 3.2, Proposition 3.3): correction rank of the copy program is exactly $`\lceil N/d\rceil`$ over all block partitions, yet constant depth suffices. Proved in full (unconditional, about a measure).
- **Identity padding** (Theorem 3.5, Theorem 3.6, Corollary 3.7): exact Newton delay $`k+1`$ on ladders; linear-size padding raises rank and frontier width; the high-rank wide-frontier promise is complete. Proved in full (unconditional; Corollary 3.7 is a reduction). Remark 3.8 (compact multiplex circuits) is a remark.
- **Width, cover and curvature measures** (Proposition 4.1, Theorems 4.3, 4.4, 4.8, 4.9, Propositions 4.5, 4.6): proved in full (counterexamples to measures; Theorem 4.9 is a P-completeness reduction). Proposition 4.2 (relation fusion) is a **known result with a proof sketch only**.
- **Fractional catalyst covers** (Theorems 5.2, 5.3, 5.5, Corollaries 5.8, 5.9, Theorem 5.10, Proposition 5.11): proved in full. Section 5.5 (exponent arithmetic) is **conditional arithmetic about a hypothetical procedure**, not a theorem.
- **Feature dimension and summaries** (Theorems 6.3, 6.4, Corollary 6.5, Proposition 6.6): proved in full (unconditional, for the models of exact invariant linear features and exact extensional summaries).
- **Four-Russians speedup** (Theorem 6.7, Corollary 6.8): proved in full; scope stated in Section 6.2.3.
- **Fan-out-two normal form and canonical expansion** (Theorems 7.2, 7.5): proved in full (Theorem 7.2 is classical and included for convenience).
- **Segment-cut compilers** (Theorems 8.3, 8.6, 8.13, Corollary 8.14): proved in full. Remark 8.4 (general branching depth) and Remark 8.29 (richer rank schedules) **quote statements of earlier notes that are not proved and not used**.
- **Guard–router reduction** (Theorem 8.19): proved in full. **Unique-Games barrier** (Corollaries 8.21, 8.23): **conditional on the UGC and P ≠ NP**, via Svensson's theorem (Theorem 8.16, quoted).
- **Rank schedules** (Theorems 8.27, 8.28, 8.30): proved in full.
- **Tail-factorized compilers** (Lemma 9.4, Theorems 9.5, 9.6, Corollary 9.7, Proposition 9.10): proved in full; bounded-treewidth recognition (Proposition 2.5) is imported from the literature.
- **Pebbling barrier** (Theorem 9.15, Lemma 9.16, Corollaries 9.17, 9.18, Remark 9.19): proved in full (unconditional, for predecessor-preserving unfoldings; not a circuit lower bound).
- **Separator speedups** (Theorem 10.5, Corollary 10.6): proved in full as **conditional statements/reductions**: under the dyadically benign padding hypothesis, Conjecture 10.1 implies MCP ∈ NC; the converse of Corollary 10.6 assumes polynomially bounded words.
- **Online separator transfer** (Theorem 10.9, Corollary 10.10, Lemma 10.12, Proposition 10.14): proved in full; Corollary 10.10 and Proposition 10.14 are **implications from hypothetical algorithms** (Conjectures 10.1 and 10.13 are not claimed).
- **Batching first failures** (Theorem 11.3, Corollaries 11.4, 11.5, Theorem 11.7): proved in full (unconditional; Theorem 11.7 is a black-box query lower bound). Theorem 11.9 and Theorem 11.12 are proved in full; Corollary 11.10 is **conditional**; Conjecture 11.14 is not claimed.

## Consolidated from

| Preprint | Sections of this paper |
|---|---|
| [Four Barriers to Speeding Up Circuit Evaluation](../../preprints/Four-Barriers-to-Speeding-Up-Circuit-Evaluation-November-3-2026/paper.pdf) | 1, 2.4, 3, 6 |
| [A Pebbling Barrier for Clone-and-Decompose Algorithms](../../preprints/A-Pebbling-Barrier-for-Clone-and-Decompose-Algorithms-November-3-2026/paper.pdf) | 1, 2.1, 2.3, 7.3 (corridors), 9 |
| [Separator Speedups Would Put MCVP in NC](../../preprints/Separator-Speedups-Would-Put-MCVP-in-NC-November-3-2026/paper.pdf) | 1, 2.4, 10, Appendix A |
| [Prefix OR Defeats Treewidth and Curvature Measures](../../preprints/Prefix-OR-Defeats-Treewidth-and-Curvature-Measures-November-3-2026/paper.pdf) | 1, 4 |
| [Batching First Failures Cannot Beat One Prefix](../../preprints/Batching-First-Failures-Cannot-Beat-One-Prefix-November-3-2026/paper.pdf) | 1, 11 |
| [Fractional Covers Do Not Certify Sequential Hardness](../../preprints/Fractional-Covers-Do-Not-Certify-Sequential-Hardness-November-3-2026/paper.pdf) | 1, 5 |
| [Segment Cuts in NC2 and a Unique Games Barrier](../../preprints/Segment-Cuts-in-NC2-and-a-Unique-Games-Barrier-November-3-2026/paper.pdf) | 1, 2.1, 2.2, 7, 8 |

## Lean

Complexity-theoretic conclusions (NC, P-completeness, UG-hardness) are not formalized in any family.

- [`../../lean/docs/010.md`](../../lean/docs/010.md) (four barriers, 010e): the extensional-summary barrier (Proposition 6.6); the generation lemma and both forms of the feature-dimension theorems (Lemma 6.2, Theorems 6.3, 6.4) over every field; synchronous correction and Theorem 3.2 (part (b) as the lower bound over partitions, attained by blocks of length d); Lemma 3.4 and Theorem 3.5 (exact Newton delay). The padding construction (Theorem 3.6, Corollary 3.7), the block-matrix compiler, Corollary 6.5 and the four-Russians results are not formalized.
- [`../../lean/docs/007.md`](../../lean/docs/007.md) (pebbling barrier 007c, segment cuts 007b): the pebbling projection (Lemma 9.12), correctness of unfoldings and the grid pebbling price g+1 (Lemma 9.16); the maximal-packing bound of Theorem 8.10, the guard–router reduction (Lemma 8.18, Theorem 8.19) in both directions, and the values on the family of Theorem 8.30. Not formalized: Lemmas 9.13, 9.14, the treewidth form of Theorem 9.15, the tail-factorized system, Svensson's theorem and Corollaries 8.21, 8.23, Lemma 8.22, the compilers and the rank schedules.
- [`../../lean/docs/005.md`](../../lean/docs/005.md) (separator 005a, batching 005g): the interval-tree combinatorics (height, Lemma 10.3, the linear budget, the heavy-node count), Lemma 10.12, and the call count of the recursion of Theorem 10.9; the first-failure validator (Lemma 11.2), the batch collapse (Theorem 11.3) and the black-box barrier (Theorem 11.7). The padding collapse, the calibration, depth bounds and conditional corollaries are not formalized.
- [`../../lean/docs/009.md`](../../lean/docs/009.md) (prefix OR, 009e): the masking bijection (Lemma 4.7), the identities of Theorem 4.8 (without the NC¹ claim), the zero-mask reduction behind Theorem 4.9, the K_{k,k} minor model of Theorem 4.3 and the cover and K_{r,r} facts of Theorem 4.4; treewidth itself is not in Mathlib, so the treewidth consequences are not formalized, nor are Propositions 4.1, 4.2, 4.5, 4.6.
- [`../../lean/docs/003.md`](../../lean/docs/003.md) (fractional covers, 003b): weak duality for the path-flow dual (Theorem 5.2), the two-path concentration bounds of Theorem 5.5 as finite averaging statements (the incomparable case under the stated hypothesis), Example 5.6, and the value h/2 and integral height ⌈h/2⌉ of the mirage and the complete grid (Theorem 5.10, Proposition 5.11). Strong duality, the flow form, Lemma 5.4, Corollaries 5.8, 5.9, the O(log h) evaluation and Section 5.5 are not formalized.

## Notes on the merge

- **Removed as duplication.** Seven introductions, related-work sections and status footnotes were merged into one introduction (Section 1) with a classification table. Sequential NOR, the model conventions, normalized record systems, the binary-core and four-coordinate propositions, constraint systems with the decomposition evaluator and bounded-treewidth module, and the two append-only machine models are defined once in Section 2. The pebbling preprint's fan-out-two circuits, branch skeleton and path-count/formula-unfolding lemma were merged with the segment-cut preprint's versions (Definition 7.7, Definition 7.8 with the corridor paragraph, Lemmas 8.1–8.2; the unfolding lemma now explicitly allows formal-variable leaves, as both sources used it). The separator preprint's "Computational checks" section became Appendix A. Restatements of companion results that are now internal became cross-references.
- **No review material** was present in the LaTeX sources beyond status footnotes; these were removed. Exhaustive checks without scripts (grid pebbling price, guard–router reduction) are listed in Appendix A as such.
- **Genuine errors fixed.**
  1. The separator and batching preprints called the problem of the fixed evaluator "the monotone circuit value problem (MCP)" while using Reinhardt's strict sequential P-completeness and the fixed evaluator of the control-trace paper, which concern a circuit value problem for compact circuits with multiplex-select gates (also denoted MCP there and in the four-barriers preprint). Here MCP denotes the multiplex problem throughout (Section 2.4), and MCVP the monotone circuit value problem; since both are P-complete, the conclusion "MCP ∈ NC" of Theorem 10.5 is equivalent to P ⊆ NC and implies MCVP ∈ NC, as the section title says. No statement changed otherwise.
  2. Citations of the form "Section 5 of" a companion preprint (fixed-lag copy) referred to section numbers that no longer exist; they now cite the consolidated paper without a section number.
- **Notation clashes resolved.** The multiscale correction rank is written $`\mathfrak{C}_L`$ (it was $`\mathfrak{R}_L`$, which clashed with the region partition $`\mathfrak{R}`$ of Section 9); the padded family of Corollary 3.7 is $`\mathcal{H}`$ (was $`\mathcal{B}`$, the branch-skeleton symbol); NC, P, SP and NOR use one font throughout.
- **Cross-group citations** (no result was moved inline; the cited results are longer than a page or only background): group 3 (Newton iteration in Strahler-rank rounds, Taylor rank, Horn–Strahler rank, Strahler-layer saturation); group 4 (semantic Strahler compiler); group 5 (binary-core records, Proposition 2.2; four-coordinate embedding, Proposition 2.3; related compilers); group 6a (append-only machines and read-adaptivity rank of the copy program, constant-frontier computations, the catalyst-height compiler and the bound δ ≤ χ ≤ 2δ); group 6b (affine history machine, MCP and its fixed evaluator, demanded reads and the linear separator budget, the observable separator conjecture, strict-sequential transfer); group 7b (flow and LP barriers, background only).
- **Status labels kept.** Proposition 4.2 is a known result with a proof sketch; Remarks 8.4 and 8.29 quote unverified statements of earlier notes; Corollaries 8.21 and 8.23 are conditional on the UGC and P ≠ NP; Theorem 10.5 and Corollary 10.6 are conditional on the padding hypothesis (and Conjecture 10.1); Corollary 10.10, Proposition 10.14 and Corollary 11.10 are implications from hypothetical algorithms; Section 5.5 is conditional arithmetic; Conjectures 10.1, 10.13 and 11.14 are not claimed.
