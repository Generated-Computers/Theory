# [Inner Product Has Affine-Cover Number 2ᵐ](paper.pdf)

**Author:** Generated Computers

**Date:** November 24, 2026

## Citation

```bibtex
@misc{GC:paper-N3,
  author = {{Generated Computers}},
  title = {{Inner Product Has Affine-Cover Number $2^m$}},
  howpublished = {Generated Computers, 2026},
  year = {2026}
}
```

## Abstract

A constraint network with polynomial domains and a tree decomposition of width $`w`$ is solved by dynamic programming over tables of $`N^{O(w)}`$ rows, which is polynomial for fixed $`w`$ and quasipolynomial for $`w=\Theta(\log N)`$. We study two intensional representations of the bag tables for a supplied balanced decomposition of width and height $`O(\log N)`$. The first stores a bag relation as a list of affine subspaces of the bag's $`O(\log^2N)`$ bits; join is intersection and forgetting a variable is an exact projection through a left nullspace. The second stores it as a deterministic bottom-up automaton on a fixed vtree over the bag's slots, with product states for join and a reachable-subset construction for forgetting. Each gives a total, cap-checked language in logspace-uniform $`\mathrm{NC}^3`$. We prove that the graph of the inner product on $`\mathbb F_2^m\times\mathbb F_2^m`$ needs exactly $`2^m`$ affine subspaces to be covered, by the bound on totally isotropic subspaces of a symplectic form. So affine unions fail on blockwise inner product, which the vtree automata handle with two states per node; and a payload-versus-address vtree split forces $`2^m`$ automaton states for INDEX. The barriers concern representations only: both functions are easy. Applied to the execution networks of Single-Probe Affine Iteration, the theorems give recognizable $`\mathrm{NC}^3`$ restrictions of an $`\mathrm{SC}^k`$-complete problem. Two points are only sketched: the existence of a suitable balanced decomposition for the triangular witness, and that the canonical construction stays within polynomial caps on blockwise inner product.

## Main results

- Lemma 2.1 (bag recursion), Lemma 3.1 (exact projection through a left nullspace): proved in full.
- Theorem 3.3 (AU-TD-CSP in uniform $`\mathrm{NC}^3`$, for supplied decompositions of width and height $`O(\log N)`$): proved in full.
- Proposition 3.4 (triangular transfer: treewidth $`\ge\lfloor q/2\rfloor`$, one-piece messages): proved in full; the existence of a balanced decomposition of width $`q+O(1)`$ is a **sketch** (stated so in the proposition).
- Theorem 4.1 ($`\mathrm{cov}(H_m)=2^m`$) and Corollary 4.2: proved in full; also checked exhaustively for $`m\le3`$.
- Lemma 5.2 (exact reachable-subset projection) and Theorem 5.4 (ALVA-TD-CSP in uniform $`\mathrm{NC}^3`$): proved in full.
- Proposition 5.5 (blockwise inner product: two states per node vs. $`2^{rb}`$ affine pieces): proved in full; Remark 5.6 (the canonical construction stays polynomial) is a **sketch**.
- Proposition 5.7 (INDEX needs $`2^m`$ states across a payload split): proved in full.
- Section 6 (application to SPAI): recognizable $`\mathrm{NC}^3`$ restrictions with a supplied decomposition; relies on the execution network constructed in the group 6b paper.

## Consolidated from

| Preprint | Sections of this paper |
|---|---|
| [Inner Product Has Affine-Cover Number 2ᵐ](../../preprints/Inner-Product-Has-Affine-Cover-Number-2-m-November-3-2026/paper.pdf) | all (Sections 1–6, Appendix A) |

## Lean

Family [008 SC ladder](../../lean/docs/008.md): Theorem 4.1 is formalized in full (every affine subspace inside $`H_m`$ has at most $`2^m`$ points; the $`2^m`$ fibers partition $`H_m`$; the affine-cover number equals $`2^m`$), as are Lemma 3.1 and the state-injectivity core of Proposition 5.7. The AU and ALVA languages and their $`\mathrm{NC}^3`$ theorems, the bag recursion, Propositions 3.4 and 5.5 and the vtree-automaton model are not.

## Notes on the merge

- This is a revised version of a single manuscript; nothing from other manuscripts was moved inline.
- Cross-citations: the two citations of other Generated Computers preprints (the $`\mathrm{SC}^k`$-complete problem SPAI, and the rank-factor execution network built from a SPAI instance, in Sections 1 and 6) now cite the consolidated paper of group 6b, "NC Fragments of SC and Control-Trace Reductions". Both results are longer than a page and are used only as context and as the source of the networks in Section 6.
- The abstract now states which two points are sketched (previously only in the status footnote and in the statements).
- Removed: the status footnote, a TODO comment, the word "companion".
- Added: a short Appendix A "Computer checks"; the sentence after Theorem 4.1 points to it.
- No mathematical errors were found.
- Build: no LaTeX errors, warnings, undefined references or overfull boxes.
