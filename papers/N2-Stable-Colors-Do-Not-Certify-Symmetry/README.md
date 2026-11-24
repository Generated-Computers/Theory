# [Stable Colors Do Not Certify Symmetry](paper.pdf)

**Author:** Generated Computers

**Date:** November 24, 2026

## Citation

```bibtex
@misc{GC:paper-N2,
  author = {{Generated Computers}},
  title = {{Stable Colors Do Not Certify Symmetry}},
  howpublished = {Generated Computers, 2026},
  year = {2026}
}
```

## Abstract

A circuit block whose inputs and outputs are $`q`$ records over a constant alphabet can be tabulated with polynomially many entries when it is equivariant under a product of symmetric groups acting on the records, since the orbits are then tuples of histograms. We ask what certifies such exchangeability. Stable colors do not: the incidence graph of the Frucht graph has one stable color on its twelve vertex-nodes and no nontrivial automorphism. Transitivity does not: the cyclic group acting on $`D^q`$ is transitive on coordinates and has at least $`|D|^q/q`$ orbits. Full symmetry does not make tabulation cheap either: a block that applies one $`A_5`$ selector $`x\mapsto M(g,x)`$ to every record is fully symmetric, but its response decides whether an arbitrary $`A_5`$ circuit outputs the identity. What does work is local: if certified transpositions of records (automorphisms of the block that fix its coefficient inputs) form a connected graph on a set $`J`$ of records, the block is $`\mathfrak S_J`$-equivariant, so a spanning forest of $`q-r`$ checkable swaps certifies the full product action. We give the resulting orbit-table compiler, which charges the depth of the coefficient computation explicitly, and its recursive version, whose depth is governed by the number of nested coefficient levels.

## Main results

All statements are proved in full. Theorems 3.1, 4.1 and 5.1 are folklore symmetry facts, presented as stress tests; the group-theoretic core of Theorem 6.4 is the standard fact that transpositions along a connected graph generate the symmetric group.

- Theorem 3.1 (Frucht incidence graph): refinement stabilizes at once with classes of sizes 12 and 18, yet the only color-preserving automorphism is the identity. Proved in full; also checked by computer (Remark 3.2, Appendix A).
- Theorem 4.1 (transitive action with many orbits): exact necklace count, at least $`d^q/q`$. Proved in full.
- Theorem 5.1 (symmetric shell with a hard coefficient): fully symmetric block whose single-record response decides a P-complete question. Proved in full.
- Lemma 6.3 and Theorem 6.4 (certified transpositions give equivariance; a spanning forest of $`q-r`$ swaps suffices), Proposition 6.5 (checking in NC). Proved in full.
- Theorem 7.1 and Corollary 7.2 (orbit-table compiler, depth $`\max\{U,T\}+O(\log n)`$). Proved in full.
- Theorem 8.2 (swap-wreath compiler, depth $`T_c+(w+1)\max\{A,L\}+O(\log n)`$). Proved in full.

## Consolidated from

| Preprint | Sections of this paper |
|---|---|
| [Stable Colors Do Not Certify Symmetry](../../preprints/Stable-Colors-Do-Not-Certify-Symmetry-November-3-2026/paper.pdf) | all (Sections 1–9, Appendix A) |

## Lean

Family [004 A5 programs](../../lean/docs/004.md): Theorem 3.1 (Frucht graph cubic and asymmetric; one refinement round keeps the two classes; only the identity preserves colors), the Burnside lower bound of Theorem 4.1 (not the exact necklace formula), Theorem 5.1 (the $`A_5`$ symmetric shell) and the connected case of Theorem 6.4 are formalized. Lemma 6.3, the component version of Theorem 6.4, and the orbit-table and swap-wreath compilers are not.

## Notes on the merge

- This is a revised version of a single manuscript; nothing from other manuscripts was moved inline.
- Cross-citations: the three citations of other Generated Computers preprints (opening $`A_5`$ cycles, in Section 1; P-completeness via Barrington gadgets, in the proof of Theorem 5.1, next to Beaudry–McKenzie–Péladeau–Thérien; the normal form for coefficient cores, in Section 9) now cite the consolidated paper of group 4, "$`A_5`$ Circuits Between $`\mathrm{NC}^2`$ and P-Completeness". Each is a pointer to related work and none is used in a proof beyond the cited P-completeness of $`A_5`$ circuit evaluation.
- Removed: the status footnote, a TODO comment, and the reference to the internal "source note" in Section 9 (rephrased as "a natural next step ... is open").
- Added: a short Appendix A "Computer checks" describing the script; Remark 3.2 now points to it.
- No mathematical errors were found.
- Build: no LaTeX errors, warnings, undefined references or overfull boxes.
