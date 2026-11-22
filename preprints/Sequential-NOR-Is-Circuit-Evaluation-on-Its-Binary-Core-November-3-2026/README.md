# [Sequential NOR Is Circuit Evaluation on Its Binary Core](paper.pdf)

**Author:** Generated Computers

**Date:** November 3, 2026

## Citation

```bibtex
@misc{GC:Sequential-NOR-Is-Circuit-Evaluation-on-Its-Binary-Core-November-3-2026,
  author = {{Generated Computers}},
  title = {{Sequential NOR Is Circuit Evaluation on Its Binary Core}},
  howpublished = {Generated Computers preprint, manuscript 006f},
  year = {2026}
}
```



## Lean

Part of this paper is formalized in Lean 4 with Mathlib, in the [Lean library](../../lean/README.md). The scope is described in [`lean/docs/006.md`](../../lean/docs/006.md), and the main statements are in the Comparator challenge [`BinaryCore.lean`](../../lean/ComparatorChallenges/BinaryCore.lean). Every listed theorem is proved without `sorry` and uses only the axioms `propext`, `Quot.sound` and `Classical.choice`. Complexity-theoretic conclusions (logspace, NC, P-completeness and the like) are not formalized.

**006f (Binary core).** Core variables are indexed by their core position rather than by their rank, an order-preserving renaming. Formalized: the root classification (Lemma 2.2), the descriptor equation $x_q=[\![\delta(q)]\!](z)$, triangularity and the unique solution of the core system (Definition 3.1, Lemma 3.2), and the mathematical content of the retraction theorem (Theorem 3.4): substituting any solution of the core system into the descriptors gives the trace. Also formalized: four-coordinate universality (Theorem 5.2). For every ordered NOR circuit, $\mathrm{Embed}(\mathcal C)$ is a parent array of length $1+2t+4G$ with $x_{\mathrm{Rep}(y)}=y$, its binary core is exactly $\{\mathrm{Rep}(w_i)\}$, and its core equations are those of $\mathcal C$. Not formalized: the circuit families $\mathrm{Core}_n$ and $\mathrm{Decode}_n$ and their depth, pointer doubling (Lemma 3.3), Section 4, logspace computability, and Corollaries 5.3–5.5 and Proposition 5.6.

## Sources

Rewritten from the following internal notes (document numbers of the 27 October 2026 corpus review):
- #19 Sequential NOR Binary Core Compilation (`Sequential_NOR_Binary_Core_Compilation.pdf`), §§2, 4, 5, 9–12 (binary-core compression, sharpened block compiler, polynomial-list completion, constant-overhead universality, collapse consequence, uniformity, audit). Its §§6–8 (core depth, formula cores, interaction covers) are in manuscript 007a; its §3 is in manuscript 006e.
- #06 SEQNOR Flagship Finished Theorems (`SEQNOR_main/SEQNOR_FLAGSHIP_FINISHED_THEOREMS_2026_09_07.pdf`), §§2–3: Lemmas 2.1–2.2, Theorem 3.1 (exact binary-core retraction), Corollaries 3.2–3.3.
- #18 Sequential NOR Structural Parallelization Compendium (`Sequential_NOR_Structural_Parallelization_Compendium.pdf`), §4 (Propositions 4.3 and 4.7, logspace cases), §7 (Theorem 7.2), §8 (Theorem 8.1, Corollary 8.2), §12 (Theorem 12.1), §13 (Theorem 13.1, Corollary 13.2), §1 (Proposition 1.3).

## Status

All results are proved in full. They are an exact structural normal form (Sequential NOR is, up to an NC² shell, ordered NOR-circuit evaluation on its |B(j)| unguarded anchors), a matching logspace embedding of every ordered NOR circuit with one core gate per source gate, and promise-class upper bounds (depth O(log² n + |B|), hence NC^max(2,c) for |B| = O(log^c n), and logspace for |B| = O(log n)). None of them is an unconditional result about unrestricted Sequential NOR, and the tools are standard: pointer jumping along negation chains, chronological guess-and-check block recovery, and a P-completeness gadget of the kind used by Okhotin. The P-completeness corollary reproduces Okhotin's theorem and is attributed to him. The polynomial-list completion statement is presented as a conditional reduction whose hypothesis, for unrestricted inputs, is as strong as placing Sequential NOR in NC. The overlapping versions in the three sources were merged into one account; no source result was found false. The core compression, the block recovery for several block widths, and the residual block recovery were checked exhaustively for all 46,233 parent arrays with n ≤ 8, and the embedding on 3,000 random circuits; these are regression checks only. Not refereed.

## Code

Checking scripts used for this manuscript are in [`verification/`](verification/): `check8.out`, `check_core.py`. They are plain Python 3 with no dependencies outside the standard library unless the script says otherwise.
