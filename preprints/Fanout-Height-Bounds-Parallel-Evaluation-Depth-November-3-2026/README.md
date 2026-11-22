# [Fanout Height Bounds Parallel Evaluation Depth](paper.pdf)

**Author:** Generated Computers

**Date:** November 3, 2026

## Citation

```bibtex
@misc{GC:Fanout-Height-Bounds-Parallel-Evaluation-Depth-November-3-2026,
  author = {{Generated Computers}},
  title = {{Fanout Height Bounds Parallel Evaluation Depth}},
  howpublished = {Generated Computers preprint, manuscript 005e},
  year = {2026}
}
```



## Lean

Part of this paper is formalized in Lean 4 with Mathlib, in the [Lean library](../../lean/README.md). The scope is described in [`lean/docs/005.md`](../../lean/docs/005.md), and the main statements are in the Comparator challenge [`FanoutHeight.lean`](../../lean/ComparatorChallenges/FanoutHeight.lean). Every listed theorem is proved without `sorry` and uses only the axioms `propext`, `Quot.sound` and `Classical.choice`. Complexity-theoretic conclusions (logspace, NC, P-completeness and the like) are not formalized.

**005e (Fanout height).** Programs are modelled as directed graphs with a fanout set `H`, and paths are lists. The round structure of the fanout-height compiler is formalized as an explicit iteration. In round `j + 1`, a node is computed once all of its skeleton predecessors are known. If every path carries at most `d` fanout nodes, every node is known after `d + 1` rounds. On acyclic graphs a path carries at most `|H|` fanout nodes. For Sequential NOR, the proposition `H = {j₁, …, jₙ}` and `d(C) = h` is proved. The per-round formula evaluation and its depth are not formalized, and neither is the equality-assisted redirection. The tensor-network section is not formalized: copy-context normal form, Hopf identities, copy-tensor rank and low-copy-debt compiler.

## Sources

Rewritten from the following internal notes (document numbers of the 27 October 2026 corpus review):
- #36 Diagonal Hack, Copy Context and Fanout Height (`old_stuff/Diagonal_Hack_Copy_Context_and_Fanout_Height_20260821.pdf`), all of it: Definitions 1-2, Theorem 3, Theorem 4, Definition 5, Corollary 6, Theorem 7, Lemmas 8-9, Theorem 10, Definition 11, Theorem 12, Corollary 13, Definition 14, Theorem 15, Sections 9-10, Theorem 16, Conjecture 17 (pp. 1-10).

## Status

Proved in full: the fanout-height compiler, the equality-assisted height bound, a search over the rank K giving depth O((Psi+1)log^2 n) (added; the source did not say how to find the best K), the copy-context normal form, the Hopf identities (standard identities of the group Hopf algebra, attributed to Sweedler), the exact rank of the copy tensor, and the low-copy-debt compiler. A small new observation: for Sequential NOR instances the fanout height equals the number of distinct parent indices, so the height refinement gives nothing beyond the fanout-kernel compiler there; this is what the title's reference to Sequential NOR covers, while the other results concern general finite-domain and A5 programs.

As agreed, the tensor/Hopf programme of the source (Theorems 15-16, Conjecture 17 and the discovery programme) is presented only as remarks and open problems. The source's claim that the height deficit can be exponentially smaller than the number of fanout classes is replaced by a linear-gap example. Without rewrites the low-copy-debt compiler is weaker than the fanout-kernel compiler; the paper says so.

Checks: the fanout statements on random A5 programs, the Sequential NOR proposition on 2000 random instances, the Hopf identities on basis vectors, and the rank of the flattened copy tensor. The brute-force scripts used for the checks are not part of this repository. Not refereed.

## Code

Checking scripts used for this manuscript are in [`verification/`](verification/): `a5lib.py`, `fanout_checks.py`, `seqnor_check.py`. They are plain Python 3 with no dependencies outside the standard library unless the script says otherwise.
