# [Prefix OR Defeats Treewidth and Curvature Measures](paper.pdf)

**Author:** Generated Computers

**Date:** November 3, 2026

## Citation

```bibtex
@misc{GC:Prefix-OR-Defeats-Treewidth-and-Curvature-Measures-November-3-2026,
  author = {{Generated Computers}},
  title = {{Prefix OR Defeats Treewidth and Curvature Measures}},
  howpublished = {Generated Computers preprint, manuscript 009e},
  year = {2026}
}
```


## Lean

Part of this paper is formalized in Lean 4 with Mathlib, in the [Lean library](../../lean/README.md). The scope is described in [`lean/docs/009.md`](../../lean/docs/009.md), and the main statements are in the Comparator challenge [`PrefixORWidthCounterexamples.lean`](../../lean/ComparatorChallenges/PrefixORWidthCounterexamples.lean). Every listed theorem is proved without `sorry` and uses only the axioms `propext`, `Quot.sound` and `Classical.choice`. Complexity-theoretic conclusions (logspace, NC, P-completeness and the like) are not formalized.

**Prefix-OR defeats treewidth and curvature measures (009e).** Formalized are: the masking
bijection with its explicit inverse and the invariance of mixed derivatives (Lemma 6.1); for
masked prefix OR, `⋁_{i≤e} y_i = ⋁_{i≤e} x_i`, `y_e = x_e ⊕ ⋁_{i<e} x_i` and the completeness of
the curvature hypergraph (Theorem 6.2, without the `NC¹` claim); the correctness of the
zero-mask reduction behind Theorem 6.3 (not P-completeness itself); for the reverse-prefix
family, `z_r = z_1 ∨ z_2` for `r ≥ 3` and an explicit `K_{k,k}` minor model in the moral graph,
`k = ⌊(h-1)/2⌋` (Theorem 4.1) — treewidth is not in Mathlib, so `tw(K_{k,k}) = k`, minor
monotonicity, the `Ω(√n)` bound and the record count are not formalized; for the triangle grid,
the record count `3r² + 4r`, every vertex cover of the moral graph has at least `2r²` vertices,
and the edges `A_iB_j` form a `K_{r,r}` (Theorem 4.2; the treewidth consequence is not
formalized). Replay (Proposition 2.1), relation fusion (Proposition 3.1), Propositions 5.1–5.2 and
all complexity statements are not formalized.

## Sources

Rewritten from the following internal notes (document numbers of the 27 October 2026 corpus review):
- #11 Source-Replay Transfer Width V126 (`SOURCE_REPLAY_TRANSFER_WIDTH_V126_2026_09_04.pdf`), all
  sections: Theorem 2.1, Corollary 2.2, Theorem 3.1, Theorems 4.1, 4.3, Proposition 4.4,
  Theorem 5.1, Corollary 5.2, Lemma 6.1, Theorems 6.2–6.3; pp. 2–7.
- Check script: `verification/masked_prefix_or_check.py` (the masked prefix-OR identities for m ≤ 11).

## Status

- Proved in full: replay with arbitrary overrides in linear size; the reverse-prefix family (one-pointer
  forest, K_{k,k} minor, treewidth Ω(√n), while computing z_1 ∨ z_2); the grid of disjoint moral
  triangles (vertex covers of density 2/3, a K_{r,r}); the support-three property of moral covers;
  the literal-binary closure criterion; the masking bijection; masked prefix OR in NC^1 despite
  complete curvature; P-completeness of masked evaluation.
- Known, with a proof sketch: the relation-fusion evaluator on a supplied tree decomposition
  (attributed to the literature on bounded-treewidth evaluation: Jansen–Sarma, Elberfeld–Jakoby–
  Tantau, with tree contraction of Miller–Reif); the source imports it from an earlier note.
- Left out: the conditional hereditary half-wave compiler (#11 Theorem 5.3), which assumes
  certificates and decoders that are not constructed, and the proposed "causal transfer width"
  target, which is mentioned in one sentence without claims.
- Clarified: the one-pointer graph of every program is a forest, so "pointer width one" holds
  trivially; the reverse-prefix family shows that it does not control the moral graph.
- These are counterexamples to proposed measures, not lower bounds.

Not refereed. No human referee has checked it yet; the proofs were developed with the assistance
of an AI system.
