# [Barrington Gadgets Meet Strahler Rank](paper.pdf)

**Author:** Generated Computers

**Date:** November 3, 2026

## Citation

```bibtex
@misc{GC:Barrington-Gadgets-Meet-Strahler-Rank-November-3-2026,
  author = {{Generated Computers}},
  title = {{Barrington Gadgets Meet Strahler Rank}},
  howpublished = {Generated Computers preprint, manuscript 004g},
  year = {2026}
}
```



## Lean

Part of this paper is formalized in Lean 4 with Mathlib, in the [Lean library](../../lean/README.md). The scope is described in [`lean/docs/004.md`](../../lean/docs/004.md), and the main statements are in the Comparator challenge [`StrahlerGadgets.lean`](../../lean/ComparatorChallenges/StrahlerGadgets.lean). Every listed theorem is proved without `sorry` and uses only the axioms `propext`, `Quot.sound` and `Classical.choice`. Complexity-theoretic conclusions (logspace, NC, P-completeness and the like) are not formalized.

**004g (Barrington gadgets and Strahler rank).** The gadget identities (Lemma 3.2), NOT/AND
correctness with the multiplication-only AND (Theorem 3.3), and the linear Boolean-to-$A_5$
reduction with sharing preserved (Corollary 3.4). For circuits given by predecessor lists, the
Strahler rank satisfies $2^{\mathrm{sr}(v)}\le U(v)$ (Corollary 6.8, with the identity congruence and
no designated constants; $U$ counts unfolding nodes over distinct predecessors) and is monotone along
arcs; the quotient lemma (Lemma 6.1) is proved for straight-line programs. Not formalized: the
transfer theorem (Theorem 4.1), portal chains, the rank computation and the depth of the compiler.

## Sources

Rewritten from the following internal notes (document numbers of the 27 October 2026 corpus review):
- #29, *A5 Is the Strict Core: Constant-State P-Completeness and the Exact Reconvergence Frontier*
  (`old_stuff/A5_Strict_Core_and_Reconvergence_Frontier_20260820.pdf`), all of it: Theorem 1
  (cited dichotomy, p. 1), Lemma 2, Theorem 3, Corollary 4 (gadgets, pp. 2–3), Theorem 5 (strict
  transfer, p. 3), Definition 6, Theorem 7, Corollary 8 (portal chains, p. 4), Definition 9,
  Theorem 10, Corollary 11 (semantic Strahler compiler, p. 5), Section 6 (residual core, pp. 5–6).

## Status

- Proved in full: the gadget identities and the linear Boolean-to-A5 reduction (folklore, after
  Barrington 1989 and Beaudry–McKenzie–Péladeau–Thérien 1997, and presented as such); the
  portal-chain collapse and logarithmic A5 portals (parallel prefix composition); the semantic
  Strahler compiler with depth O((r+1) log² s), including the computation of the ranks (r+1
  reachability phases), and the unfolding bound r ≤ log₂ U.
- Corrected: source Theorem 5 claimed P ⊆ SP from an s^{1−ε}-depth A5 evaluator, and the box after
  it claimed an equivalence. The Pippenger–Fischer simulation is relative to multitape
  Turing-machine time, while SP (Kruskal–Rudolph–Snir) is relative to RAM time. The paper proves
  only the Turing-machine-time transfer (Theorem 4.1) and states the missing RAM-time hypothesis
  explicitly (Remark 4.2). The proof relies on the logspace uniformity of the Pippenger–Fischer
  network, which is not reproved.
- Made explicit: the certification cost hidden in source Theorem 10. The congruence is part of the
  input; the ranks of the quotient are computed within the stated depth; a proposed congruence is
  checked afterwards in constant depth (Proposition 6.6); finding a congruence that lowers the
  rank is not addressed (Remark 6.7). The quotient uses topologically first representatives, which
  keeps it acyclic (the source does not say how classes are merged).
- Added: the Strahler compiler subsumes the junction-depth compiler of the same batch (manuscript
  005g) and matches the cycle-packing compiler of 004e up to one log factor (Remark 6.9); the same
  rank layering is used in 002a and 002b, and a semiring Newton version is Esparza–Kiefer–Luttenberger
  2010.
- Checks: gadget identities by computer; rank computation by phases, layer-by-layer evaluation and
  the unfolding bound on 300 random circuits; the quotient construction on 200 random circuits.
- Left out: Conjecture 12 and Corollary 13 (a conditional restatement of the open problem whose
  conclusion P ⊆ SP also depends on the uncorrected transfer).

Not refereed. No human referee has checked it yet; the proofs were developed with the assistance
of an AI system.

## Code

Checking scripts used for this manuscript are in [`verification/`](verification/): `frucht_strahler.py`. They are plain Python 3 with no dependencies outside the standard library unless the script says otherwise.
