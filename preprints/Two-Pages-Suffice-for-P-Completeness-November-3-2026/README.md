# [Two Pages Suffice for P-Completeness](paper.pdf)

**Author:** Generated Computers

**Date:** November 3, 2026

## Citation

```bibtex
@misc{GC:Two-Pages-Suffice-for-P-Completeness-November-3-2026,
  author = {{Generated Computers}},
  title = {{Two Pages Suffice for P-Completeness}},
  howpublished = {Generated Computers preprint, manuscript 006a},
  year = {2026}
}
```



## Lean

Part of this paper is formalized in Lean 4 with Mathlib, in the [Lean library](../../lean/README.md). The scope is described in [`lean/docs/006.md`](../../lean/docs/006.md), and the main statements are in the Comparator challenge [`TwoPagesSufficeForPCompleteness.lean`](../../lean/ComparatorChallenges/TwoPagesSufficeForPCompleteness.lean). Every listed theorem is proved without `sorry` and uses only the axioms `propext`, `Quot.sound` and `Classical.choice`. Complexity-theoretic conclusions (logspace, NC, P-completeness and the like) are not formalized.

**006a (Two pages).** We define alternating-direction NOR/OR arrays (Definition 7.1) with the six cell types and their sources. We define the serpentine instance $\Phi$ of Section 7.4 exactly as in the paper: constant blocks, one 8-position block per cell (Table 2) at $c(t,s)=2+2k+8(k(t-1)+e)$, and the tail. We prove that $\Phi$ is a parent array, that $x_{o(t,s)}=v(t,s)$ for every cell and $x_n=v(d,s_{\mathrm{out}})$ (Lemmas 7.6 and 7.7), and that the paper's explicit page assignment is a valid two-page assignment, so $\mathrm{pg}(\Phi)\le2$ (Lemmas 7.8–7.10, Theorem 7.11). The slot programs of Lemma 7.3 and the three-column gadgets of Table 1 are also formalized. We prove the gadget values and the claim that no cell reads outside its three columns (Lemma 7.4). We prove that the array built from a NOR circuit computes $w_G$ at cell $(d,2G)$ (Lemma 7.5). Together these give the end-to-end statement: for every NOR circuit, the resulting parent array has page number at most 2 and last trace bit $w_G$. Also formalized: Okhotin's five-cell reduction (Lemma 3.2, Theorem 3.3), the key step of Corollary 3.4 (with the dummy gate, $j_i\ne i-1$ for all $i\ge2$), Lemma 2.1, and the algebraic part of Proposition 7.2 (parity normalization turns NOR-only arrays into monotone OR/AND circuits). Of Proposition 7.2 we also prove the order-preserving layout of the wires. Not formalized: the logspace computability of all maps, the P-completeness and NC conclusions, planarity as a graph-theoretic notion and the Delcher–Kosaraju theorem, the instruction count $O(G^2)$, Proposition 5.1 (NP-completeness of $\mathrm{pg}\le k$), the one-page results of Section 6, and the live-width bound of Section 4.

## Sources

Rewritten from the following internal notes (document numbers of the 27 October 2026 corpus review):
- #24, "seqnor (2): base note" (`seqnor (2).pdf`), all sections: P-completeness gadget
  (Theorem 2.4), live width (Theorem 5.2), page-number dichotomy (Lemma 6.2, Theorem 6.3,
  Lemma 6.4, Lemma 6.6, Theorem 6.7), compression problem (Theorem 3.2, as a remark only),
  Open Problems 7.1-7.3.
- #25, "Nine Attacks on P ⊆ quasiNC" (`nine_attacks_quasiNC_with_addenda.pdf`),
  Proposition B.1, for the O(w + log n) space form of the live-width bound.

## Status

- **New in this rewrite:** the two-page theorem (Theorem 7.11). On 3 November 2026 an
  independent automated referee rewrote the construction from the paper and verified it
  by computer: all NOR circuits with G <= 4 (brute force, about 3.2·10^11 arc pairs),
  adversarial families up to n = 391,097, 720 random arrays and all small arrays, with
  0 value mismatches and 0 same-page crossings; the crossing graph was always bipartite,
  and mutated constructions were caught. No human referee has checked it. Sequential NOR on instances with page number at most 2 is P-complete under
  logspace reductions. With the one-page result this answers the source's Open Problem 7.1.
  The four-page statement of the source is now a corollary (Corollary 7.12).
- **Correction: Lemma 6.6 of the source is false as stated unless P = NC.** It claims
  that alternating-direction arrays with one NOR gate per cell are P-complete. Complement
  the odd layers, and such an array becomes a planar monotone circuit (odd layers OR or
  copy, even layers AND or copy). Planar monotone circuits can be evaluated in NC
  (Delcher and Kosaraju 1995), so these arrays are in NC (Proposition 7.2). The source
  checked its four-page bound only on this family.
- **Fix:** cells may also compute OR. One 8-position block (Table 2) yields NOR at its
  fifth position and OR at its sixth. Explicit three-column gadgets for SWAP, COPY and NOR
  (Table 1, checked by hand in Lemma 7.4) make these arrays P-complete. If each binary block
  reads its own column through its first parent and its neighbour through its second, the
  arcs into one layer are pairwise non-crossing (Lemma 7.9). This gives two pages.
- **Page numbers as promise problems:** for fixed k >= 4, deciding pg(j) <= k is
  NP-complete (Proposition 5.1, via Unger 1988 on circle-graph colouring). For k = 3 the
  complexity of recognition is open (Unger's 1992 polynomial-time 3-colouring algorithm
  for circle graphs has been argued to be incorrect). So the k-page statements for k >= 3
  are made with the page assignment given or as promise problems. For k = 2 the plain
  restricted language is in P and is P-complete.
- **One page:** stated as known. One-page instances are outerplanar (treewidth at most 2),
  so they are in L by Elberfeld, Jakoby and Tantau (FOCS 2010) (Theorem 6.1). The source's
  stack argument is kept as an elementary proof of the weaker bound LOGDCFL.
- **Attribution:** P-completeness of Sequential NOR is due to Okhotin (MCU 2007,
  TCS 2011). The source did not cite it. The five-cell proof is kept as a self-contained
  proof of his theorem. The restricted Lfmis corollary (Corollary 3.4) now inserts a dummy
  first gate, because without it j_2 = 1 = 2 - 1 can occur (referee's correction).
- Other changes. The live-width bound is stated with space O(L + log n), as in #25 B.1.
  The source's O(L log n) does not support its logspace claim. The compression
  equivalence (source Theorem 3.2) is a remark only. Proposition 3.3 and the "seven faces"
  and counting discussions of the source are omitted, and so is its unchecked claim of
  AC0 uniformity. Open Problem 7.3 (random instances) is now answered by manuscript 001c.
- Computer checks are in [`verification/`](verification/README.md): 300 compiled circuits, 450 random
  arrays, sweep and naive pairwise crossing checks, and value checks at every block. The
  proofs do not depend on them.
- Not refereed.
