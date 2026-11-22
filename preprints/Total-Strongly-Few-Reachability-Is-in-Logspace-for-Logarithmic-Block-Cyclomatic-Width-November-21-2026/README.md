# [Total Strongly-Few Reachability Is in Logspace for Logarithmic Block-Cyclomatic Width](paper.pdf)

**Author:** Generated Computers

**Date:** November 21, 2026

## Citation

```bibtex
@misc{GC:Total-Strongly-Few-Reachability-Is-in-Logspace-for-Logarithmic-Block-Cyclomatic-Width-November-21-2026,
  author = {{Generated Computers}},
  title = {{Total Strongly-Few Reachability Is in Logspace for Logarithmic Block-Cyclomatic Width}},
  howpublished = {Generated Computers preprint, manuscript 012d},
  year = {2026}
}
```

## Lean

This manuscript is not formalized yet.

## Sources

Rewritten from the following internal note:
- "Total Strongly-Few Directed Reachability: Unambiguity, Auxiliary Pushdowns, Exact Counting,
  and the StrongFewL Boundary" (`STCONsf_Class_Containments_Revised.pdf`, 9 September 2026,
  72 pp.). Used: Appendices A18 (Theorem A18.1, Corollary A18.2, Lemma A18.3, Theorem A18.4,
  Corollary A18.5), A19 (Lemmas A19.1, A19.2, Corollary A19.3, Theorem A19.4, Remark A19.5),
  A20 (Theorem A20.1, Corollary A20.2), A21 (Theorem A21.1, Remark A21.2, Theorem A21.3), A22
  (Theorem A22.1, Corollaries A22.2, A22.3), A13 (path flow, Theorem A13.1, deletion), A14
  (as a remark), A15 (as Proposition 7.3), A24 (Propositions A24.1, A24.3, Caution A24.2);
  the fail-closed caps of Section 3 (Lemmas 3.3-3.6) and the boundary conventions of A36. The
  block product theorem A17.1 is replaced by a route lemma proved here.

## Status

- **Main results, proved in full.** For b = bcw(G), the largest cyclomatic number of a block of
  the underlying undirected graph, the total language STCON_sf is decidable in time
  2^{O(b)} M^{O(1)} and space O(b + log M) (Theorem 6.3); hence it is in L on inputs with
  b = O(log M) (Corollary 6.4). For λ = min(#sources, #sinks), it is decidable in polynomial
  time and space O(kλ + log M) (Theorem 3.4), so it is in L for kλ = O(log M) and in SC^d for
  kλ = O(log^d M). Bypass pruning gives polynomial time and space O((γ+1) log M), with γ the
  largest cycle rank of a weak component (Theorem 4.6). All algorithms are fail-closed: they
  reject cyclic, over-budget and malformed inputs within the stated bounds, and the parameters
  are computed from the input, not given.
- **New in this rewrite.** The compact choice string (Lemma 3.3): the choices of the
  depth-first search fit in at most L_a - 1 <= kλ - 1 bits, instead of one O(log M)-bit frame
  per choice point. This improves source Theorem A18.4 from O((kλ+1) log M) to O(kλ + log M)
  space and source Corollary A18.5 from "kλ = O(log^{d-1} M) gives SC^d" to "kλ = O(log^d M)
  gives SC^d". An adaptive-cap variant (Remark 3.6) uses O(ℓ + log M) space on valid inputs,
  where ℓ is the largest number of maximal walks from a vertex. The route lemma (Lemma 6.2),
  proved for the block-cut structure of the whole graph, with a logspace block test via
  Menger's theorem (Lemma 6.1). The functional versions are derived uniformly from a count
  oracle (Proposition 7.3, Corollary 7.4).
- **Imported.** Reingold 2008 (undirected connectivity in L); Elberfeld-Jakoby-Tantau 2010
  (logspace Courcelle, with its cardinality version); standard block and cycle-space facts
  (Diestel); Menger's theorem. Quoted from companion manuscripts and not used: STCON_sf is in
  ReachUL and LOGDCFL, budget-mass truncation, and acyclicity with C = (I-A)^{-1} (reproved in
  two lines as Lemma 2.2).
- **Corrections and changes to the source.**
  - Theorem A21.1 of the source derived the product formula N_G(u,v) = prod r_i from Theorem
    A17.1, which is stated for a live interval G[I(s,t)] of a DAG. The algorithm applies it to
    the block-cut tree of the whole underlying graph, where it needs a separate proof. Lemma 6.2
    proves it, for directed simple paths in any loopless digraph without antiparallel pairs. It
    also makes the logspace navigation precise: the separators of u,v, their order, and the
    unique block containing consecutive separators.
  - Lemma A19.2 of the source used "every later cycle avoids v_i", which needs the active choice
    vertices to be distinct. On DAGs this holds because the current walk is a path. Lemma 4.3
    shows it on every loopless input, since an admissible move never enters an active choice
    vertex. So the cycle-rank stack bound (Corollary 4.5) also covers the cycle-detection phase
    on cyclic inputs. The admissibility condition now states w ∉ S ∪ {v} and the case v = t.
  - Theorem A19.4's bound O((1 + min{γ, kλ}) log M) is correct but superseded by
    O(log M + min{kλ, γ log M}) (Corollary 4.7), using Theorem 3.4.
  - Remark A21.2 illustrated bcw < γ by a serial chain of diamonds. Such a chain with c diamonds
    has 2^c paths, so it is valid only for k >= 2^c; the "diamond comb" (Remark 6.6) gives the
    separation on valid inputs with k = 2. Remark 6.6 also adds valid families with k = 2 and
    λ = 1 whose bcw is linear and whose treewidth is unbounded, so the three parameters are
    pairwise incomparable except bcw <= γ.
  - Theorem A20.1's connectivity check of the selected edges (via Reingold) is replaced by
    following the selected arcs from x (Lemma 5.2). Loops and antiparallel pairs are rejected
    before the block algorithm, since a simple underlying graph loses 2-cycles.
  - Theorem A21.3 (live-corridor extractor) is now Corollary 7.4, computed from the count
    oracle instead of mixed-radix tuples of local ranks. Its kernel size bounds rest on
    source Corollary A10.2, which belongs to another manuscript of this family, and are omitted.
- **Prior work now attributed.** The constant-parameter cases of Theorem 6.3 and Corollary 5.5
  follow from the logspace Courcelle theorem with its cardinality version
  (Elberfeld-Jakoby-Tantau, FOCS 2010), since tw(G) <= bcw(G) + 1 (Remark 6.5). The rank-one
  update A13.1 is the Sherman-Morrison formula and was used by King and Sagert (JCSS 2002) for
  dynamic transitive closure (Proposition 7.2). The unique-signature search barrier A24.1 is the
  standard promise-UL-completeness of unique-path reachability on DAGs (Proposition 8.3). For
  super-constant parameters we found Theorems 3.4, 4.6 and 6.3 nowhere in the literature, but
  their ingredients (fundamental cycle bases, Reingold's theorem, depth-first search with
  compressed stacks) are standard.
- **Left out.** The ReachUL-completeness claims of A14.1 for designated unitriangular inverse
  rows, which depend on a rooted-budget theorem of a companion manuscript; the alternative
  routes of A15 through the AuxPDA recounting, the NL fingerprint census and the certified
  ReachUL lift (other manuscripts of this family); the kernel size bounds of A21.3.
- **Robustification.** Theorem A22.1 and Corollaries A22.2-A22.3 are kept as Theorem 8.1 and
  Corollary 8.2. We checked every case of the proof, including the diameter. What is preserved:
  for every ρ >= 2, all walk counts between {u} ∪ A_u and {v} ∪ B_v for original u, v
  (infinite ones included), validity for every k >= 1, the s-t walks and the live interval. All
  other pairs have at most one walk. The construction also destroys all three parameters of the
  paper, so it is a barrier to replacing them by undirected connectivity, not a lower bound.
- **Computer checks** are in [`verification/`](verification/README.md). They implement the
  three deciders as stated, the signature counter, the block test, the route product, the
  robustification and the update formulas, and compare them with brute-force walk counts on all
  digraphs with up to 4 or 5 vertices (cyclic and acyclic) and on random ones. They also
  measure stack sizes against the bounds. There were 0 errors. The proofs do not depend on them.
- Not refereed.
