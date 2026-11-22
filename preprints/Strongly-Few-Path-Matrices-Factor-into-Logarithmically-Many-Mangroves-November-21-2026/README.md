# [Strongly-Few Path Matrices Factor into Logarithmically Many Mangroves](paper.pdf)

**Author:** Generated Computers

**Date:** November 21, 2026

## Citation

```bibtex
@misc{GC:Strongly-Few-Path-Matrices-Factor-into-Logarithmically-Many-Mangroves-November-21-2026,
  author = {{Generated Computers}},
  title = {{Strongly-Few Path Matrices Factor into Logarithmically Many Mangroves}},
  howpublished = {Generated Computers preprint, manuscript 012c},
  year = {2026}
}
```

## Lean

This manuscript is not formalized yet.

## Sources

Rewritten from the following internal note:
- "Total Strongly-Few Directed Reachability: Unambiguity, Auxiliary Pushdowns, Exact Counting,
  and the StrongFewL Boundary" (`STCONsf_Class_Containments_Revised.pdf`, 72 pages,
  9 September 2026). Used: Appendices A3 (Theorems A3.1, A3.3, Corollary A3.2), A4 (Lemma A4.1,
  Theorem A4.2, Corollary A4.3), A5 (Theorem A5.1, Corollary A5.2, Theorem A5.3), A6
  (Definition A6.1, Theorems A6.2, A6.3), A7 (Theorems A7.1, A7.2 and the separator skeleton),
  A8 (Theorem A8.1, Corollary A8.2, Theorem A8.3), A9 (Definition A9.1, Theorem A9.2,
  Corollary A9.3, Proposition A9.4, Caution A9.5, Problem A9.6), A10 (Theorem A10.1,
  Corollary A10.2, Proposition A10.3), A11 (Theorems A11.1, A11.3, A11.4, Proposition A11.2),
  A12 (Theorem A12.1, Proposition A12.2, Corollary A12.3, Caution A12.4), A16 (Theorems A16.1,
  A16.3, Remarks A16.2, A16.4), A17 (Theorem A17.1, Corollary A17.2, Theorem A17.3,
  Remark A17.4), and the open problems A35.6, A35.7, A35.8. The definitions of Section 2 of the
  note (walk convention, k-strong unambiguity) were also used.

## Status

- **New in this rewrite.**
  - *Level partition* (Theorem 5.3). The level sets of floor(log2 mu), where
    mu(v) = max_a N(a,v), form a monotone partition into at most floor(log2 k)+1 path-convex
    mangroves. A chain of floor(log2 k) diamonds needs that many classes (Theorem 5.4, the
    source's A6.3 made exact). So the bound is optimal for every k. The source had about
    2 log2 k blocks.
  - *Factorization* (Theorem 6.2). The path-count matrix of a simple k-strongly-unambiguous
    digraph is a product of at most 2 floor(log2 k)+1 mangrove factors. The source had fewer
    than 4 log2 k. Remark 6.3 gives the multigraph version; the source's multigraph remark only
    factored the matrix of the subdivided graph, which is not a factorization of the original
    matrix.
  - *Lower bound on factors* (Proposition 6.5). Entries of a product of f 0/1 matrices are at
    most n^(f-1), so the transitive tournament T_n (k = 2^(n-2)) needs at least
    1 + log k / log(log k + 2) factors. The source's diamond-chain bound A6.3 concerns
    path-convex block partitions only, not factor counts. Exhaustive search (Remark 6.6) gives
    least factor counts 2, 3, 2 for T_4, T_5, D_2.
  - *Equality case r = 2^c* (Theorem 8.8): it holds iff every block of the underlying graph is
    an edge or a cycle. This solves the source's Problem A9.6 / A35.7.
  - *Elementary proofs* of c+1 <= r <= 2^c by a vertex potential (Lemma 8.2), and of c <= k for
    minimal violations by a directed ear decomposition (Lemma 8.1, Theorem 10.4). The source
    used the unit-flow polytope; both arguments are given.
  - *Computer data*: |F_1| = 1, |F_2| = 7, |F_3| = 53 irredundant obstructions (Remark 10.7,
    partial answer to A35.8); exact ex_sf(n,k) for n <= 7 and for n = 8, k <= 6 (Table 1). The
    three-layer construction is optimal for k <= 3 in this range and not for k >= 4.
- **Imported.** Nothing. The classical facts used are reproved and attributed: McCabe's
  lower bound (IEEE TSE 1976), the addition-chain correspondence (Knuth, TAOCP vol. 2, 4.6.3;
  Knuth–Papadimitriou 1981), and the triangle inequality of Moon–Moser (1962) and
  Nordhaus–Stewart (1963). Block–cut-vertex trees are cited from Diestel.
- **Corrections to the source.**
  - A10.3(4) claimed pathwidth <= 3c+1 with an incomplete argument ("keeping one active
    position per kernel edge"). Proposition 10.3 proves pw(H) <= 2c+3 with an explicit path
    decomposition, which implies 3c+1 for c >= 2. The cases c <= 1 are checked directly.
  - A4.2's injectivity argument said acyclicity prevents vertex repetition "across the three
    pieces". The correct reason is that a path visits each vertex once, so the split vertices
    have unique positions (Lemma 2.1). The statement is unchanged.
  - A16.1/A16.3: the "repaired hypotheses" (d+(s) >= 2, d-(t) >= 2 after contracting forced
    chains) are the right ones and are kept; Remark 10.5 shows why they are needed and gives the
    uncontracted bounds 2k+2 and 3k+1. The finite-basis theorem is now proved with an explicit
    definition of F_k (k-cores), an explicit extraction, and an explicit count
    2^{O(k log k)}. The source's informal sketch of the converse direction was completed.
  - A6.2 and A5.3: the recursion count of the source (l(k) <= 2 l(floor(sqrt k)),
    l(k) <= 2 log2 k, 2l-1 < 4 log2 k factors, depth <= 1 + floor(log2 log2 k)) was checked by
    hand, including k = 2, 3, and by computer. It is correct and kept as Remark 5.6, but
    superseded by Theorems 5.3 and 6.2.
  - A12.3/A12.4 (weights): stated as in the source's corrected scope; all structural parameters
    refer to the expanded graph (Proposition 12.3).
- **Prior work now attributed.** McCabe 1976 (r >= c+1); Knuth TAOCP 4.6.3 and
  Knuth–Papadimitriou 1981 (addition chains as graphs); Zikan–Schmeichel 1985 (least number of
  edges for exactly r paths, a related problem); Moon–Moser 1962 and Nordhaus–Stewart 1963
  (triangle bound); Mantel 1907 (k = 1); Allender–Lange 1998 and Kannan–Khanna–Roy 2008 for the
  term mangrove; Furnas–Zacks 1994 (multitrees). The upper bound r <= 2^c is probably folklore.
  We did not find the level partition, the factorization, the two-sided inequality, the equality
  case or the minimal-violation bounds in the literature.
- **Left out.** Proposition A17.5 (second-path barrier): it is a promise-UL-hardness statement
  whose hardness rests on the UL-completeness of unique-path reachability, which is
  complexity-theoretic and outside this combinatorial paper. Remark A16.4 (Lean-friendly
  formulation): the definition of F_k in Section 10.3 is already of that form. A13–A15 and the
  rest of the source belong to companion manuscripts.
- **Computer checks** are in [`verification/`](verification/README.md): fixed points and
  budgets on all digraphs with at most 4 vertices; potentials, cuts, level partitions and both
  factorizations (multiplied back) on all 33,867 DAGs with at most 6 vertices and 300 random
  k-strongly-unambiguous graphs; sandwich, equality case, block product, chord signatures and
  kernels on 707,284 trimmed two-terminal DAGs; addition-chain constructions for r <= 128;
  minimal violations, extraction and the families F_1, F_2, F_3; exact extremal densities; and
  least factor counts for T_4, T_5, D_2. No check failed. The proofs do not depend on them.
- Not refereed.
