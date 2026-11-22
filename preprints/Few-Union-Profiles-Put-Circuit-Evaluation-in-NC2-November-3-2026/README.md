# [Few Union Profiles Put Circuit Evaluation in NC²](paper.pdf)

**Author:** Generated Computers

**Date:** November 3, 2026

## Citation

```bibtex
@misc{GC:Few-Union-Profiles-Put-Circuit-Evaluation-in-NC2-November-3-2026,
  author = {{Generated Computers}},
  title = {{Few Union Profiles Put Circuit Evaluation in $\mathrm{NC}^2$}},
  howpublished = {Generated Computers preprint, manuscript 007d},
  year = {2026}
}
```


## Lean

Part of this paper is formalized in Lean 4 with Mathlib, in the [Lean library](../../lean/README.md). The scope is described in [`lean/docs/007.md`](../../lean/docs/007.md), and the main statements are in the Comparator challenge [`FewUnionProfiles.lean`](../../lean/ComparatorChallenges/FewUnionProfiles.lean). Every listed theorem is proved without `sorry` and uses only the axioms `propext`, `Quot.sound` and `Classical.choice`. Complexity-theoretic conclusions (logspace, NC, P-completeness and the like) are not formalized.

*Few union profiles (007d).* The formalization proves absorbing elimination (Lemma 2.2) for tagged absorbing systems with arbitrary exception values. For exception-port systems it proves the composition lemma of the union-profile compiler (Lemma 3.2): both child inputs lie in the union closures, the child runs reproduce the run of the parent, and the response identity `ρ_I(α) = u_L|_{after I} ∨ u_{R'}` holds. It also proves that the root run on `0` is the true computation, and that the true contribution vector at every interval lies in `𝒰(A^in_I)` and reproduces the true values. It proves the three union-closure bounds of Proposition 4.1 and the matching example (`|𝒰(I_w)| = 2^w`, Example 4.3). The capped closure enumeration, the circuit construction of Theorem 3.3 and all depth bounds, the reduction to port systems as a circuit, and the nested example are not formalized.

No statement about NC, logspace uniformity or circuit depth is formalized.

## Sources

Rewritten from the following internal notes (document numbers of the 27 October 2026 corpus review):
- #05, 30-Page Most Important Results (`SEQNOR_30_PAGE_MOST_IMPORTANT_RESULTS_2026_09_07.pdf`), Chapter 8 (pp. 26-27): absorbing regular regions and exception ports, Lemma 8.1, Lemma 8.2, Theorem 8.3 (UFR-20), Section 8.5. The `.tex` file of #05 includes its chapters from files that are not in the corpus, so the PDF was used.
- #03, Sequential NOR to SC full compendium (`Sequential_NOR_to_SC_Full_Research_Compendium_Draft.pdf`), Component 2 (pp. 177-192), in particular pp. 181-183 (exception-port normal form, Theorem UFR-20, carrier construction, parent/child compatibility, the nested and matching examples) and pp. 184-185 (UFR-12, UFR-14, UFR-15).
- #16, Best Post-Corpus Results (`BEST_POST_CORPUS_SEQNOR_RESULTS_2026-09-02.pdf`), pp. 4-6, which states the same theorem; its proofs live in files that were not supplied, and it was used only for orientation.

## Status

The source proofs (#05 p. 26-27, #03 pp. 181-183) are sketches; this paper completes them. Proved in full: elimination of regular (absorbing) gates by one reachability computation, the reduction to an exception-port system, capped parallel enumeration of union closures, the composition lemma, and the union-profile compiler (for fixed C, the promise nu_cut <= (N+2)^C is recognized and the full trace is computed in logspace-uniform depth O(log^2 N)); the bounds of the union closure by distinct rows, distinct columns and missing-set size; the nested example with nu_cut = O(sqrt N); the matching example with exponential nu_cut.

The tagged model is defined here from the description in #05 (regular rule V = Y or AND of predecessors; bounded-arity exceptions); the source's "explicitly tagged UFR-14 system" is not defined in full in #03 or #05. As the review noted, the relation of the tagged model to raw Sequential NOR is not given in the sources: Sequential NOR is the special case in which every gate is an exception, and there the promise reduces to a bound on the number of values crossing each canonical cut (Remark 4.4). The paper states this scope explicitly.

Stated without proof (Remark 4.5, clearly marked): the reuse-height ladder (UFR-14), the reconvergence-treewidth compiler (UFR-15) and the barrier statements (INDEX, full transformation monoid), whose proofs are not in #03 or #05. The co-singleton and fixed-missing-set compilers (UFR-18, UFR-19) and the literal-row and column-atom compilers (UFR-16, UFR-17) appear only through the bounds of Proposition 4.1, which make them special cases. Not refereed.
