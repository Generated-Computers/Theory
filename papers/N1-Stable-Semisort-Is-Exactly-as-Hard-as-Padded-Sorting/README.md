# [Stable Semisort Is Exactly as Hard as Padded Sorting](paper.pdf)

**Author:** Generated Computers

**Date:** November 24, 2026

## Citation

```bibtex
@misc{GC:paper-N1,
  author = {{Generated Computers}},
  title = {{Stable Semisort Is Exactly as Hard as Padded Sorting}},
  howpublished = {Generated Computers, 2026},
  year = {2026}
}
```

## Abstract

A stable semisort rearranges records so that records with equal keys are contiguous and keep their input order. We give a complete proof of a short reduction: an unstable semisort, one padded sort of $`n`$ distinct integers below $`(n+1)^2`$, and $`O(n)`$ work and $`O(\log n)`$ depth of scans together give a stable semisort, with additive costs. We then show that this reduction does not close the problem. Sorting $`n`$ distinct integers below $`(n+1)^2`$, stable sorting of integer keys in $`[0,n]`$, stable semisort and colored prefix ranks are mutually reducible with $`O(n)`$ work and $`O(\log n)`$ depth, and unstable semisort is needed in only one direction. So, given a work-efficient unstable semisort, stable semisort has an algorithm with linear work and polylogarithmic depth if and only if the padded sort used by the reduction has one: the reduction replaces stable semisort by a problem equivalent to it. We state the assumptions on word size, machine model and failure probability that each statement needs. We also prove two facts about approximate within-group ranks. For monotone labels, the prediction-alignment error equals the collision energy. Labels built from random anchors of density $`1/2`$ have collision energy at most $`3n`$ with high probability. Conversely, any labeling of a group of size $`f`$ with at most $`k+1`$ distinct values has collision energy at least $`\tfrac12(f^2/(k+1)-f)`$.

## Main results

All statements are proved in full; nothing is conditional except on the stated black boxes.

- Theorem 3.1 (closure reduction): unstable semisort + `PaddedSort(n,(n+1)^2)` + $`O(n)`$ work, $`O(\log n)`$ depth give a stable semisort, costs and failure probabilities additive. Proved in full (Lemmas 3.2–3.5; Corollary 3.7 is the conditional linear-work consequence).
- Theorem 4.1 (equivalence): DS, IS, SS and CPR are mutually reducible; only SS ⪯ IS uses an unstable semisort. Proved in full.
- Corollary 4.3 (the reduction is circular): given a work-efficient unstable semisort, stable semisort meets the target iff padded sorting does. Proved in full.
- Proposition 5.2 (radix restoration): $`O(n/\varepsilon)`$ work and $`O((n^\varepsilon+\log n)/\varepsilon)`$ depth after group discovery. Proved in full.
- Lemma 6.2 (PAE = collision energy for monotone labels). Proved in full.
- Proposition 7.1 and Theorem 7.2 (random anchors: expected energy below $`n`$, energy at most $`3n`$ w.h.p.). Proved in full.
- Theorem 7.3 (density barrier). Proved in full.

## Consolidated from

| Preprint | Sections of this paper |
|---|---|
| [Stable Semisort Is Exactly as Hard as Padded Sorting](../../preprints/Stable-Semisort-Is-Exactly-as-Hard-as-Padded-Sorting-November-3-2026/paper.pdf) | all (Sections 1–7, Appendix A) |

## Lean

Family [011 semisort](../../lean/docs/011.md): both directions of the equivalence are formalized as explicit transformations with correctness proofs (Theorem 3.1 with Lemmas 2.4, 3.2–3.5, the reductions of Theorem 4.1 except the CPR part (d)), together with the collision-energy identity (Lemma 6.2) and the density barrier (Theorem 7.3). Costs (work, depth, space, write exclusivity, failure probabilities), hence Corollaries 3.7 and 4.3, and Section 5, Proposition 7.1 and Theorem 7.2 are not formalized.

## Notes on the merge

- This is a revised version of a single manuscript; no material from other manuscripts was merged in, and there were no citations of other Generated Computers preprints.
- Removed: the status footnote (replaced by the standard acknowledgement), the "Organization" subsection, a TODO comment, and the sentences that referred to the internal "source note(s)" (in Section 1, Remark 4.2, Section 5.2, Section 6 and Remark 7.4); each was rephrased to state only what this paper does or does not use or claim. No mathematical content changed.
- No mathematical errors were found.
- Build: no LaTeX errors, no undefined references, no overfull hboxes; one overfull vbox of about 1.1pt on page 1 (invisible).
