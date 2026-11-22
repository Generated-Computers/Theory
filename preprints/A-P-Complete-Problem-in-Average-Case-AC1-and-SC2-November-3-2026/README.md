# [A P-Complete Problem in Average-Case AC¹ and SC²](paper.pdf)

**Author:** Generated Computers

**Date:** November 3, 2026

## Citation

```bibtex
@misc{GC:A-P-Complete-Problem-in-Average-Case-AC1-and-SC2-November-3-2026,
  author = {{Generated Computers}},
  title = {{A P-Complete Problem in Average-Case $\mathrm{AC}^1$ and $\mathrm{SC}^2$}},
  howpublished = {Generated Computers preprint, manuscript 001c},
  year = {2026}
}
```


## Lean

Part of this paper is formalized in Lean 4 with Mathlib, in the [Lean library](../../lean/README.md). The scope is described in [`lean/docs/001.md`](../../lean/docs/001.md), and the main statements are in the Comparator challenge [`RandomSeqNORKleenePrefix.lean`](../../lean/ComparatorChallenges/RandomSeqNORKleenePrefix.lean). Every listed theorem is proved without `sorry` and uses only the axioms `propext`, `Quot.sound` and `Classical.choice`. Complexity-theoretic conclusions (logspace, NC, P-completeness and the like) are not formalized.

*A P-Complete Problem in Average-Case AC1 and SC2 (001c).* The formalization proves the following.
- The reset decomposition $x^*_i=x^*_{\varrho(i)}\oplus((i-\varrho(i))\bmod2)$.
- The Kleene–prefix iteration of Definition 3.1, defined explicitly. Lemma 3.2 is proved in full: $K_t=\{i:d(i)\le t\}$, and the recorded values are the trace. Hence the iteration succeeds after $R$ rounds exactly when $\max d\le R$.
- Dependency chains, with the deterministic first step of Theorem 3.4. If $d(i)\ge L+1$ there is a chain of length $L$ along which the depth drops by one per step. So, if no chain of length $L$ stays at positions $\ge g_0\ge1$, the iteration knows every position after $L+g_0-1$ rounds.
- The threshold algebra. Admissible $\eta,\lambda$ with $\theta<1$ exist iff $\varepsilon>(\sqrt{17}-1)/4$ (Theorem 3.4). The limit equation of Lemma 3.5 gives $\varepsilon\ell^*=(2+\varepsilon-\sqrt{4+4\varepsilon-3\varepsilon^2})/2$. Also $\varepsilon\ell^*>1-\varepsilon$ iff $\varepsilon>(1+\sqrt{13})/6$ (Theorem 3.6), and $\varepsilon\varpi(\varepsilon)>1-\varepsilon$ iff $\varepsilon>3/4$, with $\varpi(3/4)=1/3$ (Theorem 3.9).

The relevance-pruned iteration and Lemmas 3.11 and 3.12 are formalized, in the file of the fourth paper (see below). The following are not formalized: the density lemmas (3.3, 3.5 beyond the limit equation, 3.8), the probability bounds of Theorems 3.4, 3.6 and 3.9 (Steps 2–5), the AC$^0$ implementability of a round, and Corollaries 3.15–3.16 (average-case AC$^1$ and SC$^2$, $\varepsilon_c\le3/4$).

## Sources

This manuscript is not rewritten from the 27 October 2026 corpus. It is the existing paper below,
converted into the Generated Computers template on 3 November 2026. The statements, proofs,
constants, tables, captions and status disclosures are unchanged.
- `random-seqnor-newton/papers/3-kleene/paper.tex` (companion paper III of the 2 November 2026
  split, with the fixes of 3 November 2026).
- It was carved from the combined paper `random-seqnor-newton/paper/paper.tex`: the section on
  the Kleene–prefix iteration (lines 1736–2401: resets and the iteration, density of ones in
  smoothed instances, the round bound, the sharper density bound, the relevance-pruned iteration)
  and its consequences (2630–2729), with the setting, the smoothing definitions (1291–1333) and the
  density results (1159–1199) it uses, the numerics (2969–3134), the discussion of the upper end of
  the noise threshold, and the verification record (3525–3651). Line numbers are those of
  2 November 2026.
- Scripts: [`verification/random-seqnor/`](verification/random-seqnor/) (`kp_check.py`, `kp_constants.py`,
  `kp_density.py`, `kpr_check.py`, `kpr_witness.py`, `kpr_meanfield.py`, `kp_greedy.c`,
  `kpr_relax.c`, the `kp*_runall.sh` drivers and their `.out` files).

What the conversion changed: the preamble (gcams), the bibliography (BibTeX, author-year), the
citation commands, one sentence of the related-work section that called the cited notes
"unpublished notes" (now "other manuscripts of this collection"), one sentence in the numerics
appendix giving the location of the scripts, and the date. Citations of the earlier internal
notes now point to the manuscripts of this collection that contain the cited content
(P-completeness: 006a; structural compilers: 006f, 009c, 006a, 006c; greedy MIS form and cut
externalization: 011b; the reset-set iteration: 006b, and its measurements: 006c). Section
numbers of those notes were dropped from the citations.

## Status

- Proved in full: for every ε > 3/4 and every base, the Kleene–prefix iteration (rounds in AC⁰)
  finishes in O_ε(log n) rounds with probability at least 1 − 2/n on the ε-smoothing of the base.
  The proof has explicit constants above ε_K = (√17 − 1)/4 ≈ 0.7808 (35.1 ln(n + 1) + 244 rounds on
  uniform instances), a sharper threshold ε_B = (1 + √13)/6 ≈ 0.7676, and the threshold 3/4 with
  astronomical constants. Consequences: errorless average-case AC¹ with failure 2/n, and
  polynomial time with O(log² n) space and failure O(1/n), on uniform instances; ε_c ≤ 3/4. The
  relevance-pruned variant is never slower, and a switch characterisation describes both depths.
- Not refereed by any reviewer: part (b) of the limiting-density lemma, which shows that density
  bounds cannot go below 3/4, was written after the last (seventh) automated review.
- Checks: the section on the iteration was refereed by a fourth automated reviewer, the sharper
  threshold and the relevance-pruned iteration by a fifth, and the limiting-density lemma, the
  switch characterisation, the threshold-3/4 theorem and the remark on the relevance-pruned
  iteration by a sixth and a seventh (Appendix B; reviewers numbered as in the combined paper).
  The composition lemma was refereed by a third reviewer with the hardness results of 001b.
  Scripts check the lemmas and constants.
- Fixed on 3 November 2026: in the corollary on uniform instances, the abort threshold is
  (n + 1)^{λ′ + 2}, with λ′ the exponent of the call bound; the ε-scan paragraph of the appendix
  now gives the per-base counts behind the ratio 4.6 to 10.6.
- Heuristic or numerical only: the remark on what a proof for the relevance-pruned iteration below
  3/4 needs, the conjecture that it works for every ε > 0.6, and the empirical threshold between
  0.45 and 0.55.

Not refereed. No human referee has checked it yet; the proofs were developed with the assistance
of an AI system.
