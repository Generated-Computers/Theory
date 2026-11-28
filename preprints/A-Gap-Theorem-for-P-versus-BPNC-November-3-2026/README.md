# [A Gap Theorem for P versus BPNC](paper.pdf)

**Author:** Generated Computers

**Date:** November 3, 2026

> **Superseded (24 November 2026; updated 28 November 2026).** Superseded by the consolidated paper [Sequential NOR on Random and Smoothed Instances](../../papers/1-Sequential-NOR-on-Random-and-Smoothed-Instances/paper.pdf) (Sections 7–12). There the hardness reaches every noise level up to 0.4468, not only 1/64, through a latch embedding (every level below 4/9) and an embedding with a design of period 24 (0.4468), and success probability n^(-K) already suffices. So, unless P ⊆ BPNC, the critical noise level lies in [0.4468, 0.7288], also at each level NC^k, k ≥ 2.

## Citation

```bibtex
@misc{GC:A-Gap-Theorem-for-P-versus-BPNC-November-3-2026,
  author = {{Generated Computers}},
  title = {{A Gap Theorem for P versus BPNC}},
  howpublished = {Generated Computers preprint, manuscript 001b},
  year = {2026}
}
```


## Lean

Part of this paper is formalized in Lean 4 with Mathlib, in the [Lean library](../../lean/README.md). The scope is described in [`lean/docs/001.md`](../../lean/docs/001.md), and the main statements are in the Comparator challenge [`RandomSeqNORGap.lean`](../../lean/ComparatorChallenges/RandomSeqNORGap.lean). Every listed theorem is proved without `sorry` and uses only the axioms `propext`, `Quot.sound` and `Classical.choice`. Complexity-theoretic conclusions (logspace, NC, P-completeness and the like) are not formalized.

*A Gap Theorem for P versus BPNC (001b).* The formalization proves the following.
- Lemma 3.3, the composition of smoothings, as an exact identity of finite laws. It is proved for one coordinate and for the product law on parent arrays of length $n$, together with the up-set step ($\varepsilon\le\varepsilon''\le1$ gives a suitable $\varepsilon'\in[0,1]$).
- Lemma 3.4, the gadgets $N$ and $M$, and the 6-gate majority gadget $M'$ with $c=k-1$, for every instance carrying the listed pointers and whatever $x^*_{k-1}$.
- The density facts behind Lemma 3.6: an intact $N$ has a one, and an intact $M'$ has at least two ones among its six positions.
- The compiler Comp, defined for cells of every depth $h$ (Theorem 3.5 uses $h=3$) with an arbitrary NOR circuit and arbitrary coins. It is shown to be a valid parent array.
- Exactness at $\varepsilon=0$: $x^*_{o(t,\ell)}=\mathrm{val}(g_t)$ for all $t,\ell$ and all coins.
- Step 1 of Theorem 3.5 (dominating events), pathwise for every instance. If a cell's output is wrong, the event $D(\mathrm{root})$ holds, with "hit" replaced by the weaker "does not carry its listed pointers".
- The numbers of Step 3 of Theorem 3.5 ($q_0\le0.204$, $q_1\le0.11587$, $q_2\le0.04517$, $q_3\le0.01394$ for $\varepsilon\le1/1000$, $\beta\le1/10$) and the constant $10e\bar q<0.38$ of Step 4.
- The ten-iteration bound $q_{10}\le0.1161$ of Theorem 3.7.

The following are not formalized: the probabilistic Steps 2, 4 and 5 (conditional independence, binomial and Chernoff tails), Theorems 3.5 and 3.7 themselves, Lemma 3.6, the compiler Comp$'$ (padding, depth-10 cells with $M'$, flags), the logspace computability of the compiler, Corollaries 3.8–3.10 and the gap Theorem 3.11. These are conditional statements about P and BPNC.

## Sources

This manuscript is not rewritten from the 27 October 2026 corpus. It is the existing paper below,
converted into the Generated Computers template on 3 November 2026. The statements, proofs,
constants, tables, captions and status disclosures are unchanged.
- `random-seqnor-newton/papers/2-gap/paper.tex` (companion paper II of the 2 November 2026 split,
  with the fixes of 3 November 2026).
- It was carved from the combined paper `random-seqnor-newton/paper/paper.tex`: the smoothing
  section (lines 1274–1735: smoothed algorithms, the noise-tolerant embeddings at noise 1/c and
  1/64, the consequences including the gap theorem), the setting it needs (314–381), the numerics
  on smoothed instances (2908–2968), the discussion of the lower end of the noise threshold, and
  the verification record (3479–3524, 3652–3710). Line numbers are those of 2 November 2026.
- Scripts: [`verification/random-seqnor/`](verification/random-seqnor/) (`smooth.c`, `smooth_check.py`,
  `smooth_flags.py`, `gadget_search.py`, `fronts.py`, `runall.sh`, `smooth_runall.out`).

What the conversion changed: the preamble (gcams), the bibliography (BibTeX, author-year), the
citation commands, one sentence in the numerics appendix giving the location of the scripts, and
the date. The P-completeness citation of an earlier internal note now points to manuscript 006a.

## Status

- Proved in full: the noise-tolerant embedding at noise ε ≤ 1/1000 and its sharpened form at
  ε ≤ 1/64, with the density lemma for compiled instances; hence an errorless randomized NC
  algorithm that succeeds with probability 1/20 on the ε-smoothing of every base, for some
  ε ≤ 1/64, would give P ⊆ BPNC. Smoothings compose, so the noise levels at which randomized NC
  succeeds form an up-set containing 1, and its infimum ε_c is 0 if P ⊆ BPNC and at least 1/64
  otherwise (the gap theorem). Unless P ⊆ BPNC, Newton's method needs more than ⌈log₂ n⌉^k rounds
  on the smoothings of some bases.
- Conditional: all hardness statements are reductions to the open question P ⊆ BPNC. No explicit
  base is shown hard for Newton. The upper bound ε_c ≤ 3/4 is taken from manuscript 001c.
- Checks: Section 3 was refereed by an automated reviewer, and the hardness at noise 1/64 (the
  density lemma, the 1/64 embedding and its corollary) by two further automated reviewers
  (Appendix B). Gadget constants are checked by `smooth_check.py`; compiled instances with padding
  are simulated by `smooth_flags.py`.
- Fixed on 3 November 2026: the bundle-fidelity table gained a "worst, h = 2" row, which backs the
  sentence on cells of depth 2; the proof of the 1/64 embedding says that h_g depends only on the
  circuit C, not on the coins.
- Numerical only: bundle fidelity up to ε = 0.05 with cells of depth 3, and Newton's slowdown on
  smoothed structured bases.

Not refereed. No human referee has checked it yet; the proofs were developed with the assistance
of an AI system.
