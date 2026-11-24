# [Small Noise Defeats Two Natural Parallel Iterations](paper.pdf)

**Author:** Generated Computers

**Date:** November 3, 2026

> **Superseded (24 November 2026).** Superseded by the consolidated paper [Sequential NOR on Random and Smoothed Instances](../../papers/1-Sequential-NOR-on-Random-and-Smoothed-Instances/paper.pdf) (Sections 12 and 16). There both iterations need linearly many rounds against adaptive adversaries, and Ω(n/log n) rounds on random block bases fixed in advance below explicit noise levels, with 4/9 the exact level of the relevance-pruned iteration on those bases.

## Citation

```bibtex
@misc{GC:Small-Noise-Defeats-Two-Natural-Parallel-Iterations-November-3-2026,
  author = {{Generated Computers}},
  title = {{Small Noise Defeats Two Natural Parallel Iterations}},
  howpublished = {Generated Computers preprint, manuscript 001d},
  year = {2026}
}
```


## Lean

Part of this paper is formalized in Lean 4 with Mathlib, in the [Lean library](../../lean/README.md). The scope is described in [`lean/docs/001.md`](../../lean/docs/001.md), and the main statements are in the Comparator challenge [`RandomSeqNORSmallNoise.lean`](../../lean/ComparatorChallenges/RandomSeqNORSmallNoise.lean). Every listed theorem is proved without `sorry` and uses only the axioms `propext`, `Quot.sound` and `Classical.choice`. Complexity-theoretic conclusions (logspace, NC, P-completeness and the like) are not formalized.

*Small Noise Defeats Two Natural Parallel Iterations (001d).* The formalization proves the following.
- The relevance-pruned iteration of Definition 3.3 and its depth $D$, defined by the paper's min–max formula over anchors.
- Lemma 3.4 in full: (a) $K_t=\{i:D(i)\le t\}$ with correct values, and (b) every position known to the Kleene–prefix iteration is known to the pruned one, via $D\le d$.
- Lemma 3.5 in full, the switch characterisation. Part (a) gives the recursions for $D$ (four cases) and for $d$ (three cases). Part (b) gives the characterisation of $D(i)\ge t+1$ and of $d(i)\ge t+1$.
- Lemma 4.2 in full (non-deep positions), for $D$ and for $d$, including the claims about $x^*_p=1$ and about gate $u+1$.
- The deterministic over-approximation step of Theorem 4.3: Lemma 4.2 read through abstract indicators $\hat U$ and $\hat K$ gives conditions (A$'$) and (B$'$), for both parts.
- The exact numbers used in that proof:
  - the bound $\sum_{r<R}N(r)\le(2-u)/(1-u)^2$ for the recursion $a_r,b_r$;
  - $u^*$, $k^*$, $\mu$ and $\mu_1$ and the inequalities $\mu\le\sigma^*-\eta$ and $\mu_1\le\sigma^1_*-\eta$ in both parts;
  - $u^*(2-u^*)\in\{7/16,231/400\}$ with $6\ln(1/(u^*(2-u^*)))\ge3$;
  - $2\eta^2m\ge6\ln n$.

The random block bases and Theorem 4.3 itself (the lower bound $n/(5\cdot10^6\ln^2n)$ with probability $1-n^{-1/2}$) are not formalized. Neither are their probabilistic steps: the conditional laws, the monotone coupling, the Hoeffding bounds, and the parameter estimates involving $\ln n$ and ceilings.

## Sources

This manuscript is not rewritten from the 27 October 2026 corpus. It is the existing paper below,
converted into the Generated Computers template on 3 November 2026. The statements, proofs,
constants, tables, captions and status disclosures are unchanged.
- `random-seqnor-newton/papers/4-lower/paper.tex` (companion paper IV of the 2 November 2026
  split, with the fix of 3 November 2026).
- It was carved from the combined paper `random-seqnor-newton/paper/paper.tex`: the subsection on
  random block bases and the lower bound (lines 2402–2629), the definitions and lemmas it needs
  from the Kleene–prefix section (1758–1825, 2175–2401, with density lemmas from 1957–2174), the
  numerics (3135–3386: block bases, the algorithm search, algorithms that forget, chaos of long
  random blocks, two hard cores), the discussion of the iterations at small noise, and the
  verification record (3711–3740). Line numbers are those of 2 November 2026.
- Scripts: [`verification/random-seqnor/`](verification/random-seqnor/) (`blockbase.c`, `nogo_block.sh`,
  `nogo_check.py`, `kpr_check.py`, `kpr_witness.py`, and the search test bed in `evolve/`).

What the conversion changed: the preamble (gcams), the bibliography (BibTeX, author-year), the
citation commands, one sentence in the numerics appendix giving the location of the scripts, the
directory name `verification/evolve` (now `evolve`, inside `verification/random-seqnor/`), and the date. Citations
of earlier internal notes now point to manuscripts 006a (P-completeness, live width) and 011b
(greedy MIS form).

## Status

- Proved in full, unconditionally: for ε ≤ 1/10 and n ≥ 10^13 there are bases (random block bases)
  on whose ε-smoothings the Kleene–prefix iteration and its relevance-pruned variant both need at
  least n/(5·10^6 ln² n) rounds with probability at least 1 − n^{−1/2}; for the Kleene–prefix
  iteration this holds for ε ≤ 3/20. The proof rests on a lemma on non-deep positions. The three
  lemmas it uses from manuscript 001c (rounds equal dependency depth, the relevance-pruned
  comparison, the switch characterisation) are included with their proofs.
- Scope: the bound concerns two fixed algorithms. It says nothing about the critical noise level
  ε_c of all errorless randomized NC algorithms, and is no evidence that ε_c > 0.
- Checks: the non-deep-positions lemma and the lower-bound theorem were refereed by an automated
  reviewer (Appendix B); the imported lemmas were refereed by other automated reviewers, recorded
  in 001c.
- Fixed on 3 November 2026: the relevance-pruned count at ε = 0.3 for B = 128 falls from
  1.01 n/B at n = 2^18 to 0.88 n/B at 2^24 (it was described as close to n/B).
- Numerical only: the search over bounded-support substitution, cut-map doubling and windowed
  Jacobi algorithms, which fail on random block bases with long blocks, and the observation that a
  random block of length B forgets its state only after about 2^{0.1B} blocks. These are evidence
  about the algorithms tried, not about P versus BPNC.

Not refereed. No human referee has checked it yet; the proofs were developed with the assistance
of an AI system.
