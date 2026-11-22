# [A P-Complete Problem in Average-Case NC](paper.pdf)

**Author:** Generated Computers

**Date:** November 3, 2026

## Citation

```bibtex
@misc{GC:A-P-Complete-Problem-in-Average-Case-NC-November-3-2026,
  author = {{Generated Computers}},
  title = {{A P-Complete Problem in Average-Case NC}},
  howpublished = {Generated Computers preprint, manuscript 001a},
  year = {2026}
}
```


## Lean

Part of this paper is formalized in Lean 4 with Mathlib, in the [Lean library](../../lean/README.md). The scope is described in [`lean/docs/001.md`](../../lean/docs/001.md), and the main statements are in the Comparator challenge [`RandomSeqNORNewton.lean`](../../lean/ComparatorChallenges/RandomSeqNORNewton.lean). Every listed theorem is proved without `sorry` and uses only the axioms `propext`, `Quot.sound` and `Classical.choice`. Complexity-theoretic conclusions (logspace, NC, P-completeness and the like) are not formalized.

*A P-Complete Problem in Average-Case NC (001a).* Newton's method over GF(2) is defined explicitly, by forward substitution of the linearised system with the paper's NOT-gate convention. The formalization proves the following.
- Lemma 4.2, the error recursion, at NOT gates, binary gates and position $0$.
- The trace is a fixed point of the Newton map.
- Lemma 4.3, the front identity. The next error vanishes up to $i$ when there is no source up to $i$, it equals $1$ at the first source, and $f_{t+1}\ge f_t+2$.
- The deterministic part of Lemma 4.4: iterates on $[0,n]$ depend only on $j_1,\dots,j_n$.
- Lemma 5.2(i), the pathwise witness property.
- Proposition 3.1, the Newton–Strahler bound. After $t$ rounds every gate of Horton–Strahler rank below $t$ is exact, from any start, so $T_n\le\rho(n)+1$.
- Proposition 8.1 in full, Newton's exact worst case. From the standard start $T_n\le\lfloor(n-1)/2\rfloor$ for all instances, and the explicit instance $W$ has front exactly $f_t=2t+3$ and $T_n(W)=\lfloor(n-1)/2\rfloor$ for every $n\ge3$. So the maximum over all instances is exactly $\lfloor(n-1)/2\rfloor$.
- Corollary 8.5: the lexicographically first maximal independent set of the graph with edges $\{i-1,i\}$, $\{j_i,i\}$ is the set of ones of the trace.
- The final algebraic step of Theorem 8.3: if $L\le U$ lie in $[0,1/2]$ with $L\ge g(U)$ and $U\le g(L)$, where $g(u)=(1-u)/(2-u)$, then $L=U=(3-\sqrt5)/2$.

The main probabilistic results are not formalized: the $O(\log n)$ bound with probability $1-o(1)$ (Theorem 7.1, Theorem A), the lower bound $\log_2\ln n-3$ (Theorem 5.3), the Strahler asymptotics (Theorem 3.2), the random-structure bounds (Proposition 8.2), the existence of the almost-sure density limit, and the NC/space consequences (Corollaries 7.3 and 8.4). Lemmas 4.1, 4.5, 4.6 and the window lemma are not formalized.

## Sources

This manuscript is not rewritten from the 27 October 2026 corpus. It is the existing paper below,
converted into the Generated Computers template on 3 November 2026. The statements, proofs,
constants, tables, captions and status disclosures are unchanged.
- `random-seqnor-newton/papers/1-newton/paper.tex` (companion paper I of the 2 November 2026 split,
  with the fixes of 3 November 2026).
- It was carved from the combined paper `random-seqnor-newton/paper/paper.tex` (54 pages): the
  introduction (lines 131–312, cut to the Newton results), Sections at lines 314–1273 (setting,
  Strahler bound, tools, good events, window lemma, main theorem, worst case, structure, density,
  class-level consequences, greedy independent sets), discussion items 1–4 and the 0.87 conjecture
  (2730–2752, 2790–2795), the numerics appendix (2798–2907) and the verification record
  (3387–3478, 3741–3773). Line numbers are those of 2 November 2026.
- Scripts: [`verification/random-seqnor/`](verification/random-seqnor/) (`newton*.c`, `worstcase.c`,
  `check_constants.py` and others named in the appendices).

What the conversion changed: the preamble (gcams), the bibliography (BibTeX, author-year), the
citation commands, two sentences of the related-work section that called the cited notes
"unpublished notes" (now "other manuscripts of this collection"), one sentence in the numerics
appendix giving the location of the scripts, and the date. Citations of the earlier internal
notes now point to the manuscripts of this collection that contain the cited content (Newton
step, error identity and Newton–Strahler bound: 002a; first-collision law: 006d; P-completeness,
live width and the average-case open problem: 006a; binary core and core-size ladder: 006f; the
anchor–Γ portfolio: 009c; the reset-set iteration: 006b; the random-instance measurements, the
mean-field density prediction and the linear family for the reset-set iteration: 006c; greedy
MIS form: 011b). Section and theorem numbers of those notes were dropped from the citations.

## Status

- Proved in full: the O(log n) bound on Newton rounds with probability 1 − o(1) from the standard
  start and from a uniformly random start (Theorem A), the lower bound log₂ ln n − 3 (Theorem B),
  the errorless average-case circuits of depth O(log³ n) (Corollary D) and the class-level
  consequences (errorless NC^{k+2} with failure O(log^{−k} n); space O(log³ n)), the
  Newton–Strahler bound, the exact worst case ⌊(n − 1)/2⌋, the linear binary core and live width
  of random instances, the golden-ratio density of ones, and the greedy-MIS corollary.
- Sketched: one law-of-large-numbers step in the proof that the Horton–Strahler rank is
  (√(8/π) + o(1))√n (Theorem C), which Proposition 8.2(a) restates. All other proofs are complete.
- Checks: the arithmetic of the main recursion is machine-checked (`check_constants.py`, 11,202
  scales). Sections 2–7 were refereed by an automated reviewer (findings F1–F10, all resolved;
  Appendix B), and Section 8 by a second automated reviewer.
- Numerical only: about 0.87 log₂ n rounds for n between 2^16 and 2^25, and the conjecture
  T_n / log₂ n → c ≈ 0.87.
- Credits: the Boolean Newton step, its error identity, the first-collision law and the
  Newton–Strahler bound come from earlier notes, now manuscripts 002a and 006d; the golden-ratio
  density was predicted heuristically in the notes behind 006c.
- Nothing claims P ⊆ NC: the algorithm is errorless average-case, and Newton needs linearly many
  rounds on some instances.

Not refereed. No human referee has checked it yet; the proofs were developed with the assistance
of an AI system.
