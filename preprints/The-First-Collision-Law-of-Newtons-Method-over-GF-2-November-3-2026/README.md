# [The First-Collision Law of Newton's Method over GF(2)](paper.pdf)

**Author:** Generated Computers

**Date:** November 3, 2026

## Citation

```bibtex
@misc{GC:The-First-Collision-Law-of-Newtons-Method-over-GF-2-November-3-2026,
  author = {{Generated Computers}},
  title = {{The First-Collision Law of Newton's Method over $\mathrm{GF}(2)$}},
  howpublished = {Generated Computers preprint, manuscript 006d},
  year = {2026}
}
```



## Lean

Part of this paper is formalized in Lean 4 with Mathlib, in the [Lean library](../../lean/README.md). The scope is described in [`lean/docs/006.md`](../../lean/docs/006.md), and the main statements are in the Comparator challenge [`FirstCollisionLaw.lean`](../../lean/ComparatorChallenges/FirstCollisionLaw.lean). Every listed theorem is proved without `sorry` and uses only the axioms `propext`, `Quot.sound` and `Classical.choice`. Complexity-theoretic conclusions (logspace, NC, P-completeness and the like) are not formalized.

**006d (First-collision law).** Newton's method over $\mathbb F_2$ is defined explicitly. The Newton direction is computed by forward substitution, and we prove that it solves $J(x)d=F(x)$. Formalized: the exact error identity $J(x)e^+=q(e)$ (Lemma 2.1) and the first-collision law (Theorem 2.2): $e^+$ vanishes up to the first collision and equals $q$ there, and the first error advances by at least two. Also formalized: Corollary 2.3. From every start with $x_0=1$, Newton's method is exact on $0,\dots,n$ after $\lceil n/2\rceil$ rounds, and after $\lceil(n-1)/2\rceil=\lfloor n/2\rfloor$ rounds from $(1,0,\dots,0)$. Proposition 2.5 is checked on its instance. Not formalized: the contraction onto mixers (Theorem 2.4), the coefficient formula (Proposition 2.6), the tightness family (Theorem 2.7, so the lower bound $\lceil n/2\rceil$ is not formalized), and Section 3.

## Sources

Rewritten from the following internal notes (document numbers of the 27 October 2026 corpus review):
- #23, "Addendum N: compatible partial algebras" (`addendum_n_compatible_partial_algebras.pdf`),
  all sections: Theorem 2.1, Corollary 2.2, Proposition 2.3, Theorems 3.1-3.2,
  Lemmas 3.3-3.4, Theorem 4.1, Theorem 5.2 (as a remark only), Theorem 6.1,
  Proposition 6.2, formulas (N.25)-(N.26), Theorem 6.3.
- #25, "Nine Attacks on P ⊆ quasiNC" (`nine_attacks_quasiNC_with_addenda.pdf`), Section
  4.1 (exact Newton identity), with the two-line proof from Addendum E.1.

## Status

- Proved in full:
  - the exact error identity of one Newton round over GF(2) (NOT gates written as affine
    maps);
  - the first-collision law, so that Newton converges within ⌈n/2⌉ rounds from any start
    with x_0 = 1;
  - tightness of ⌈n/2⌉ on an explicit mixer-free family, with the closed form
    C(r-2, t-1) mod 2 for the errors;
  - the exact contraction of the transport onto mixers, and the one-round coefficient
    formula;
  - the interface facts: selector bound, one-way index, exact overlap needs 2^r queries,
    sum-check, disclosed-challenge forgery, honest strategy contains the table, and
    multilinear extensions count modulo p.
- Reconciliation with manuscript 001a: the ⌈n/2⌉ bound is the worst case over all
  starts. It is attained for the start that flips y_1 and y_2 of the trace on the family
  above. From the standard start (1, 0, ..., 0), position 1 is always correct, and 001a
  proves the exact worst case ⌊(n-1)/2⌋ for n >= 3. The tight family needs one round
  from that start. Exhaustive check for n <= 7 (all instances, all starts): maximum
  ⌈n/2⌉. For n <= 8 from the standard start: maximum ⌊(n-1)/2⌋ for n >= 3.
- Remark only: the Cook-Mertz bridge (Theorem 5.2 of #23). At polylogarithmic
  parameters, depth-first evaluation already gives polylogarithmic space, so it removes
  no obstacle.
- Changes:
  - the fine workspace bound W_b + O(log^3 n) for inverse entries in Theorem 6.1 is
    replaced by the plainer statement that the reduced coefficients are logspace
    computable;
  - the research-programme parts of #23 (Target 7.1 and the audit list) are left out;
  - references to an "Addendum M" outside the corpus are removed by stating the overlap
    facts for arbitrary functions A, B.
- Checks: the identity, the front law and the round counts were verified exhaustively for
  all parent arrays and all starts with n <= 7. The tight family was verified for
  n <= 40, including the binomial formula and the absence of mixers.
- Not refereed.
