# [Constant-Frontier Computations Are in NC](paper.pdf)

**Author:** Generated Computers

**Date:** November 3, 2026

## Citation

```bibtex
@misc{GC:Constant-Frontier-Computations-Are-in-NC-November-3-2026,
  author = {{Generated Computers}},
  title = {{Constant-Frontier Computations Are in NC}},
  howpublished = {Generated Computers preprint, manuscript 010c},
  year = {2026}
}
```


## Lean

Part of this paper is formalized in Lean 4 with Mathlib, in the [Lean library](../../lean/README.md). The scope is described in [`lean/docs/010.md`](../../lean/docs/010.md), and the main statements are in the Comparator challenge [`ConstantFrontier.lean`](../../lean/ComparatorChallenges/ConstantFrontier.lean). Every listed theorem is proved without `sorry` and uses only the axioms `propext`, `Quot.sound` and `Classical.choice`. Complexity-theoretic conclusions (logspace, NC, P-completeness and the like) are not formalized.

**Constant-frontier computations (010c).** The internal live frontier, the compact-configuration graph, its edges and layer reachability are formalized. Proved are Lemma 3.2 (reachable nodes are exact), Lemma 3.3 (layer `t` is reachable iff `f(a, a+t) ≤ f`), the resulting criterion of Theorem 3.5 that the reachable layers are exactly those with `a + t ≤ e_f(a)`, and the exactness part of Corollary 3.6. Also proved are monotonicity (Lemma 2.3), restartability (Lemma 4.1), packing (Lemma 4.2) and minimality of the greedy epoch cover (Proposition 4.4). On the moving-frame side, Lean proves the conjugation Lemma 5.3 (with the support statement), one link of the event chain of Theorem 5.4 (the state stays put until the first later event whose source is the current state, then takes its target), and the cycle-plus-transposition formula behind Corollary 5.9 (`c^{-r} τ c^r = (−r, 1−r)` and `x_t = y_t + r_t`). The graph-size bound (Lemma 3.4), Boolean matrix squaring, all NC/depth bounds (Theorems 3.5, 4.3, 5.6 and Corollaries 3.6, 5.8, 5.9 as complexity statements), the successor-graph construction (Lemma 5.5) and pointer jumping are not formalized. The full multi-link event chain is obtained by iterating the formalized link, but it is not stated as a single theorem.

## Sources

Rewritten from the following internal notes (document numbers of the 27 October 2026 corpus review):
- #26, Closest Results Toward P ⊆ SP — full proofs (`Closest_Results_Toward_P_in_SP_Full_Proofs_20260820.pdf`),
  Appendix C: Lemmas C.1–C.3, Theorem C.4, Corollary C.5, Lemmas C.7–C.8, Theorem C.9 and the
  greedy-cover optimality of C.16 (PDF pp. 48–52, 55); Appendix W: Definitions W.1–W.2, Lemma W.3,
  Theorem W.4, Lemma W.5, Theorem W.6, Remark W.7, Corollaries W.8–W.9 (PDF pp. 184–189).

## Status

- Proved in full: exactness of reachable compact configurations, the path–frontier equivalence,
  the compact-frontier epoch generator (polynomial work, O((f+1)² log² N) depth for fixed f),
  constant-frontier executions in NC, restartability, packing, the maximal-epoch cover and its
  minimality; the moving-frame conjugation lemma, the exact event-chain characterization, the
  successor-graph construction, the moving-frame compiler, the block corollary and the
  cycle-plus-transposition trajectory compiler.
- Attribution: the compact-frontier generator is the classical reachability argument behind
  Borodin's theorem (1977), applied to epochs; it is presented as an application, not as a new
  technique. The moving-frame compiler is a combination of standard PRAM primitives.
- Changes: the machine model is stated explicitly with a fixed convention for reads of unwritten
  cells; the monotonicity of the frontier in the endpoint is proved (the notes use it implicitly).
  The two results were kept in one paper because each is short and both are exact trace generators
  that need no proposed trace.
- Scope: no bound on the number of epochs or on the exception volume of any strictly sequential
  evaluator is claimed; the block corollary assumes decompositions that we do not know how to
  produce in general.
- Checks: the reachability criterion on 400 random small machines (budgets 0–2); the moving-frame
  compiler on 3,000 random instances and 1,500 random cycle-plus-transposition words.

Not refereed. No human referee has checked it yet; the proofs were developed with the assistance
of an AI system.

## Code

Checking scripts used for this manuscript are in [`verification/`](verification/): `moving_frame_compact.py`. They are plain Python 3 with no dependencies outside the standard library unless the script says otherwise.
