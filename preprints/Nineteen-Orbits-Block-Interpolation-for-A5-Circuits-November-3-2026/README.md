# [Nineteen Orbits Block Interpolation for A₅ Circuits](paper.pdf)

**Author:** Generated Computers

**Date:** November 3, 2026

## Citation

```bibtex
@misc{GC:Nineteen-Orbits-Block-Interpolation-for-A5-Circuits-November-3-2026,
  author = {{Generated Computers}},
  title = {{Nineteen Orbits Block Interpolation for $A_5$ Circuits}},
  howpublished = {Generated Computers preprint, manuscript 004c},
  year = {2026}
}
```



## Lean

Part of this paper is formalized in Lean 4 with Mathlib, in the [Lean library](../../lean/README.md). The scope is described in [`lean/docs/004.md`](../../lean/docs/004.md), and the main statements are in the Comparator challenge [`NineteenOrbitsA5.lean`](../../lean/ComparatorChallenges/NineteenOrbitsA5.lean). Every listed theorem is proved without `sorry` and uses only the axioms `propext`, `Quot.sound` and `Classical.choice`. Complexity-theoretic conclusions (logspace, NC, P-completeness and the like) are not formalized.

**004c (nineteen orbits).** P. Hall's theorem is proved in general: if $T$ is simple nonabelian and
generating pairs $(x_i,y_i)$ are pairwise not related by an automorphism, then $(x_i)_i,(y_i)_i$
generate $T^\iota$ (Lemma 5.1, Theorem 5.2). For $A_5$, a kernel-checked certificate for each of the
3600 pairs shows: a pair generates $A_5$ iff it is conjugate under $S_5$ to one of 19 explicit
representatives, by a unique permutation; otherwise it lies in one of 21 explicit maximal subgroups,
each metabelian. Hence exactly 2280 generating and 1320 non-generating pairs, forming 19 free
$S_5$-orbits; distinct representatives are separated by automorphism invariants, so evaluation on
them maps $F_2$ onto $A_5^{19}$. The mirror-word theorem (Theorem 6.1), the 19 selectors
(Corollary 6.2) and non-interpolation (Corollary 6.3, without the size bound $m+O(1)$) are proved.
Also proved: power permutations and unit-power reversibility (Lemma 3.5, Theorem 3.6) and the
inverse of the Fibonacci update (Corollary 3.3). Not formalized: that $\mathrm{Aut}(A_5)$ is $S_5$
(the orbit statements use $S_5$-conjugation), the census by subgroup order, the Fibonacci cycle
structure, and the scan, fusion and cold-sector compilers (Theorems 3.2, 3.8, 4.1).

## Sources

Rewritten from the following internal note (document numbers of the 27 October 2026 corpus review):
- #45, *The Nielsen Scan Hack: two-register corridors, unit-power updates, and the
  nineteen-channel barrier* (`old_stuff/Nielsen_Scan_Hack_and_Nineteen_Channel_Barrier_20260822.pdf`),
  the whole note: Def 1, Thm 2 (p. 2); Cor 3, Lemma 4, Thm 5 (pp. 3–4); Def 6, Thm 7 and the
  remark after it (pp. 4–5); the census and Thm 8 (p. 5); Thm 9 and the "no pair-orbit
  interpolation" box (p. 6); Thm 10, Cor 11 and the explicit word (p. 7).

## Status

Proved in full: the two-register prefix compiler, noncommutative Fibonacci, power permutations and
unit-power reversibility (Thm 3.2, Cor 3.3, Lemma 3.5, Thm 3.6), the pair-corridor fusion compiler
(Thm 3.8), the cold-sector compiler (Thm 4.1, quoting the DET bound of Beaudry–McKenzie–Péladeau–
Thérien), nineteen-channel independence (Thm 5.2) with a self-contained subdirect-product lemma,
and the mirror-word results (Thm 6.1, Cors 6.2–6.3).

Changes relative to the source: Thm 5.2 (the 19 orbits and F_2 ↠ A5^19) is P. Hall's theorem
(Quart. J. Math. 1936), which the source does not cite; it is attributed and presented with a
proof, and Hall's converse (k ≤ 19) is recorded as a remark. The mirror words of Section 6 are the
new part. As the reviewers noted, the scan results are elementary; the Fibonacci example is
accompanied by the observation that the recurrence is periodic (cycle lengths of (x,y) ↦ (xy,x)
on A5^2 at most 50). The pair-corridor decomposition is defined precisely; the source also allowed
gates covered by unspecified "established compilers", which is dropped, and the proof (levels by
longest path, pointer jumping on unary forests) is completed. The source's boxed statement on
interpolation is formalized as Cor 6.3. Omitted: the conditional transfer theorem (Thm 12), whose
hypotheses use notions the source does not define.

Computer checks (script `verification/check_a5.py`, permutations of five points): element orders; the
power and unit-power statements for all exponents; the census of pairs by generated subgroup
(1, 45, 80, 30, 144, 180, 360, 480, 2280); that the 58 proper two-generated subgroups have trivial
second derived subgroup; |Aut(A5)| = 120 acting freely with 19 orbits on the 2280 generating pairs;
that all 171 pairwise projections are A5^2; that w = [[x,y], x^{-1}[x,y]x] is the identity on all
1320 cold pairs and non-identity on exactly 1920 hot pairs (16 full orbits) under both commutator
and composition conventions; the cycle structure of the Fibonacci map.

Not refereed.
