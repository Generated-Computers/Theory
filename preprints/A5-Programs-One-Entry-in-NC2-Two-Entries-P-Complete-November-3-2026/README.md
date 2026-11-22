# [A₅ Programs: One Entry in NC², Two Entries P-Complete](paper.pdf)

**Author:** Generated Computers

**Date:** November 3, 2026

## Citation

```bibtex
@misc{GC:A5-Programs-One-Entry-in-NC2-Two-Entries-P-Complete-November-3-2026,
  author = {{Generated Computers}},
  title = {{$A_5$ Programs: One Entry in $\mathrm{NC}^2$, Two Entries P-Complete}},
  howpublished = {Generated Computers preprint, manuscript 004d},
  year = {2026}
}
```



## Lean

Part of this paper is formalized in Lean 4 with Mathlib, in the [Lean library](../../lean/README.md). The scope is described in [`lean/docs/004.md`](../../lean/docs/004.md), and the main statements are in the Comparator challenge [`OneEntryA5.lean`](../../lean/ComparatorChallenges/OneEntryA5.lean). Every listed theorem is proved without `sorry` and uses only the axioms `propext`, `Quot.sound` and `Classical.choice`. Complexity-theoretic conclusions (logspace, NC, P-completeness and the like) are not formalized.

**004d (one entry vs two entries).** One-entry programs over any group compute powers $x^{a_v}$ with
exponents given by the local rules (Theorem 3.1); over $A_5$ the exponents reduce mod 30, giving at
most 30 value functions (Corollary 3.2). Dominator condensation (Theorem 4.3, main claim): if $d$
dominates $v$ in a well-formed program then $\mathrm{val}(v)=\mathrm{val}(d)^a$ with $a$ independent
of the entry values; inverse and squaring gates are dominated by their operand (Theorem 4.3(iii)).
Theorem 6.1 is formalized as the power normal form plus the embedding of Boolean circuits into
constant-free two-entry programs. Not formalized: Theorem 4.3(iv) and prime roots, the prime-core
construction (Theorem 4.4), path counting, and all NC² / depth statements.

## Sources

Rewritten from the following internal note (document numbers of the 27 October 2026 corpus review):
- #46, *The One-Generator Escape Hatch: dominator power condensation, unary coefficient cores, and
  the exact one-versus-two entry threshold* (`old_stuff/One_Generator_Escape_Hatch_20260822.pdf`):
  Def 1, Thm 2 (p. 2); Cor 3, Thm 4 (p. 3); Def 5, Lemma 6, Def 7, Thm 8 (pp. 3–4); Thms 9–10,
  Cor 11 (p. 5); Thm 17 (p. 7); the stress-family audit (p. 8).

## Status

Proved in full: the one-generator power normal form, the thirty-class contraction and the
one-entry compiler (Thm 3.1, Cor 3.2, Thm 3.3), dominator power condensation (Thm 4.3), prime-core
equivalence (Thm 4.4), construction of the whole normal form with polynomial work in depth
O(log^2 n) (Thm 5.1), the evaluation bound O(h(C) + log^2 n) (Cor 5.2), and the one-versus-two
entry dichotomy (Thm 6.1).

Changes relative to the source: Thm 17(ii) ("two-entry regions contain the strict core for
P ⊆ SP") is restated as P-completeness of constant-free two-entry programs, with a linear-size
reduction. In Thm 4.3, (iii) is extended to squaring gates and (iv) is stated as an equivalence
(immediate from (i)); "uniquely determined exponent" is replaced by "determined by the local
rules", since the exponent is unique only modulo the order of the root value. The exponent
computation is made explicit as path counting modulo 30 by matrix powering. Omitted: Thms 12–13 and
Cor 14 (they rely on a fanout-height compiler from another note and on a conditional speedup
criterion), Def 15 and Thm 16 (they rely on swap/orbit modules from another note), and the
conditional transfer Thm 18. Following the reviewers' caveat, Remark 6.2 records that the normal
form does not shrink hard instances: on programs built from random Boolean circuits by the
commutator gadgets, 72–76% of the nodes are prime (measured, script `verification/prime_core_gadget.py`).

Computer checks (script `verification/check_a5.py`): Thm 4.3, including (iii) and (iv), on 300 random
two-generator programs with up to 39 nodes, at 40 random assignments of (P,Q) each.

Not refereed.
