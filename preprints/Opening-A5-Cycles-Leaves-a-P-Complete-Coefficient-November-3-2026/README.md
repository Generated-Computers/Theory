# [Opening A₅ Cycles Leaves a P-Complete Coefficient](paper.pdf)

**Author:** Generated Computers

**Date:** November 3, 2026

## Citation

```bibtex
@misc{GC:Opening-A5-Cycles-Leaves-a-P-Complete-Coefficient-November-3-2026,
  author = {{Generated Computers}},
  title = {{Opening $A_5$ Cycles Leaves a P-Complete Coefficient}},
  howpublished = {Generated Computers preprint, manuscript 004f},
  year = {2026}
}
```



## Lean

Part of this paper is formalized in Lean 4 with Mathlib, in the [Lean library](../../lean/README.md). The scope is described in [`lean/docs/004.md`](../../lean/docs/004.md), and the main statements are in the Comparator challenge [`OpeningCycles.lean`](../../lean/ComparatorChallenges/OpeningCycles.lean). Every listed theorem is proved without `sorry` and uses only the axioms `propext`, `Quot.sound` and `Classical.choice`. Complexity-theoretic conclusions (logspace, NC, P-completeness and the like) are not formalized.

**004f (opening A5 cycles).** The hard-coefficient cycle (Theorem 2.1) and its link to Boolean
circuits through the $A_5$ compilation (core of Corollary 2.2); the mixer cycle and mixer inverse
(Lemma 3.1); bijectivity of mixer strips and the impossibility of a summary by fewer than $W$ group
values (Theorem 3.2(i),(iii)); the Nielsen-strip embedding of multiplication circuits with $s$
registers and at most $2s$ transvections $g_i\leftarrow g_ig_j$, $i\ne j$ (Theorem 7.2). Symbolic
opening (Theorem 3.3) is covered by the monodromy and descriptor-composition theorems of 004e. Not
formalized: Theorem 3.2(ii) (disjoint cycles in the graphs), ancestrally liftable kernels, and the
transfer statements.

## Sources

Rewritten from the following internal notes (document numbers of the 27 October 2026 corpus review):
- #27, *Symbolic Monodromy and the Nielsen-Strip Core* (`Symbolic_Monodromy_and_Nielsen_Core_20260820.pdf`;
  a byte-identical copy is in `old_stuff/`), all of it: Definition 1, Lemma 2, Theorem 3,
  Corollary 4 (symbolic opening, pp. 2–3), Theorem 5 and Corollary 6 (hard-coefficient cycle, p. 4),
  Definition 7, Theorem 8, Proposition 9 (ancestral kernels, p. 5), Lemma 10 and Theorem 11 (mixer
  strips, pp. 5–6), Definition 12, Theorem 13, Corollary 14 (Nielsen strips, pp. 6–7).

## Status

- Proved in full: symbolic cycle opening (O(m) work, O(log m) depth, linear expression size) and
  bulk opening; the hard-coefficient cycle and the reduction showing its satisfiability problem is
  P-complete; the ancestral-kernel compiler (depth O((t+1) log² s)); the mixer-strip barrier; the
  linear embedding of A5 circuits into Nielsen strips (2 transvections per gate) and the resulting
  transfer of a depth saving to A5 circuits and to multitape Turing-machine time.
- Made precise relative to the source: the definition of an ancestrally liftable kernel (forest
  H-cones), with a proof that a feedback set is sufficient and an explicit example that it is not
  necessary; the restriction to Latin gates (x ≠ y), needed for the six local bijections.
- Not established, stated only conditionally: source Corollary 14 ("P ⊆ SP if and only if Nielsen
  strips admit polynomial work and depth s^{1−Ω(1)}"). The source relies on the strict transfer of
  #29 (now 004g), which holds relative to multitape Turing-machine time only; the RAM-time
  hypothesis (H) that the equivalence needs is stated in Remark 7.4. The reviewer's description
  ("cites a strict transfer from a note not in the corpus") is slightly off: the transfer is in #29,
  which is in the corpus; the note that is missing is the one on context capacity cited for the
  interface-width statement, which is reproved here by a counting argument (Theorem 6.2(iii)).
- As the review notes, the symbolic opening gains nothing by itself and the Nielsen embedding is
  elementary; the paper says so.
- Checks: the descriptor composition rule, the bijection of Theorem 3.3 (brute force on 60 random
  cycles of length 2 and 3 over A5) and the mixer opening (all 3600 pairs) by computer.
- Left out: Theorem 15, Conjecture 16 and Corollary 17 (conditional transfer criteria that restate
  the open problem and conclude P ⊆ SP through the uncorrected transfer).

Not refereed. No human referee has checked it yet; the proofs were developed with the assistance
of an AI system.

## Code

Checking scripts used for this manuscript are in [`verification/`](verification/): `a5checks.py`. They are plain Python 3 with no dependencies outside the standard library unless the script says otherwise.
