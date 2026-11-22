# [Few Disjoint Cycles Give Sublinear-Depth Circuit Evaluation](paper.pdf)

**Author:** Generated Computers

**Date:** November 3, 2026

## Citation

```bibtex
@misc{GC:Few-Disjoint-Cycles-Give-Sublinear-Depth-Circuit-Evaluation-November-3-2026,
  author = {{Generated Computers}},
  title = {{Few Disjoint Cycles Give Sublinear-Depth Circuit Evaluation}},
  howpublished = {Generated Computers preprint, manuscript 004e},
  year = {2026}
}
```



## Lean

Part of this paper is formalized in Lean 4 with Mathlib, in the [Lean library](../../lean/README.md). The scope is described in [`lean/docs/004.md`](../../lean/docs/004.md), and the main statements are in the Comparator challenge [`FewDisjointCycles.lean`](../../lean/ComparatorChallenges/FewDisjointCycles.lean). Every listed theorem is proved without `sorry` and uses only the axioms `propext`, `Quot.sound` and `Classical.choice`. Complexity-theoretic conclusions (logspace, NC, P-completeness and the like) are not formalized.

**004e (few disjoint cycles).** The descriptor algebra (Lemma 5.1), the cycle monodromy bijection
between solutions of a cycle of relations and roots of the return map (Theorem 5.2), and the full
$A_5$ root-domain classification (Theorem 5.3: $|D_1(A,B)|\in\{0,3,4,5,60\}$, nonzero iff $A$ is
conjugate to $B^{-1}$, then equal to $|C(B)|$, 60 only for $A=B=e$; $|D_{-1}(A,B)|\in\{0,1,16\}$,
16 iff $A=B$, 0 iff $A^{-1}B$ has order 2). Not formalized: the stress family (Theorem 4.1), the
2-core lemma, the short-kernel-cycle lemma and the cycle-packing feedback set (Lemmas 3.1–3.2,
Theorem 3.3), and the compilers and depth bounds.

## Sources

Rewritten from the following internal notes (document numbers of the 27 October 2026 corpus review):
- #30, *Feedback Kernels and A5 Cycle Monodromy* (`old_stuff/Feedback_Kernels_and_A5_Cycle_Monodromy_20260820.pdf`),
  all of it: Theorem 1 (stress family, p. 2), Lemma 3 and Theorem 4 (forest and feedback-kernel
  compilers, p. 3), Lemma 5, Theorem 6 and Corollary 7 (cycle-packing feedback set, pp. 4–5),
  Definition 8 to Theorem 13 (ready cycles, descriptors, A5 classification, bulk contraction,
  pp. 5–7).
- For the comparison remarks: the low-excess compiler and escape switching of #33
  (`old_stuff/Output_Conditioned_Latin_Core_and_LP_Precision_Barrier_20260820.pdf`, Thms 5, 11–12),
  now manuscript 003f, and the Strahler compiler of #29, now manuscript 004g.

## Status

- Proved in full: the stress family (all six parts), the forest and feedback-kernel compilers
  (depth O((h+1) log² s)), the constructive cycle-packing feedback set (size at most
  cp·(2⌈log₂ s⌉+1), depth O((cp+1) log² s)), the cycle-packing compiler (depth O((cp+1) log³ s)),
  the descriptor algebra, the A5 root-domain classification ({0,3,4,5,60} and {0,1,16}) and bulk
  contraction of disjoint ready cycles.
- Made explicit relative to the source: the parallel computation of the 2-core (a
  characterization lemma with proof), the kernel construction, the depth O(log² s) per iteration
  (the source says "polylog"), and the restriction to Latin gates z = xy with x ≠ y (a squaring
  gate does not induce a bijection, which the source's descriptor lemma silently needs).
- The source normalizes fanout before defining the wire graph; this is not needed, and the bounds
  for the unnormalized graph imply the source's (Remark 2.1).
- Prior work: the feedback-set construction is the greedy form of the Erdős–Pósa (1965) girth
  argument (uncited in the source); it is presented as such, not as new.
- Added in this rewrite: Remark 5.5 names the three compilers the review said are subsumed (the
  forest compiler, the supplied-kernel compiler, and the low-excess compiler of 003f, via
  cp ≤ cyclomatic excess); Remark 5.6 shows the Strahler compiler of 004g matches the
  cycle-packing bound up to one log factor (Strahler rank ≤ (h+1)(log₂((κ+1)s)+1) for any
  feedback set of size h), so the new content of the cycle-packing compiler is the explicit
  feedback set.
- Checks: the A5 classification exhaustively over all 3600 pairs; stress-family part (iii) by
  simulation; the feedback-set construction against brute-force cycle packings on 600 random
  graphs; the rank bound of Remark 5.6 on 3000 random circuits.
- Left out: the "feedback-or-ready-cycle transfer" (source Thm 14) and Conjecture 15. The
  transfer is a conditional restatement of the open problem and relies on a strict transfer to
  P ⊆ SP whose RAM-time version is not established (see 004g). Readiness of many cycles at once is
  stated as open.

Not refereed. No human referee has checked it yet; the proofs were developed with the assistance
of an AI system.

## Code

Checking scripts used for this manuscript are in [`verification/`](verification/): `a5checks.py`, `graphchecks.py`, `rank_vs_fvs.py`. They are plain Python 3 with no dependencies outside the standard library unless the script says otherwise.
