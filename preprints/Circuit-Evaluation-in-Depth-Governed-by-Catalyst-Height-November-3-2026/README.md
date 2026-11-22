# [Circuit Evaluation in Depth Governed by Catalyst Height](paper.pdf)

**Author:** Generated Computers

**Date:** November 3, 2026

## Citation

```bibtex
@misc{GC:Circuit-Evaluation-in-Depth-Governed-by-Catalyst-Height-November-3-2026,
  author = {{Generated Computers}},
  title = {{Circuit Evaluation in Depth Governed by Catalyst Height}},
  howpublished = {Generated Computers preprint, manuscript 003e},
  year = {2026}
}
```



## Lean

Part of this paper is formalized in Lean 4 with Mathlib, in the [Lean library](../../lean/README.md). The scope is described in [`lean/docs/003.md`](../../lean/docs/003.md), and the main statements are in the Comparator challenge [`CatalystHeightCompiler.lean`](../../lean/ComparatorChallenges/CatalystHeightCompiler.lean). Every listed theorem is proved without `sorry` and uses only the axioms `propext`, `Quot.sound` and `Classical.choice`. Complexity-theoretic conclusions (logspace, NC, P-completeness and the like) are not formalized.

**003e (catalyst height).** Covers, heights and fractional certificates are defined on carrier graphs. The factor-two rounding theorem is proved: the threshold set is a catalyst cover meeting every path in at most `2d` nodes, and a cover of height `k` gives a fractional certificate of value `k`. Tightness is proved on one fusion of two sources (`d* = 1/2`, `χ = 1`). Only the "if" direction of the path-potential lemma is formalized. The core of the catalyst-height compiler is formalized as a combinatorial statement. Take a cover and any grading of it that strictly increases along proper ancestry, such as the levels `ℓ_H`. Then in round `r` every node of the cone `C_r` has at most one predecessor not yet known. Relative to the cover, every node has at most one unknown predecessor (joint composition). Two examples are also proved: a cover made of sources has height one (the accumulator), and every cover of the two-register recurrence of length `m` has height at least `m`. The PRAM depth bounds (`O((cht+1)log² n)`, functional closure in `O(log n)`) and NC checkability are not formalized.

## Sources

Rewritten from the following internal notes (document numbers of the 27 October 2026 corpus review):
- *Fusion Is Not the Event: The catalyst-cover hack, fractional certificates, and the true balanced core* (`old_stuff/Catalyst_Cover_Hack_20260822.pdf`, document #41): Definitions 1-2 and Lemma 3 (functional-DAG closure), Theorem 5 (joint catalyst composition), Theorem 6 (height compiler), Corollary 7 (role covers), Theorem 8 (accumulator), Definition 9, Theorem 10 and Corollary 11 (rounding and certificate), Theorem 13 (conditional transfer), pp. 2-8.

## Status

Proved in full: functional closure, joint composition, the catalyst-height compiler O((cht+1) log^2 n) (the proof gives O(log^2 n + cht log n)), role covers, the batch-side accumulator, factor-two rounding with tightness, and the NC-checkable potential certificate. The techniques are standard (pointer jumping, prefix scans, threshold rounding), and height one is close to skew circuits; the related work says so. Corrections: the source's claim that catalyst height strictly improves the earlier fusion-based parameter is replaced by the precise statement that catalyst height and fusion depth are incomparable (accumulator one way, matched rails the other); the source's boxed claim that catalyst height is the sequential charge is withdrawn, since matched rails have linear catalyst height and logarithmic depth (companion 003b). The conditional transfer (Theorem 13) is not stated as a theorem: its first branch is its conclusion, its catalyst branch alone has a false hypothesis (matched rails, also as A5 programs), and its other branches use undefined notions; the exact reduction to the open problem is stated instead. Left out: equality-assisted catalyst height (Theorem 12), which depends on an equality-saturation procedure from another note. Checked by computer: the level structure of the compiler and the rounding bound on 500 random circuits each. Not refereed.

## Code

Checking scripts used for this manuscript are in [`verification/`](verification/): `check_47_41.py`. They are plain Python 3 with no dependencies outside the standard library unless the script says otherwise.
