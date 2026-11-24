# [Sequential NOR on Random and Smoothed Instances](paper.pdf)

**Author:** Generated Computers

**Date:** November 24, 2026

## Citation

```bibtex
@misc{GC:paper-1,
  author = {{Generated Computers}},
  title = {{Sequential NOR on Random and Smoothed Instances}},
  howpublished = {Generated Computers, 2026},
  year = {2026}
}
```

## Abstract

Sequential NOR is the P-complete recurrence $`x_0 = 1`$, $`x_i = \mathrm{NOR}(x_{i-1}, x_{j_i})`$
with $`0 \le j_i < i`$ (Okhotin, 2011). We study it on random instances and on smoothed
instances, in which an adversary chooses the pointers and each pointer is then resampled with
probability $`\varepsilon`$.

(1) *Upper bounds.* On uniformly random instances Newton's method over GF(2) is exact after
$`O(\log n)`$ rounds with probability $`1-o(1)`$, and the density of ones in the trace tends to
$`(3-\sqrt5)/2`$. For every $`\varepsilon > 3/4`$ an elementary iteration whose rounds are prefix
computations finishes in $`O(\log n)`$ rounds on the $`\varepsilon`$-smoothing of every base, and
there is a deterministic logspace algorithm that is never wrong and gives up with probability at
most $`3/n`$.

(2) *Hardness.* For every $`\varepsilon < 4/9`$, a randomized NC algorithm that outputs the trace
with probability only $`n^{-K}`$ on the $`\varepsilon`$-smoothing of every base gives
P ⊆ BPNC. Three embeddings of circuits reach noise $`1/64`$, $`1/4`$ and every level below
$`4/9`$; the last keeps every value on two rails restored by chains of set–reset latches. So,
unless P ⊆ BPNC, the critical noise level lies in $`[4/9, 3/4]`$, and the same holds at each
level $`\mathrm{NC}^k`$, $`k \ge 2`$. Below $`4/9`$ a polynomial speedup with near-linear work for
smoothed instances would give one for circuit evaluation.

(3) *The two natural iterations.* Against adaptive adversaries both need linearly many rounds. On
random block bases, fixed in advance, they need $`\Omega(n/\log n)`$ rounds below explicit noise
levels, and $`4/9`$ is the exact level of the relevance-pruned iteration there. A first-moment
count of dependency chains cannot reach below about $`0.72`$ for all bases. A table iteration
gives $`O(\sqrt{\varepsilon n} + \log n)`$ rounds on the block bases. In the ideal model of the
latch, layered designs with independent reads forget their input from noise $`0.455`$ on, while
numerically a design of period 24 keeps a bit up to about $`0.447`$.

None of this says anything about P versus NC in the worst case.

## Main results

Theorem numbers refer to [paper.pdf](paper.pdf).

- **Threshold 3/4** (Theorems 10, 13, 15; Section 4): the Kleene–prefix iteration finishes in
  $`O(\log n)`$ rounds on the $`\varepsilon`$-smoothing of every base for $`\varepsilon > 3/4`$,
  with explicit constants above $`\varepsilon_K \approx 0.7808`$. Proved.
- **Average-case logspace** (Theorem 26): for $`\varepsilon > 3/4`$ a deterministic logspace
  machine is never wrong and gives up with probability at most $`3/n`$. Proved.
- **Newton's method on random instances** (Theorems 45, 42, 33, 50; Section 6): exact after
  $`O(\log n)`$ rounds with probability $`1-o(1)`$, at least $`\log_2\ln n - 3`$ rounds needed,
  the Strahler obstruction, and the golden-ratio density. Proved, except one law-of-large-numbers
  step in Section 6, which is marked as a sketch.
- **Hardness** (Theorems 63, 72, 86, 100, 107, 114; Sections 7–11): success probability
  $`n^{-K}`$ on smoothings at noise below $`4/9`$ would give P ⊆ BPNC, through embeddings at
  $`1/64`$, $`3/20`$, $`1/4`$ and the latch embedding below $`4/9`$. Conditional on
  P ⊄ BPNC, as stated.
- **Zero–one gap** (Theorems 68, 182): the critical noise level is $`0`$ if P ⊆ BPNC and
  otherwise lies in $`[4/9, 3/4]`$, also at each level $`\mathrm{NC}^k`$, $`k \ge 2`$.
- **The two iterations** (Sections 12–17): linear rounds against adaptive adversaries; bounds
  below $`3/4`$ for fixed-distance and ordered bases (Theorems 132, 139); short pointers
  (Theorem 148); lower bounds on block bases with the exact level $`4/9`$ for the pruned
  iteration (Theorems 157, 158, 163); a table iteration (Theorem 169).
- **Layered designs and work** (Sections 18–19; Theorems 178, 184): independent reads forget
  their input from noise $`0.455`$; the work statements for polynomial speedups.

## Consolidated from

| Preprint | Where it is in this paper |
| --- | --- |
| [A P-Complete Problem in Average-Case AC1 and SC2](../../preprints/A-P-Complete-Problem-in-Average-Case-AC1-and-SC2-November-3-2026/paper.pdf) | Sections 3–5, 13 |
| [A Gap Theorem for P versus BPNC](../../preprints/A-Gap-Theorem-for-P-versus-BPNC-November-3-2026/paper.pdf) | Sections 7–8 (extended in 9–11) |
| [Small Noise Defeats Two Natural Parallel Iterations](../../preprints/Small-Noise-Defeats-Two-Natural-Parallel-Iterations-November-3-2026/paper.pdf) | Sections 12, 16 |
| [A P-Complete Problem in Average-Case NC](../../preprints/A-P-Complete-Problem-in-Average-Case-NC-November-3-2026/paper.pdf) | Section 6 |

The paper goes beyond these preprints: the hardness range grows from noise $`1/64`$ to every level
below $`4/9`$ (Sections 9–11), success probability $`n^{-K}`$ suffices (Section 8), and Sections 5,
14, 15, 17, 18 and 19 are new.

## Lean

The deterministic lemmas behind the NOR-tree and latch embeddings are proved in Lean 4 with the
core library only, in [`lean/`](lean/README.md): the exactness and domination lemmas of the
NOR-tree embedding (Section 9, `SeqNORTree.lean`), the refined cells of Section 10
(`SeqNORTree2.lean`), and the latch chains of Section 11 (`SeqNORLatch.lean`). The results of
the constituent preprints that are formalized in the main Lean library are described in
[`lean/docs/001.md`](../../lean/docs/001.md). The probabilistic steps and the complexity-theoretic
conclusions are not formalized.

## Notes

- This paper is distributed as a PDF; its LaTeX source is not in this repository.
- Section 20 of the paper lists the computations in exact and interval arithmetic it relies on.
  The scripts of the constituent preprints are in their `verification/` folders under
  [`preprints/`](../../preprints/).
- Section 6 (Newton's method on random instances) overlaps with the paper
  "Newton's Method, Horn Saturation and Strahler Rank" of this collection, which contains the same
  preprint as part of its Strahler-rank theme.
