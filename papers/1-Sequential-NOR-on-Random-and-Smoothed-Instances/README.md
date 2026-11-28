# [Sequential NOR on Random and Smoothed Instances](paper.pdf)

**Author:** Generated Computers

**Date:** November 28, 2026

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
$`O(\log n)`$ rounds with probability $`1-o(1)`$ (with very large constants), and the density of
ones in the trace tends to $`(3-\sqrt5)/2`$. For every $`\varepsilon > 3/4`$ an elementary
iteration whose rounds are prefix computations finishes in $`O(\log n)`$ rounds on the
$`\varepsilon`$-smoothing of every base, and there is a deterministic logspace algorithm that is
never wrong and gives up with probability at most $`3/n`$. With relevance pruning,
$`O(\log n)`$ rounds suffice on every base for every $`\varepsilon > 0.7288`$.

(2) *Hardness.* For every $`\varepsilon \le 0.4468`$, a randomized NC algorithm that outputs the
trace with probability only $`n^{-K}`$ on the $`\varepsilon`$-smoothing of every base gives
P ⊆ BPNC. Four embeddings of circuits reach noise $`1/64`$, $`1/4`$, every level below $`4/9`$,
and $`0.4468`$. The third keeps every value on two rails restored by chains of set–reset latches;
the fourth replaces the latch by chains that run a program of period 24, whose stages oscillate
between two states, and rests on a certificate computed in exact arithmetic. So, unless
P ⊆ BPNC, the critical noise level lies in $`[0.4468, 0.7288]`$; in particular it is neither
$`4/9`$ nor $`3/4`$. The same holds at each level $`\mathrm{NC}^k`$, $`k \ge 2`$. Below
$`0.4468`$ a polynomial speedup with near-linear work for smoothed instances would give one for
circuit evaluation.

(3) *The two natural iterations.* Against adaptive adversaries both need linearly many rounds. On
random block bases, fixed in advance, they need $`\Omega(n/\log n)`$ rounds below explicit noise
levels, and $`4/9`$ is the exact level of the relevance-pruned iteration on random block bases
over zero gates. A first-moment count of dependency chains cannot reach below about $`0.72`$ for
all bases. On fixed-distance bases with a large distance, a count of positions gives
$`O(\log n)`$ rounds from noise $`0.30`$ on; since $`0.30`$ is below the hardness level
$`0.4468`$, at those levels the hardness belongs to particular bases. A table iteration gives
$`O(\sqrt{\varepsilon n} + \log n)`$ rounds on the block bases. In the ideal model of the latch,
layered designs with independent reads forget their input from noise $`0.455`$ on, while the
design of period 24 keeps a bit up to about $`0.447`$; from $`0.455`$ on, an errorless NC
algorithm solves the smoothing of every layered base with wide bundles, so this method of proving
hardness stops between $`0.4468`$ and $`0.455`$.

None of this says anything about P versus NC in the worst case.

## Main results

Theorem numbers refer to [paper.pdf](paper.pdf).

- **Threshold 3/4** (Theorems 4.3, 4.6, 4.8; Corollaries 4.10, 4.11): the Kleene–prefix
  iteration finishes in $`O(\log n)`$ rounds on the $`\varepsilon`$-smoothing of every base for
  $`\varepsilon > 3/4`$, with explicit constants above $`\varepsilon_K \approx 0.7808`$; an
  errorless AC¹ algorithm. Proved.
- **Average-case logspace** (Theorem 5.8): for $`\varepsilon > 3/4`$ a deterministic logspace
  machine is never wrong and gives up with probability at most $`3/n`$. Proved.
- **Newton's method on random instances** (Theorems 6.3, 6.12, 6.15, 6.20): exact after
  $`O(\log n)`$ rounds with probability $`1-o(1)`$, at least $`\log_2\ln n - 3`$ rounds needed,
  the Strahler obstruction, and the golden-ratio density. Proved, except one law-of-large-numbers
  step of Theorem 6.3, which is marked as a sketch.
- **Every base above 0.7288** (Theorem 18.2): the relevance-pruned iteration finishes in
  $`O(\log n)`$ rounds on the $`\varepsilon`$-smoothing of every base for every
  $`\varepsilon > \varepsilon_1`$, $`\varepsilon_1 = 0.72878\ldots`$. Proved; the level is
  checked in exact rational arithmetic (`allbases_levels.py`). New in this version.
- **Hardness** (Theorems 7.10, 8.3, 9.11, 10.11, 11.12, 12.11): success probability $`n^{-K}`$
  on smoothings at noise up to $`0.4468`$ would give P ⊆ BPNC, through embeddings at $`1/64`$,
  $`3/20`$, $`1/4`$, the latch embedding below $`4/9`$, and the period-24 embedding at
  $`0.4468`$. Conditional on P ⊄ BPNC, as stated. The period-24 embedding rests on the
  certificate of Proposition 12.7 (`s24_check.py`). New in this version: the level $`0.4468`$.
- **Zero–one gap** (Corollary 12.12, Theorem 21.1): the critical noise level is $`0`$ if
  P ⊆ BPNC and otherwise lies in $`[0.4468, 0.7288]`$, also at each level $`\mathrm{NC}^k`$,
  $`k \ge 2`$.
- **Fixed-distance bases** (Theorems 15.9, 15.24, 15.28): on the base in which every gate reads
  a fixed large distance back, $`O(\log n)`$ rounds from noise $`0.455`$ (two rows) and from
  $`0.30`$ (three rows). Proved, resting on the potential certificates of Lemmas 15.23 and
  15.27 (`rows_check.c`, `rows3_check.c`). New in this version: the level $`0.30`$.
- **The two iterations** (Sections 13–17, 19): linear rounds against adaptive adversaries
  (Proposition 13.2); the chain-count barrier at about $`0.72`$ (Proposition 16.2); lower bounds
  on block bases with the exact level $`4/9`$ over zero gates (Theorems 17.8, 17.14); a table
  iteration (Theorem 19.2).
- **Layered designs** (Section 20; Theorems 20.7, 20.12, 20.18, 20.28, 20.31): independent reads
  forget their input from noise $`0.455`$; the method of proving hardness stops between
  $`0.4468`$ and $`0.455`$; a first bound for dependent reads (Theorem 20.31, `scan_check.c`, new
  in this version).
- **Levels of NC, speedups and greedy independent sets** (Section 21; Theorems 21.1, 21.3,
  Corollary 21.7): the work statements for polynomial speedups, and, new in this version, the
  lexicographically first maximal independent set on a path with one extra edge per vertex: as
  hard as the worst case up to $`0.4468`$ when the extra edges are smoothed, in NC from
  $`0.7288`$, and slow for the parallel greedy algorithm on some of these graphs below
  $`0.3819`$.

## Check of this version (28 November 2026)

This version replaces the 24 November version of paper 1. Before it was added, the source was
read in six parts by independent reviewers, who checked every proof step and recomputed the
constants with their own programs (not the programs in `verification/`).

- **No error was found in any theorem.** Independently reproduced: the level
  $`\varepsilon_1 = 0.7287762\ldots`$ and $`\kappa_2(0.7287) = 0.9573`$ of Section 18; the
  certificate of Proposition 12.7 for the period-24 embedding at $`\varepsilon = 3661/8192`$,
  in a separate implementation in exact interval arithmetic (all boxes and bounds agree); the
  latch threshold $`4/9`$ analytically; the constants of the threshold-3/4 tables; and all
  numerical claims of Sections 6–8 and 20.
- **Not reproduced.** The runs of `rows_check.c` and `rows3_check.c` behind the fixed-distance
  results were read but not re-run; the run of the three-row certificate on $`[0.30, 0.34]`$,
  which has the smallest margin, has no independent reproduction. The bound with the constant
  $`C_2`$ in Step 3 of the proof of Theorem 15.28 is stated without the full computation; a
  rough estimate shows it holds with room to spare. Both are said in the paper.
- **Corrections made in this version.**
  - The abstract, the introduction, Section 15 and Corollary 21.7 said the fixed-distance
    result starts at $`0.455`$; the theorem proves $`0.30`$.
  - "4/9 is the exact level" on block bases is proved only over zero gates; now stated so.
  - Theorem 7.15(b): the per-bit error is $`1/(3(n+1))`$, not $`1/(3n)`$.
  - In Section 21, $`\varepsilon_1 < 0.7288`$ (not $`= 0.7288`$), probability $`1-3/n`$ for the
    fixed-distance bases, and $`0 < \varepsilon < d^*`$; the noise model of the
    independent-set corollary is stated exactly, and the $`O(\log n)`$ bound for parallel greedy
    is credited to Fischer and Noever.
  - In Section 20, $`\alpha_d`$ is the probability of a zero, not a one; "as for independent
    reads" is now "as for the plain chain".
  - Smaller slips: a forward reference to $`\varepsilon_c`$, a wrong lemma part, a reversed table
    description, the description of the interval arithmetic of `s24_check.py`, a Chernoff
    exponent $`(f-1)/16`$, the order of a constant in Section 16, and several statements that rest
    on simulation are now marked as such.
  - Two claimed verification scripts that do not exist were removed from the text (the
    statements themselves were independently confirmed), and an over-precise simulation figure
    for the density was corrected.
  - The passages that reported checks by automated referees were removed or attributed to the
    programs that perform the checks.
- **Template.** The paper is set in the Generated Computers template, with section-based
  numbering, author–year citations and a BibTeX bibliography.

## Lean

The deterministic lemmas behind the NOR-tree and latch embeddings are proved in Lean 4 with the
core library only, in [`lean/`](lean/README.md): the exactness and domination lemmas of the
NOR-tree embedding (Section 9, `SeqNORTree.lean`), the refined cells of Section 10
(`SeqNORTree2.lean`), and the latch chains of Section 11 (`SeqNORLatch.lean`). The results of the
earlier family-001 preprints that are formalized in the main Lean library are described in
[`lean/docs/001.md`](../../lean/docs/001.md). The probabilistic steps, the certificates and the
complexity-theoretic conclusions are not formalized.

## Verification

[`verification/`](verification/README.md) holds the programs behind the computations (Appendix A
of the paper says what each does and how to run it), independent check programs, and records of
searches that are not part of any proof.

## Earlier preprints

This paper supersedes the four family-001 preprints, which remain in the repository:

| Preprint | Where it is in this paper |
| --- | --- |
| [A P-Complete Problem in Average-Case AC1 and SC2](../../preprints/A-P-Complete-Problem-in-Average-Case-AC1-and-SC2-November-3-2026/paper.pdf) | Sections 3–5, 14 |
| [A Gap Theorem for P versus BPNC](../../preprints/A-Gap-Theorem-for-P-versus-BPNC-November-3-2026/paper.pdf) | Sections 7–8 (extended in 9–12) |
| [Small Noise Defeats Two Natural Parallel Iterations](../../preprints/Small-Noise-Defeats-Two-Natural-Parallel-Iterations-November-3-2026/paper.pdf) | Sections 13, 17 |
| [A P-Complete Problem in Average-Case NC](../../preprints/A-P-Complete-Problem-in-Average-Case-NC-November-3-2026/paper.pdf) | Section 6 |

## Notes

- Section 6 (Newton's method on random instances) overlaps with the paper
  "Newton's Method, Horn Saturation and Strahler Rank" of this collection.
- Not refereed by a human. The results were developed with the assistance of an AI system.
