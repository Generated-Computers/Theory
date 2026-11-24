# [Normal Forms and NC Compilers for Sequential NOR](paper.pdf)

**Author:** Generated Computers

**Date:** November 24, 2026

## Citation

```bibtex
@misc{GC:paper-5,
  author = {{Generated Computers}},
  title = {{Normal Forms and NC Compilers for Sequential NOR}},
  howpublished = {Generated Computers, 2026},
  year = {2026}
}
```

## Abstract

Sequential NOR, $`x_0=1`$ and $`x_i=\mathrm{NOR}(x_{i-1},x_{j_i})`$ with $`0\le j_i<i`$, is a P-complete
circuit value problem. We give its structure theory in two parts. Part I gives normal forms and
hardness results. On two pages the problem is already P-complete under logspace reductions, while
one-page instances are in logspace, and recognizing $`k`$ pages is NP-complete for every fixed
$`k\ge4`$. The trace is the parity of the distance to the last reset, and the reset set is the unique
fixed point of an operator computable in $`\mathrm{NC}^1`$; exactly $`F_{N+1}`$ words occur as traces, and
the parent arrays with a given trace form an explicit product. Up to a logspace-uniform
$`\mathrm{NC}^2`$ shell the problem is evaluation of an ordered NOR circuit with exactly $`|B(j)|`$ gates,
one per unguarded anchor, and every ordered NOR circuit arises in this way with four coordinates
per gate. For binary-table sequential circuits, a cut contracts the suffix exactly to $`q(b)`$ gates
in $`O(n)`$ work and $`O(\log n)`$ depth; uniform-lag instances are cyclic rotations of a tiling by
$`10`$ and $`100`$ and are periodic from index $`2D`$ on.

Part II gives compilers for restricted instances, all of them promise theorems: $`k`$-switch phase
repair in $`k`$ rounds; depth $`O(\log^2 n+r)`$ for $`|B(j)|\le r`$, hence $`\mathrm{NC}^{\max(2,c)}`$ for
$`|B(j)|=O(\log^c n)`$ and logspace for $`|B(j)|=O(\log n)`$; compilers for core depth, formula cores,
interaction covers, sharing, treewidth and modulators, interface repair, live-interval deletion and
elimination-order defects; quasiNC compilers for few long paths and for small recursive
separators; and grid compilers, including an $`\mathrm{NC}^1`$ compiler for homogeneous grids and a
runwise portfolio in $`\mathrm{FNC}^k`$. The grid normal form embeds into Sequential NOR but is not
known to be P-hard, so the grid compilers are not known to apply to any hard instance.
Work-efficient evaluation of indexed linear algebraic circuits is stated as a conjecture; a few
depth bounds rely on imported balancing modules whose depth is kept explicit. Nothing here places
unrestricted Sequential NOR in NC or quasiNC.

## Main results

Theorem numbers refer to [paper.pdf](paper.pdf). Everything is proved in full unless a status is
given.

**Part I: normal forms and hardness**

- Greedy independent sets and the jump rule (Proposition 3.1, Lemma 3.3); a self-contained proof of
  Okhotin's P-completeness theorem (Theorem 3.6); live-width bound, space $`O(L(j)+\log n)`$
  (Proposition 3.9). Proved in full.
- Page number: one page is in L (Theorem 4.2, using the logspace Courcelle theorem of Elberfeld,
  Jakoby and Tantau); two pages are P-complete, also with the page assignment given (Theorem 4.15);
  deciding $`\mathrm{pg}(j)\le k`$ is NP-complete for fixed $`k\ge4`$ (Proposition 4.1); arrays with one NOR
  gate per cell are in NC (Proposition 4.6), which refutes an earlier four-page argument unless
  P = NC. Proved in full; the complexity of recognizing three pages is open.
- quasiNC = polyL under polylog-space uniformity (Theorem 5.2, Borodin); reset-predecessor normal
  form, event queue, reset operator with unique fixed point in $`\mathrm{NC}^1`$ and first-disagreement
  lemma (Theorem 5.4, Propositions 5.5–5.6, Lemma 5.7); active-one and live-error compilers of size
  $`n^{O(w+1)}`$ and depth $`O((w+1)\log^2 n)`$ (Theorems 5.11, 5.13); two barriers (Theorems 5.16,
  5.18). Proved in full; the round count $`\lceil n/3\rceil`$ in Remark 5.9(a) is computed for
  $`n\le300`$, not proved.
- Census of traces $`F_{N+1}`$ and product fibres (Theorems 6.1, 6.2); exact list-decoding capacities
  with and without adaptive queries (Theorems 6.6, 6.10), fractional-cover capacity for randomized
  query policies (Theorem 6.12), spectrum sandwich (Theorem 6.13). Proved in full. Remark 6.15
  (potential closures) is a standard observation, not a theorem.
- Binary-core retraction in $`\mathrm{NC}^2`$ (Theorem 7.4) and four-coordinate universality (Theorem 7.7),
  with the exact retraction, P-completeness, structural boundary and collapse corollaries
  (Corollaries 7.8–7.10, Proposition 7.11). Proved in full.
- Affine-product normal form and exact multiplicative complexity of the NOR chain (Proposition 8.1,
  Lemma 8.3, Proposition 8.4). Proved in full.
- Exact cut externalization (Theorem 9.3), cut-norm recursion (Theorem 9.5), padding
  counterexample to the quadratic-span claim (Proposition 9.7) and corrected hereditary statement
  (Corollary 9.8); trace-resolved register stack machine computations as linear algebraic circuits
  (Theorem 9.11), NC with polynomial work (Proposition 9.12), elimination rounds (Lemma 9.13,
  Corollary 9.14). Proved in full. **Conjecture 9.15** (linear-work, sublinear-depth evaluation of
  indexed linear algebraic circuits) is a conjecture.
- NOR tiling rotation and periodicity from index $`2D`$ (Theorem 10.7, Corollary 10.8); all sixteen
  homogeneous rules (Theorem 10.12); polarity-gauge conjugacy and the gauge-cover compiler
  (Theorems 10.15, 10.17, Proposition 10.18). Proved in full.

**Part II: compilers for restricted instances** (all are promise theorems)

- Greedy phase repair: $`k`$ switches are repaired in exactly $`k`$ rounds (Theorem 11.6). Proved in full.
- Small cores: blockwise guessing (Theorem 12.5, depth $`O(\log^2 n+r\log n)`$) and the abstract
  block-lifting lemma (Theorem 12.11); binary-core block compiler, depth $`O(\log^2 n+r)`$
  (Theorem 12.13), core-size ladder $`\mathrm{NC}^{\max(2,c)}`$ (Corollary 12.14), logarithmic cores in
  logspace (Proposition 12.12), polynomial-list completion as a conditional reduction
  (Proposition 12.16). Proved in full.
- Structural parameters of the core (Sections 13–15; table in Section 13): core depth, formula
  cores, interaction covers (Theorems 13.7, 13.9, 13.12), sharing count, depth and frontier
  (Theorems 13.15, 13.17, 13.18), balanced interval interfaces (Theorem 14.4), treewidth of the
  relevant and of the full core (Theorems 14.6, 14.7), modulators (Theorem 14.8), cotree covers
  (Theorems 14.13, 14.15), interface repair (Theorems 14.18, 14.19), live intervals and their
  optimizers (Theorems 15.2–15.17, Proposition 15.18), order defects (Theorems 15.20, 15.22). Proved
  in full, using imported modules stated as Facts 13.1 and 13.3 (Buss's formula evaluator; the
  logspace theorems of Elberfeld, Jakoby and Tantau; logspace in $`\mathrm{NC}^2`$; balanced tree
  decompositions); Theorems 14.8(b) and 15.22 keep the depth $`D_{\mathrm{bal}}`$ of the imported
  balancing module explicit and also give a bound without it. The randomized
  $`\mathrm{RNC}^2`$ optimizer is a remark only.
- Few long paths: anchor deletion compiler (Theorem 16.3), path-hitting identity, bounded search
  tree and packing sandwich (Theorems 16.4–16.6, Corollary 16.7), path family and a non-degenerate
  example (Theorem 16.9, Proposition 16.11), recursive-separator compiler (Theorem 16.13), portfolio
  (Theorem 16.14). Proved in full; quasiNC for polylogarithmic parameters.
- Grids: homogeneous templates in $`\mathrm{NC}^1`$ (Theorem 17.14), threshold-reset composition
  (Theorem 17.16, Corollary 17.17), embedding into Sequential NOR (Proposition 17.7); row-partition
  compiler (Theorem 18.4), Fibonacci-carrier algebra (Lemma 18.7, Propositions 18.8, 18.10, 18.11,
  Theorem 18.9), common-core compiler in $`\mathrm{FNC}^2`$ (Theorem 18.12), absorbing collars in
  $`\mathrm{FNC}^k`$ (Theorem 18.17), runwise portfolio in $`\mathrm{FNC}^k`$ and its strictness (Theorem 18.21,
  Proposition 18.23), common cores in the $`\Gamma`$ class (Proposition 18.24). Proved in full.
  **Caveat:** the grid normal form is not known to be P-hard, so these compilers are not known to
  apply to any hard instance.
- Barriers: INDEX gadget, full transformation monoid, equality quotients (Propositions 19.1–19.3).
  Folklore, proved in full; not circuit lower bounds.

## Consolidated from

| Preprint | Sections of this paper |
|---|---|
| [Two Pages Suffice for P-Completeness](../../preprints/Two-Pages-Suffice-for-P-Completeness-November-3-2026/paper.pdf) | 2.1 (elementary facts), 3, 4, 20 (open problems), App. A |
| [A Reset Normal Form for a P-Complete Problem](../../preprints/A-Reset-Normal-Form-for-a-P-Complete-Problem-November-3-2026/paper.pdf) | 5, App. A |
| [Sequential NOR Has Exactly Fibonacci-Many Traces](../../preprints/Sequential-NOR-Has-Exactly-Fibonacci-Many-Traces-November-3-2026/paper.pdf) | 6, App. A |
| [Sequential NOR Is Circuit Evaluation on Its Binary Core](../../preprints/Sequential-NOR-Is-Circuit-Evaluation-on-Its-Binary-Core-November-3-2026/paper.pdf) | 2.2 (core, root classification), 7, 12.6, App. A |
| [Homogeneous Sequential NOR Grids Lie in NC1](../../preprints/Homogeneous-Sequential-NOR-Grids-Lie-in-NC1-November-3-2026/paper.pdf) | 8 (affine-product form), 17, App. A |
| [Exact Cut Contraction for P-Complete Sequential Circuits](../../preprints/Exact-Cut-Contraction-for-P-Complete-Sequential-Circuits-November-3-2026/paper.pdf) | 3.1 (greedy MIS remark, jump rule), 9, App. A |
| [NOR Shift Registers Are Tiling Rotations](../../preprints/NOR-Shift-Registers-Are-Tiling-Rotations-November-3-2026/paper.pdf) | 10, App. A |
| [Parameterized NC Compilers for a P-Complete Problem](../../preprints/Parameterized-NC-Compilers-for-a-P-Complete-Problem-November-3-2026/paper.pdf) | 2.3 (standard modules), 11, 13, 14, 15, 20, App. A |
| [Blockwise Guessing Puts Low-Defect Sequential NOR in NC](../../preprints/Blockwise-Guessing-Puts-Low-Defect-Sequential-NOR-in-NC-November-3-2026/paper.pdf) | 12.1–12.5, 20, App. A |
| [Few Long Paths Put Sequential NOR in QuasiNC](../../preprints/Few-Long-Paths-Put-Sequential-NOR-in-QuasiNC-November-3-2026/paper.pdf) | 16, App. A |
| [Three NC Compilers for Sequential NOR Grids](../../preprints/Three-NC-Compilers-for-Sequential-NOR-Grids-November-3-2026/paper.pdf) | 18.1–18.5, 19, App. A |
| [A Runwise Portfolio of NC Grid Compilers](../../preprints/A-Runwise-Portfolio-of-NC-Grid-Compilers-November-3-2026/paper.pdf) | 18.6–18.8 |

## Lean

Parts of the constituent results are formalized in Lean 4 with Mathlib in the [Lean
library](../../lean/README.md); complexity-theoretic conclusions (logspace, NC, P-completeness,
work and depth) are not formalized in any family.

- [`lean/docs/006.md`](../../lean/docs/006.md) (P-completeness and normal forms; 006a, 006b, 006e,
  006f, 006g): the serpentine two-page construction with its values and page assignment, the
  gadgets, Okhotin's five-cell reduction and the NOR-only parity normalization (Sections 3–4); the
  reset-predecessor and event-queue normal forms, the unique fixed point of the reset operator, the
  first-disagreement lemma and the realizable-trace construction (Section 5); the root
  classification, descriptor equation, triangularity, the mathematical content of the retraction
  theorem and four-coordinate universality (Section 7); bad shields, prefix locality, the
  unique-valid-branch lemma and correctness of the blockwise schedule (Section 12.1–12.3); the
  path-hitting identity, the packing sandwich and the path formula (Section 16). In 006a the
  serpentine instance is called $`\Phi`$; here it is $`\Sigma`$.
- [`lean/docs/007.md`](../../lean/docs/007.md) (structural compilers; 007a): the unique fixed point of
  $`\Phi_j`$ and greedy phase repair (Section 11), and the interaction-cover lemma and corrected
  residual evaluator of Theorem 13.12 with the counterexample of Remark 13.13. The other compilers
  of Sections 13–15 are not formalized.
- [`lean/docs/009.md`](../../lean/docs/009.md) (grid compilers and trace counting; 009a–009d): the
  exact grid facts behind the homogeneous-template compiler and threshold resets (Section 17); the
  bounds on $`\Gamma`$, the injective rows, the constant two-row block, the INDEX gadget and the
  counting parts of Proposition 19.1 (Sections 18–19); the abstract finite-portfolio lemma and the
  $`\Gamma`$ bounds of the runwise portfolio (Section 18.6–18.8); the census and fibre theorems, causal
  projection and the deterministic list-decoding capacity (Section 6). No circuit, depth or
  uniformity statement is formalized.
- [`lean/docs/010.md`](../../lean/docs/010.md) (010b): the tiling-rotation theorem, the collapse of the
  six rules, unique NOR polarity, polarity-gauge conjugacy and the minimality of the greedy cover
  (Section 10); periodicity is proved there from index $`2D-1`$ on, one index earlier than stated here.
- [`lean/docs/011.md`](../../lean/docs/011.md) (011b): exact cut externalization as a correctness
  statement, the crossing-area identity, the padding counterexample, and the greedy-MIS identity
  and jump rule (Sections 3.1 and 9). Costs, the cut-norm recursion and the linear-algebraic part
  are not formalized.

The Lean documents refer to the theorem numbers of the original preprints.

## Notes on the merge

- **Structure.** The twelve manuscripts were reorganized into one paper with a single
  preliminaries section (parent arrays and traces, the elementary facts, syntactic classes, the
  binary core and bad shields, the root classification, the circuit model, promise classes and the
  standard modules) and two parts. Labels of the source manuscripts were kept internally with a
  prefix per source.
- **Removed as duplication.** The twelve introductions and their repeated definitions of Sequential
  NOR; the repeated definitions of resets, anchors, the binary core and bad shields
  (Blockwise, Parameterized, Few Long Paths); the restatement of binary-core compression in the
  Parameterized manuscript (its Theorem 2.5, replaced by references to Section 7); the second proof
  of the greedy-MIS identity in Exact Cut (identical to Proposition 3.1); the restated companion
  results of the grid manuscripts (imported homogeneous-slab and threshold-reset theorems, the
  "two arms" theorem and the "two row facts" of Runwise, now references to Sections 17–18); the
  repeated definition of active-run compilers; the duplicate Fibonacci-number conventions; the
  four-step P-completeness gadget of the shift-register manuscript; the proof of the
  unique-fixed-point lemma for reset masks (Lemma 11.2), which is the reset normal form of Section 5
  in mask notation and now cites it; the list of corrections relative to the source notes at the end
  of the Parameterized manuscript (each correction is still explained where it occurs).
- **Removed review material.** The status footnotes, including the sentence about an independent
  automated check of the two-page construction; the scripts of that independent check are kept in
  `verification/two_pages_independent/` and are described neutrally in Appendix A. No findings
  tables or review appendices were present in the sources.
- **Renamed symbols.** The serpentine instance of Section 4 is $`\Sigma`$ (was $`\Phi`$, which also names
  the reset operator); the fill of an elimination set in Section 9 is $`\mathrm{fill}(S)`$ (was
  $`\Phi(S)`$, which clashed with the cut maps $`\Phi_i`$ of the same section); the unguarded anchors of
  Few Long Paths, written $`G(j)`$ there, are $`B(j)`$ here; the one-argument evaluation bracket of
  the Parameterized manuscript is a separate macro. Bibliography keys were unified (e.g.
  `GHR1995`, `ladner1975circuit` → `GreenlawHooverRuzzo1995`, `Ladner1975`).
- **Errors fixed.** None of mathematical substance was found while merging. The verification
  script of Few Long Paths imported `check_core.py`, which was not in its folder; the merged
  `verification/` contains it, so the script now runs.
- **Cross-group citations.** Space bounds near $`\sqrt n`$ and the rank encoding: cited as group 6b
  (*NC Fragments of SC and Control-Trace Reductions*). Random instances: group 1 (*Sequential NOR on Random and Smoothed Instances*, errorless $`O(\log^2 n)`$-space algorithm) and group 3 (*Newton's
  Method, Horn Saturation and Strahler Rank*, linear live width of random instances). Segment cuts
  and Unique-Games barriers for structural parameters: group 7a (*Barriers to Speeding Up Circuit
  Evaluation*). No result was moved inline from another group.
- **Status labels that matter.** The grid compilers (Sections 17–18) are not known to apply to any
  hard instance because the grid normal form is not known to be P-hard; this caveat is repeated in
  the abstract, the introduction, Sections 17, 18 and 20. Conjecture 9.15 is a conjecture. Remark 5.9(a)
  contains a computed, unproved round count. Polynomial-list completion (Proposition 12.16), the
  proposal criterion (Corollary 11.8), the baseline-portfolio corollary (Corollary 5.14) and the
  potential closures (Remark 6.15) are conditional or reformulations of the open problem, as stated
  in the text.
