# [Newton's Method, Horn Saturation and Strahler Rank](paper.pdf)

**Author:** Generated Computers

**Date:** November 24, 2026

## Citation

```bibtex
@misc{GC:paper-3,
  author = {{Generated Computers}},
  title = {{Newton's Method, Horn Saturation and Strahler Rank}},
  howpublished = {Generated Computers, 2026},
  year = {2026}
}
```

## Abstract

We show that the Horton–Strahler rank is the round parameter of two exact fixed-point iterations.
Over $`\mathbb{F}_2`$, write a circuit of bounded fan-in as affine gates and binary products; then
the error of Newton's method satisfies $`J(x)e^{+} = Q(e)`$, where $`Q(e)`$ is nonzero only at
products of two wrong parents, so from any start Newton is exact after $`\rho+1`$ rounds, where
$`\rho`$ is the Strahler rank of the product skeleton; each round is a triangular solve of depth
$`O(\log^2 n)`$. The bound extends to arbitrary gates through a Taylor rank, to compressed
multiplexers, and to narrow rank frontiers given a valid layering. On Sequential NOR
($`x_0=1`$, $`x_i=\mathrm{NOR}(x_{i-1},x_{j_i})`$, P-complete) the identity is a first-collision
law: Newton finishes within $`\lceil n/2\rceil`$ rounds from every start, which is tight, and from
the standard start the worst case is exactly $`\lfloor (n-1)/2\rfloor`$ for $`n \ge 3`$. On
uniformly random instances the rank is $`(\sqrt{8/\pi}+o(1))\sqrt n`$, where one
law-of-large-numbers step of the proof is only sketched, yet Newton is exact after $`O(\log n)`$
rounds with probability $`1-o(1)`$ and needs at least $`\log_2\ln n-3`$; this gives errorless
average-case circuits of depth $`O(\log^3 n)`$ for a P-complete problem. Random instances have
linear binary core and live width, and the density of ones in the trace tends to
$`(3-\sqrt5)/2`$ almost surely.

Over the Boolean semiring, the facts of a Horn system with a derivation of Strahler rank at most
$`k`$ are exactly those reachable, in a graph built from the facts of rank below $`k`$, from the
seeds that these facts derive in one step; so rank $`K`$ costs $`K+1`$ reachability rounds, and over
all polynomial Horn encodings the least achievable rank equals parallel depth up to a factor
$`O(\log^2 N)`$. Inside one layer, vertex Menger gives an exact path–cut alternative for new
equalities in the value/equality calculus of $`A_5`$ programs, but the cut does not lift across
ranks: a one-fact separator can hide $`2^t`$ joint states. Compilers for closed proof portals are
proved conditionally on explicitly listed polynomial state sets; the surplus transfer that would
use them is sketched and stated as a conjecture. No class collapse is claimed.

## Main results

Numbers refer to `paper.pdf`.

- **Theorem A** (Theorems 3.8, 3.14): Newton–Strahler theorem for affine–product circuits over
  $`\mathbb{F}_2`$, from any start, with depth $`O((\rho+1)\log^2 n)`$ and size
  $`O((\rho+1)n^3\log n)`$. Proved in full. Also proved in full: the error identity (Lemma 3.5),
  rank as maximal derivation-tree dimension (Proposition 3.11), Taylor-rank extension
  (Theorems 3.18, 3.21), compressed multiplexers (Lemma 3.24, Theorem 3.25), frontier quotient for a
  supplied valid layering (Theorem 3.28). Remark 3.12 (zero start via the integer Newton map) relies
  on a counting identity that was checked by computer, not proved.
- **Theorem B** (Lemma 4.1, Theorem 4.2, Corollary 4.3, Theorem 4.10, Proposition 4.11):
  first-collision law, the bound $`\lceil n/2\rceil`$ from every start and its tightness, and the
  exact worst case $`\lfloor (n-1)/2\rfloor`$ from the standard start. Proved in full; also the
  contraction onto mixers and the coefficient formula (Theorem 4.7, Proposition 4.9).
- **Theorem C** (Theorem 5.1): Strahler rank of random instances is
  $`(\sqrt{8/\pi}+o(1))\sqrt n`$. **Sketch**: one law-of-large-numbers step is only sketched;
  Proposition 5.14(a) restates it with the same label.
- **Theorem D** (Theorems 5.11, 5.8, Remark 5.12): $`T_n = O(\log n)`$ with probability
  $`1-o(1)`$ from the standard and from a random start; $`T_n \ge \log_2\ln n - 3`$. Proved in full,
  with explicit constants; the arithmetic of the window-lemma recursion is machine-checked.
- **Corollary E** (Corollaries 5.13, 5.16): errorless average-case circuits of depth
  $`O(\log^3 n)`$; errorless $`\mathrm{NC}^{k+2}`$ with failure $`O(\log^{-k} n)`$; space
  $`O(\log^3 n)`$. Proved in full.
- Random structure, golden-ratio density, greedy MIS (Proposition 5.14(b,c), Theorem 5.15,
  Corollary 5.17): proved in full.
- **Theorem F** (Theorems 6.7, 6.9, 6.16, Proposition 6.12, Corollaries 6.8, 6.11): exact Strahler
  layers by reachability, the saturation algorithm, Boolean Newton iterates, and saturation rank
  equals parallel depth up to $`O(\log^2 N)`$ (a reformulation). Proved in full.
- **Theorem G** (Lemma 7.2, Theorem 7.4, Corollary 7.5, Theorem 7.6, Proposition 7.7): balanced-seed
  layer lemma, Menger inside one layer, side-premise star and its $`A_5`$ realization. Proved in
  full.
- Closed proof portals (Lemma 7.9, Theorems 7.10, 7.13, 7.15): proved in full, **conditional** on
  explicitly listed admissible state sets (hypotheses of the theorems). The surplus transfer
  (Lemma 7.16, Proposition 7.17, from the group-4 paper) is proved; its portal branch is only
  **sketched**, and Conjecture 7.18 is open.
- Interfaces between subproblems (Propositions 8.1–8.3, 8.6, Lemmas 8.4–8.5): proved in full;
  Remark 8.7 is a remark.
- **Numerical only**: about $`0.87\log_2 n`$ rounds for $`2^{16} \le n \le 2^{25}`$ and
  Conjecture 9.1 ($`T_n/\log_2 n \to c \approx 0.87`$).

## Consolidated from

| Preprint | Sections of this paper |
|---|---|
| [A P-Complete Problem in Average-Case NC](../../preprints/A-P-Complete-Problem-in-Average-Case-NC-November-3-2026/paper.pdf) | §1 (Theorems C–E, proof idea, related work), §2.3, §4.1 (Lemmas 4.4–4.5), §4.2, §4.5, §5, §9 (open problems, Conjecture 9.1), App. A, App. B(1)–(2) |
| [The First-Collision Law of Newton's Method over GF(2)](../../preprints/The-First-Collision-Law-of-Newtons-Method-over-GF-2-November-3-2026/paper.pdf) | §1, §2.3, §4.1, §4.3, §4.4, §8, App. B(2) |
| [Newton's Method Evaluates Circuits in Strahler-Rank Rounds](../../preprints/Newtons-Method-Evaluates-Circuits-in-Strahler-Rank-Rounds-November-3-2026/paper.pdf) | §1 (Theorem A, related work), §2.1–2.2, §3, §9, App. B(3) |
| [Horn Saturation in Strahler-Rank Reachability Rounds](../../preprints/Horn-Saturation-in-Strahler-Rank-Reachability-Rounds-November-3-2026/paper.pdf) | §1 (Theorem F, related work), §2.1–2.2, §6, §9, App. B(4) |
| [Menger's Theorem Inside One Strahler Layer](../../preprints/Mengers-Theorem-Inside-One-Strahler-Layer-November-3-2026/paper.pdf) | §1 (Theorem G, related work), §7, §9, App. B(5) |

## Lean

Parts of four constituents are formalized in Lean 4 with Mathlib, in the [Lean library](../../lean/README.md).
Complexity-theoretic conclusions are not formalized anywhere.

- [`lean/docs/001.md`](../../lean/docs/001.md) (random Sequential NOR): from the average-case NC
  manuscript, the error recursion (Lemma 4.4), the front identity (Lemma 4.5), the deterministic part
  of adaptedness (Lemma 5.3), the pathwise witness property (Lemma 5.7(i)), the Newton–Strahler bound
  for Sequential NOR (Proposition 4.6), the exact worst case (Proposition 4.11), the greedy-MIS
  identity (Corollary 5.17) and the final algebraic step of the golden-ratio theorem (Theorem 5.15).
  The probabilistic results (Theorems 5.1, 5.8, 5.11, the structure bounds, the density limit) are not
  formalized.
- [`lean/docs/002.md`](../../lean/docs/002.md) (Newton–Strahler): the error identity (Lemma 3.5),
  the Newton–Strahler theorem (Theorem 3.8), the valid-layering form of Remark 3.9(ii), the
  multilinear Taylor identity, the general error identity and the Taylor-rank contraction
  (Lemma 3.17, Theorems 3.18, 3.21); and for Horn saturation the exact layer theorem (Theorem 6.7),
  stabilization (Corollary 6.8), the Boolean Newton form (Proposition 6.12), the leaf bound
  (Lemma 6.3(b)), the round part of Corollary 6.11 and the truth-table lemma (Lemma 6.15). Depth and
  size accounting, Proposition 3.11, Remark 3.12, the multiplexer lemmas, the examples and the
  frontier quotient are not formalized.
- [`lean/docs/005.md`](../../lean/docs/005.md) (portals): the balanced-seed layer lemma (Lemma 7.2),
  the closure lemma (Lemma 7.9) and the derivability pattern of the side-premise star (Theorem 7.6).
  Menger's theorem is not in Mathlib, so Theorem 7.4 and Corollary 7.5 are not formalized; nor are the
  forest-mass lemma, the $`A_5`$ realization and the portal compilers.
- [`lean/docs/006.md`](../../lean/docs/006.md) (Sequential NOR normal forms): from the first-collision
  manuscript, the error identity (Lemma 4.1), the first-collision law (Theorem 4.2), Corollary 4.3 and
  the instance of Proposition 4.8. The contraction onto mixers, the coefficient formula, the tight
  family (Theorem 4.10) and Section 8 are not formalized.

## Notes on the merge

- **Structure.** One introduction states Theorems A–G; one preliminaries section defines the
  Horton–Strahler combination (previously defined separately in three manuscripts), the cost model
  (two manuscripts) and the Sequential NOR Newton map with the NOT-gate convention (two manuscripts).
  Results are grouped by theme: circuits (§3), Sequential NOR deterministic (§4), random instances
  (§5), Horn saturation (§6), one layer (§7), interfaces (§8).
- **Removed.** The five separate introductions, related-work sections, organization paragraphs and
  status notes; duplicate definitions of Sequential NOR, the Newton step and the rank; the
  verification-record appendix of the average-case manuscript (automated-review findings table F1–F10,
  the review of its Section 8, and the referee checklist) and every sentence about automated
  reviewers. The machine check of the window-lemma recursion is kept in App. B(1). The separate
  computer-check sections are merged into App. B. All theorems, lemmas, proofs, tables and remarks of
  substance are kept; the error identity appears both in matrix form (Lemma 4.1) and gate by gate
  (Lemma 4.4), and the Sequential NOR Newton–Strahler bound (Proposition 4.6) keeps its direct proof
  next to the general Theorem 3.8.
- **Notation.** The trace of the first-collision manuscript ($`y`$) is now $`x^*`$ throughout; the
  field is $`\mathbb{F}_2`$ throughout. In §7 the balanced seeds are $`S^{\mathrm b}_k`$ and the
  unary-spine graph is $`U_k`$, to avoid a clash with $`S_k`$ and $`G_k`$ of the Horn layer theorem;
  $`\mathcal F_{<k}=S_{k-1}`$ and $`\mathcal F_{\le k}=S_k`$. The symbol $`\mathcal F`$ denotes the
  filtration in §5 and the set of facts in §§6–7.
- **Moved inline from another group.** The charging lemma and the surplus transfer (Lemma 7.16,
  Proposition 7.17) of *Every Hypergraph Is an A5 Proof-Support System* (group 4), which the Menger
  manuscript used by citation, are stated and proved inline with their original proofs.
- **Cross-group citations.** Group 1 (Kleene–prefix iteration, average-case AC¹/SC², gap theorem,
  small-noise lower bounds); group 4 (A₅ value/equality calculus, predicate-complete gadget,
  proof-support systems, ancestor-cut compilation); group 5 (P-completeness of Sequential NOR, binary
  core and core-size ladder, live width and the average-case question, greedy-MIS form, reset-set
  iteration and its linear family, grid compilers); group 6b (square-root space, one rank layer as a
  monotone circuit, exponential-state portals); group 7a (extensional block tabulation). The internal
  memo cited as "Nine attacks" (not part of the collection) is kept as in the source.
- **Errors.** No mathematical error was found while merging. Corrections already made in the
  constituents (Taylor-rank convention, multiplexer hypotheses, frontier theorem for a supplied
  layering, the extra case in the Horn layer proof and in the balanced-seed layer lemma, the
  exact worst case $`\lfloor (n-1)/2\rfloor`$ replacing earlier finite claims) are kept, with their
  in-text remarks.
- **Status labels.** Theorem 5.1 carries "one step of the proof is sketched" in its title and its
  proof heading; Proposition 5.14(a) and the abstract repeat it. The portal theorems are conditional
  on their listed state sets; the portal branch of the surplus transfer is a sketch; Conjectures 7.18
  and 9.1 are conjectures, the latter numerical. Remark 3.12 depends on a computer-checked identity.
