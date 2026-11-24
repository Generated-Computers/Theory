# [A₅ Circuits Between NC² and P-Completeness](paper.pdf)

**Author:** Generated Computers

**Date:** November 24, 2026

## Citation

```bibtex
@misc{GC:paper-4,
  author = {{Generated Computers}},
  title = {{$A_5$ Circuits Between $\mathrm{NC}^2$ and P-Completeness}},
  howpublished = {Generated Computers, 2026},
  year = {2026}
}
```

## Abstract

Evaluating straight-line programs over the alternating group $`A_5`$ is P-complete, even when the
only inputs are two fixed generators. We map which structure brings such programs down to NC² and
which leaves the whole problem intact. A program with one entry computes powers of it, with
exponents computed in NC²; in a two-generator program every node not immediately dominated by the
source is a fixed power of its prime root, and the program is evaluated in depth
$`O(h+\log^2 n)`$ with $`h`$ prime nodes, while constant-free two-entry programs are already
P-complete. On the 1320 non-generating pairs a two-entry program is tabulated in NC², but the 2280
generating pairs form 19 independent $`\mathrm{Aut}(A_5)`$-orbits (P. Hall), so words in the second
derived subgroup can vanish on all easy pairs and take arbitrary values on the orbits. Commutator
towers put every node of a linear-size P-complete program into the $`s`$-th derived subgroup of the
free group, so every solvable or nilpotent image of polynomial size is blind. A fixed block of 61
probes makes its unique pigeonhole collision encode an arbitrary value, so finding a collision is
P-hard; equality facts with proofs of Strahler rank $`K`$ are found in depth
$`O((K+1)\log^2 n)`$, every hypergraph is the support system of such proofs, and opening a factor
cycle can leave a P-complete coefficient.

On the positive side we give compilers charged only to explicit parameters: two-register corridor
fusions, ancestrally liftable kernels and cuts, logarithmic portals, and the semantic Strahler rank
$`r`$ with respect to a supplied congruence (depth $`O((r+1)\log^2 s)`$; finding the congruence is
not included). A depth-$`s^{1-\varepsilon}`$ evaluator for $`A_5`$ circuits would speed up
multitape Turing machines, which is weaker than $`\mathsf{P}\subseteq\mathsf{SP}`$. Conditional
parts: the surplus law assumes an open hypothesis on collapse mass, one charging instantiation is
only sketched, one statement is a conjecture, and the prime-core fractions are measurements.

## Main results

Numbers refer to [paper.pdf](paper.pdf).

- **Boolean basis and two-generator normal form** (Thm 3.3, Cor 3.4, Thm 3.5, Cor 3.6): NOT and
  AND with at most 3 and 13 gates; every $`A_5`$ circuit of size $`s`$ becomes a two-generator SLP of
  size at most $`s+64`$; two-generator SLPs are P-complete with output promised in
  $`\{e,a\}`$. Proved in full (folklore after Barrington and Beaudry–McKenzie–Péladeau–Thérien).
- **Transfer relative to Turing-machine time** (Thm 3.7): proved, relying on the logspace
  uniformity of the Pippenger–Fischer network, which is quoted. Remark 3.8 explains why this does
  not give $`\mathsf{P}\subseteq\mathsf{SP}`$.
- **Shared commutator tower, deep perfect reduction, $`\textsc{DeepCore}_{1/305}`$
  P-complete, shadow annihilation** (Thms 4.2, 4.3, 4.4, Cor 4.5, Thm 4.6, Cor 4.7): proved in full.
- **One-entry power normal form and compiler, dominator power condensation, prime core, NC²
  construction, evaluation in depth $`O(h(C)+\log^2 n)`$, one-versus-two entry dichotomy**
  (Thm 5.1, Cor 5.2, Thms 5.3, 5.6, 5.7, 5.8, Cor 5.9, Thm 5.10): proved in full. The prime-node
  fractions 72–76% in Remark 5.11 are **measurements**.
- **Two-register scans, unit-power reversibility, pair-corridor fusion compiler, cold-sector
  compiler** (Thms 6.2, 6.6, 6.8, 6.10): proved in full (elementary; the cold-sector compiler quotes
  the DET bound of Beaudry–McKenzie–Péladeau–Thérien).
- **Nineteen-channel independence** (Thm 6.12, P. Hall 1936, with a self-contained proof) and
  **mirror words, selectors, no interpolation** (Thm 6.14, Cors 6.15, 6.16): proved in full.
- **61-probe selector, P-hardness of collision search, predicate-complete equality** (Thm 7.2,
  Cor 7.4, Thm 7.5): proved in full, resting on the Maurer–Rhodes theorem (quoted); the probe terms
  were not computed.
- **Context-signature contraction, calculus soundness and completeness, P-completeness of the full
  closure, rank-$`K`$ saturation, exact component collapse** (Thm 7.7, Cor 7.8, Thm 7.9, Prop 7.10,
  Thms 7.12, 7.14): proved in full.
- **Surplus law** (Thm 7.18, Cor 7.19): **conditional**; the hypothesis is open.
- **Support redundancy, hypergraph realization, star-transversal barrier, logarithmic and liftable
  ancestor-cut compilers, charging lemma, surplus transfer** (Prop 8.1, Thm 8.3, Thm 8.5, Thms 8.9,
  8.11, Lemma 8.12, Prop 8.13): proved in full. The instantiation with logarithmic ancestor cuts
  (alternative (iv) in Sec. 8.5) is only a **sketch**; Conjecture 8.14 is a **conjecture**.
- **Symbolic cycle opening, hard-coefficient cycle, ancestral-kernel compiler, mixer-strip
  barrier, Nielsen embedding and transfer** (Thm 9.3, Cor 9.4, Thm 9.5, Cor 9.6, Thms 9.9, 9.12,
  9.14, Prop 9.15): proved in full; the claimed equivalence with $`\mathsf{P}\subseteq\mathsf{SP}`$
  is only discussed **conditionally** on hypothesis (H) in Remark 9.16.
- **Portal-chain collapse, semantic Strahler compiler, congruence check, unfolding bound**
  (Thm 10.2, Cor 10.3, Thm 10.8, Prop 10.9, Cor 10.11): proved in full; the cost of finding the
  congruence is excluded (Remark 10.10).

## Consolidated from

| Preprint | Sections of this paper |
|---|---|
| [Finding Pigeonhole Collisions in A₅ Is P-Complete](../../preprints/Finding-Pigeonhole-Collisions-in-A5-Is-P-Complete-November-3-2026/paper.pdf) | 3.1–3.2 (gadget lemma and normal-form lemma, merged), 7, App. A |
| [P-Complete A₅ Circuits Invisible to Solvable Groups](../../preprints/P-Complete-A5-Circuits-Invisible-to-Solvable-Groups-November-3-2026/paper.pdf) | 2.1 (series, Lemma 2.1), 3.2, 4, App. A |
| [Nineteen Orbits: Block Interpolation for A₅ Circuits](../../preprints/Nineteen-Orbits-Block-Interpolation-for-A5-Circuits-November-3-2026/paper.pdf) | 6, App. A |
| [A₅ Programs: One Entry in NC², Two Entries P-Complete](../../preprints/A5-Programs-One-Entry-in-NC2-Two-Entries-P-Complete-November-3-2026/paper.pdf) | 2.3 (matrix powering), 5, App. A |
| [Every Hypergraph Is an A₅ Proof-Support System](../../preprints/Every-Hypergraph-Is-an-A5-Proof-Support-System-November-3-2026/paper.pdf) | 8, App. A |
| [Opening A₅ Cycles Leaves a P-Complete Coefficient](../../preprints/Opening-A5-Cycles-Leaves-a-P-Complete-Coefficient-November-3-2026/paper.pdf) | 9, App. A |
| [Barrington Gadgets Meet Strahler Rank](../../preprints/Barrington-Gadgets-Meet-Strahler-Rank-November-3-2026/paper.pdf) | 3.1, 3.3, 10, App. A |

## Lean

Parts of the constituent results are formalized in Lean 4 with Mathlib, in the
[Lean library](../../lean/README.md); complexity-theoretic conclusions (logspace, NC,
P-completeness, depth bounds) are not formalized.

- **Family 004, straight-line programs over A₅** ([`lean/docs/004.md`](../../lean/docs/004.md)),
  covering Sections 3–7, 9 and 10. Formalized: the Maurer–Rhodes theorem, the 61-probe selector,
  predicate-complete equality, the universal-collision count, soundness and completeness of the
  value/equality calculus and the gadget compilation (from 004a); every element of A₅ a commutator,
  the commutator tower's values and derived depth, $`G^{(d)}\le\gamma_{2^d}(G)`$ and shadow
  annihilation, and the normal form (004b); Hall's theorem in general, the 19 orbits and the mirror
  words, power permutations and unit-power reversibility (004c); the one-generator power normal
  form and dominator power condensation (004d); the hard-coefficient cycle, mixer strips and the
  Nielsen embedding (004f); the gadget identities, the linear Boolean-to-A₅ reduction, the quotient
  lemma and the unfolding bound for Strahler rank (004g). Not formalized: the depth and NC
  statements, prime cores and the NC² construction, the scan/fusion/cold-sector compilers, ranked
  saturation and the surplus law, ancestrally liftable kernels, the transfer theorems, portal chains
  and the Strahler compiler's depth.
- **Family 005, portals** ([`lean/docs/005.md`](../../lean/docs/005.md)), covering Section 8:
  collision blocks, essential support, the 61-probe selector (with a $`|G|+1`$-probe analogue for
  every finite group), the realization theorem, part (i) of the star barrier and the charging
  lemma. Not formalized: the size count, support redundancy, parts (ii)–(iii) of the star barrier,
  the surplus transfer and all complexity statements.

## Notes on the merge

- **Removed as duplicates.** The seven introductions and preliminaries were merged into one
  introduction and one preliminaries section (the group, conventions, derived and lower central
  series, the program models, the parallel model). The Boolean gadget lemma of the pigeonhole
  preprint and the gadget theorem of the Barrington preprint are the same construction; they appear
  once (Lemma 3.2, Thm 3.3, Cor 3.4), and the hardness consequence of the pigeonhole lemma is
  Cor 3.6. The normal-form lemma of the pigeonhole preprint (size $`s+c_0`$) is subsumed by Thm 3.5
  (size $`s+64`$). The hypergraph preprint's restatements of ranked saturation, collapse mass and
  the 61-probe selector (with proof) were replaced by references to Sections 7.1–7.4. The seven
  "Computer checks" sections were merged into Appendix A; each preprint's status footnote was
  replaced by the consolidated thanks line. No automated-review material was present in the LaTeX
  sources.
- **Renamed for consistency.** $`F_2=F(X,Y)`$ of the nineteen-orbits preprint is now
  $`F=F(P,Q)`$, the free group of the invisible-to-solvable preprint; macros `\Af`, `\Ptime` were
  unified to `\A`, `\Pclass`; bibliography keys were unified (`BMPT1997`, `GHR1995`, `EKL2010`).
  The two different notions "ancestrally liftable kernel" (opening-cycles preprint, Def 9.7) and
  "ancestrally liftable cut" (hypergraph preprint, Def 8.10) keep their definitions; a sentence after
  Def 8.10 says they differ and which one Section 8.5 uses.
- **Genuine errors fixed.** (1) Remark 10.12(c) used an undefined symbol $`\rho`$ for the Strahler
  rank (and $`\rho`$ denotes class representatives in the same section); it now reads "after
  $`r+1`$ Newton steps, $`r`$ the Strahler rank". (2) Remark 5.11 said the combinations with ranked
  equality saturation are omitted "since they depend on notions not developed here"; ranked
  saturation is now developed in Section 7, so the sentence was corrected to give the actual reasons
  (the other notions are not developed here, the transfer is conditional). (3) The surplus-law
  Remark 7.21 and the transfer sentence in Section 8.5 spoke of a speedup "for
  polynomial-time computation" through the strict transfer; the transfer proved (Thm 3.7) is
  relative to multitape Turing-machine time, and both sentences now say so, consistently with
  Remark 3.8.
- **Cross-group citations.** Cited as consolidated papers, not inlined: group 3 (*Newton's Method,
  Horn Saturation and Strahler Rank*) for the general Horn-saturation statement of which Thm 7.12 is
  a special case, the GF(2) Newton iteration, and the Menger theorem inside one Strahler layer;
  group 6a (*Structural Parameters That Put Circuit Evaluation in NC*) for the ready-cycle return
  maps and root-domain classification, the six local Latin bijections, and the feedback-set bound on
  Strahler rank in Remark 10.12(b); group 7a (*Barriers to Speeding Up Circuit Evaluation*) for the
  junction-depth compiler in Remark 10.12(a); group 7b (*Circuit Evaluation by Flows and Linear Programs*) for
  output-conditioned instances in Section 9.1; group 6b (*NC Fragments of SC and Control-Trace
  Reductions*) for symbolic (exponential-state) portals, mentioned in the introduction of Section 8.
  Nothing was moved inline from other groups.
- **Status labels that matter.** Thm 7.18 and Cor 7.19 are conditional on an open hypothesis;
  alternative (iv) in Section 8.5 is a sketch; Conjecture 8.14 is a conjecture; Remark 5.11 reports
  measurements; Thm 3.7 and Prop 9.15 quote the logspace uniformity of the Pippenger–Fischer
  network; the claimed equivalences with $`\mathsf{P}\subseteq\mathsf{SP}`$ from the source notes
  are not established (Remarks 3.8, 9.16).
