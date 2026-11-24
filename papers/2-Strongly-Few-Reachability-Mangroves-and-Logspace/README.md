# [Strongly-Few Reachability, Mangroves and Logspace](paper.pdf)

**Author:** Generated Computers

**Date:** November 24, 2026

## Citation

```bibtex
@misc{GC:paper-2,
  author = {{Generated Computers}},
  title = {{Strongly-Few Reachability, Mangroves and Logspace}},
  howpublished = {Generated Computers, 2026},
  year = {2026}
}
```

## Abstract

For a directed graph $`G`$ let $`N_G(u,v)`$ be the number of walks from $`u`$ to $`v`$, with
repeated vertices allowed, the empty walk counted and parallel edges distinct. Apers and
Edenhofer proved that the total language $`\mathrm{STCON}_{\mathrm{sf}}`$ of all
$`\langle G,s,t,1^k\rangle`$ with $`N_G(u,v)\le k`$ for all $`u,v`$ and $`N_G(s,t)\ge1`$ is in
$`\mathrm{BQL}`$, and asked whether it is in $`\mathrm{SC}^2`$ or in
$`\mathrm{DSPACE}(O(\log^2n/\log\log n))`$. We prove that it is in $`\mathrm{ReachUL}`$, with an
algorithm that rejects cyclic graphs and graphs with too many walks without any promise; known
containments then give $`\mathrm{UL}\cap\mathrm{coUL}`$, $`\mathrm{LOGDCFL}\subseteq\mathrm{SC}^2`$
and $`\mathrm{DSPACE}(O(\log^2M/\log\log M))`$ for input length $`M`$, which answers both parts of
the question. The proof rests on an elementary truncation lemma for walk budgets and on certified
finite-field lifts in the hashing-and-layering method of Garvin, Stolee, Tewari and
Vinodchandran; it extends to rooted, pair, selected-root and two-cone budgets of polynomial total
size. A direct capped depth-first search gives the $`\mathrm{LOGDCFL}`$ bound from the theorems of
Sudborough and Cook alone; Cheng and Wu obtained this containment independently. We also prove
matching hardness: with the threshold in binary the language is $`\mathrm{PL}`$-complete, already
on acyclic graphs; rooted $`k`$-fewness and the two-cone language with budgets $`k`$ and $`1`$ are
$`\mathrm{ReachUL}`$-complete for every fixed $`k`$, so a $`\mathrm{BQL}`$ recognizer of the
two-cone promise would give $`\mathrm{ReachUL}\subseteq\mathrm{BQL}`$; and
$`\mathrm{STCON}_{\mathrm{sf}}`$ is $`\mathrm{StrongFewL}`$-hard.

In deterministic logspace, $`\mathrm{STCON}_{\mathrm{sf}}`$ is decidable in space
$`O(b+\log M)`$, where $`b`$ is the largest cyclomatic number of a block of the underlying
undirected graph, in space $`O(k\lambda+\log M)`$, where $`\lambda`$ is the smaller of the numbers
of sources and sinks, and in space $`O((\gamma+1)\log M)`$, where $`\gamma`$ is the largest cycle
rank of a weak component. For mangroves ($`k=1`$) we show that reachability, path mass, parents in
the hidden out-tree, ranking, unranking and cone listing are pairwise equivalent under
promise-respecting logspace reductions, and that the total language is in $`\mathrm{L}`$ if and
only if the promise problem is; for unary $`k`$, walk counting, path mass, bounded-fill
elimination and no-growth matrix powering are each in logspace under the promise if and only if
$`\mathrm{STCON}_{\mathrm{sf}}\in\mathrm{L}`$. Finally, the path-count matrix of a simple
$`k`$-strongly-unambiguous graph is a product of at most $`2\lfloor\log_2k\rfloor+1`$ path-count
matrices of mangroves, through a level partition into $`\lfloor\log_2k\rfloor+1`$ path-convex
mangroves that is optimal for every $`k`$; we also prove $`c+1\le r\le2^c`$ for two-terminal DAGs
with $`r`$ paths and cyclomatic number $`c`$, with equality $`r=2^c`$ exactly for chains of bridges
and cycles, and a finite forbidden-subdivision characterization of $`k`$-strong unambiguity. All
results are proved in full from the imported theorems stated in the paper; nothing places mangrove
reachability in $`\mathrm{L}`$. A few counts (of obstructions, extremal densities and least factor
numbers) were obtained by computer and are labelled as such.

## Main results

All statements below are **proved in full**, from the imported theorems listed in Section 2.3
(Sudborough, Cook, Lange, the three-outcome normal form for ReachUL used by Garvin–Stolee–Tewari–
Vinodchandran after Buntrock–Jenner–Lange–Rossmanith, Allender–Lange, Immerman–Szelepcsényi,
Allender–Ogihara, Apers–Edenhofer, Allender–Reinhardt–Zhou, Reingold, Elberfeld–Jakoby–Tantau).
The walk convention (empty walk counted, parallel edges distinct) is fixed in Definition 2.1;
promise problems are kept as promise problems (Section 2.4).

- **Theorem 1.1 (= Corollary 5.11 and the proof in Section 5).** $`\mathrm{STCON}_{\mathrm{sf}}\in\mathrm{ReachUL}`$, hence in
  $`\mathrm{UL}\cap\mathrm{coUL}`$, in $`\mathrm{LOGDCFL}\subseteq\mathrm{SC}^2`$ and in
  $`\mathrm{DSPACE}(O(\log^2M/\log\log M))`$. Extensions: RootBudget (Theorem 5.8), PairBudget,
  SelBudget, FBFew (Corollary 5.11), fail-closed compiler for logspace machines (Corollary 6.1).
  Proved in full.
- **Theorem 1.2 (= Theorem 3.12).** Direct DAuxPDA in $`O(M^4)`$ steps; $`\mathrm{LOGDCFL}`$ bounds
  for walk budgets (Theorems 4.1, 4.4, Corollary 4.6). Proved in full. Obtained independently by
  Cheng and Wu (arXiv:2609.23603, Appendix D).
- **Theorem 2.25 (truncation principle).** Budgets hold for all walks iff they hold for walks of
  length at most the total budget. Proved in full.
- **Theorem 1.4 (= Theorem 9.1).** BIN-STCON_sf is PL-complete, hard on acyclic instances with
  $`s\leadsto t`$; one-pair caps are NL-/PL-complete (Theorem 9.4). Proved in full.
- **Theorem 1.5 (= Theorems 7.3, 7.6, Lemma 7.4) and Corollary 1.6 (= Corollary 7.7).** Rooted and
  two-cone ReachUL-completeness; a BQL recognizer of the two-cone promise would give
  ReachUL ⊆ BQL. Proved in full.
- **Theorem 1.7 (= Theorem 8.1).** STCON_sf is StrongFewL-hard. Proved in full.
- **Propositions 10.1–10.3, Theorems 11.1, 11.3, 11.5, Corollary 11.6.** One GapL zero test;
  collision-averaged decoding and capped counts in FL^NL, also for arbitrary #L functions. Proved
  in full (certificates for known containments; the capped #L form is new to us).
- **Theorems 1.8–1.10 (= Theorems 15.3, 12.4, 13.6, Corollary 13.7).** STCON_sf in space
  $`O(\mathrm{bcw}+\log M)`$, $`O(k\lambda+\log M)`$, $`O((\gamma+1)\log M)`$; logspace for logarithmic
  parameters. Proved in full. Robustification barrier (Theorem 17.1), functional versions
  (Corollary 16.4).
- **Theorem 1.15 (= Theorems 20.3, 20.4, 21.2, Proposition 21.5).** Level partition into
  $`\lfloor\log_2k\rfloor+1`$ path-convex mangroves (optimal), factorization into
  $`2\lfloor\log_2k\rfloor+1`$ mangrove factors, lower bound for the transitive tournament. Proved
  in full. Further structure: Theorems 19.2, 22.1, 22.2, 23.3, 23.8, 24.1, 25.4, 25.6, 26.1,
  Proposition 26.2, Section 27. Computer data, labelled as such: Remark 21.6 (least factor
  numbers), Remark 25.7 ($`|\mathcal F_1|=1,|\mathcal F_2|=7,|\mathcal F_3|=53`$), Table 3 (exact
  extremal densities).
- **Theorems 1.11–1.14 (= Theorems 30.2, 31.1, 33.6, 34.3, 34.8, Corollaries 28.4, 31.4).** The
  six-way mangrove equivalence, the strongly-few one-query equivalences, the unique annotation and
  the promise-to-total transfers, and single-power totalization with tight exponent. Proved in
  full; these are equivalences, no new algorithm. Theorem 35.2 (rooted frontier) is an immediate
  consequence of Lange's theorem.

## Consolidated from

| preprint | sections of this paper |
|---|---|
| [Strongly-Few Reachability Is in ReachUL](../../preprints/Strongly-Few-Reachability-Is-in-ReachUL-November-21-2026/paper.pdf) (012a) | 1.1, 2.1–2.3, 2.5 (truncation), 3, 4, 5, 6, 36.1, Appendix A, Appendix B |
| [Strongly-Few Reachability with Binary Thresholds Is PL-Complete](../../preprints/Strongly-Few-Reachability-with-Binary-Thresholds-Is-PL-Complete-November-21-2026/paper.pdf) (012b) | 1.2, 2.1–2.3, 7, 8, 9, 10, 11, 36, Appendix B |
| [Strongly-Few Path Matrices Factor into Logarithmically Many Mangroves](../../preprints/Strongly-Few-Path-Matrices-Factor-into-Logarithmically-Many-Mangroves-November-21-2026/paper.pdf) (012c) | 1.4, 2.1 (concatenation lemma), 2.5 (stabilization, all-pairs test), 18.1, 19–27, 36, Appendix B |
| [Total Strongly-Few Reachability Is in Logspace for Logarithmic Block-Cyclomatic Width](../../preprints/Total-Strongly-Few-Reachability-Is-in-Logspace-for-Logarithmic-Block-Cyclomatic-Width-November-21-2026/paper.pdf) (012d) | 1.3, 2.3 (undirected tools), 2.4 (composition lemma), 2.5 (caps), 12–17, Appendix B |
| [Mangrove Reachability Is Logspace-Equivalent to Path Mass](../../preprints/Mangrove-Reachability-Is-Logspace-Equivalent-to-Path-Mass-November-21-2026/paper.pdf) (012e) | 1.4, 2.1, 2.4 (promise problems and reductions), 18.2, 28–35, 36, Appendix B |

The main theorem of 012a was also announced in arXiv:2610.09139 (October 2026).

## Lean

Family 012 (strongly-few reachability) is not formalized in Lean; none of the five constituent
preprints has a Lean formalization, and no other family is involved.

## Notes on the merge

**Removed as duplication.** The five introductions were replaced by one (Section 1), which keeps
012a's account of the Apers–Edenhofer question, the quantum-candidate remark, 012b's
classification table, 012d's relation to the logspace Courcelle theorem and 012e's background on
Allender's question. One preliminaries section (Section 2) replaces five: the walk convention
(stated five times) is Definition 2.1; the four walk-basics lemmas (012a Lemma 2.2, 012b Lemma
2.1, 012d Lemma 2.2, 012e Lemma 2.1) are merged into Lemma 2.2 with parts (a)–(e); fewness,
mangroves, encodings and all languages are defined once; Lange's theorem (012a, 012e) is stated
once (Theorem 2.9). The budget-mass truncation lemma, proved in 012a (Theorem 4.1), reproved in
012b (Lemma 2.8) and in 012c as "budgeted stabilization" (Theorem 3.3, Corollary 3.4), is stated
once as Theorem 2.25, with 012c's recurrence form as Remark 2.26 and its all-pairs test as
Corollary 2.29. 012e's Theorem 10.1 (cumulative powers, now Theorem 34.1) is noted to be
Corollary 2.29 in matrix form; its short direct proof is kept. The "facts from companion
manuscripts" (012b Fact 2.7 and its ReachUL facts Fact 2.3, 012d Remark 2.3 (F1)–(F3), and the
background paragraphs of 012e) are replaced by internal references (Theorem 5.8, Corollaries 2.11,
5.2, 5.11). In Section 11 (012b's capped counts) the fingerprint and the layered lift now refer to
Definition 5.4 and Lemma 5.5 instead of being redefined. The five open-problem sections are merged
(Section 36): 012a's questions (1) and (2) coincide with 012b's Problems 8.1 and 8.3, and 012a's
question (4) is merged with 012e's Problem 12.5. The five computer-check appendices are merged into
Appendix B.

**Removed as review/changelog material.** The "Status" paragraphs of the five title-page notes and
012d's Remark 8.6 ("smaller changes from the source note": admissibility now states
$`w\notin S\cup\{v\}`$ and the case $`v=t`$; the path test follows arcs instead of a connectivity
test; loops and antiparallel pairs are rejected before the block algorithm; the live-corridor
extractor is derived from the count oracle; the robustification proof was checked case by case;
Propositions 17.3–17.4 are labelled standard). References to item numbers of the unpublished
internal note (Caution A9.5, A12.4, Problems A9.6, A35.6–A35.8) were dropped; the mathematical
remarks comparing with that note are kept, worded as "the earlier internal note". There were no
automated-referee sections in these preprints.

**Genuine fixes made while merging.**
- *Definition mismatch for ReachUL.* 012e defined ReachUL and StUL with machines that have a
  unique accepting configuration (as in Buntrock et al.) and uses that configuration in the proof
  of Theorem 35.2, while 012a's definition (used everywhere else) has no such requirement. Section
  2.3 now adds one sentence showing the two agree: by the three-outcome normal form (Theorem 2.10)
  at most one accepting configuration is reachable, so a new configuration entered from all
  accepting ones keeps reach-unambiguity.
- *Notation clash.* 012a's universal-source lift was written $`U(G)`$, which in 012d denotes the
  underlying undirected multigraph; the lift is now $`\mathcal U(G)`$, $`\mathcal U_R(G)`$
  throughout (Construction 4.2, Lemma 4.3, Theorem 4.4, Corollaries 4.6 and 5.11, Table 4).
- *Missing definition after the merge.* 012b's prefix gadget (its Lemma 2.9, used in Sections 7 and
  9) is placed at the start of Section 7 (Lemma 7.1); 012d's block lemma, $`\gamma`$ and
  $`\mathrm{bcw}`$ moved to Section 2.3. Label and macro clashes between the preprints (e.g.
  "Theorem capped" and "Section rooted" in both 012a/012b and 012b/012e; two different "lem:block";
  \RootBudget defined twice) were resolved by renaming.
- No mathematical error in a statement or proof was found during the merge; the mathematics is
  unchanged.

**Results moved inline from other groups / cross-group citations.** None: no constituent cites a
Generated Computers preprint outside family 012. The omitted kernel-size bounds of 012d's
live-corridor extractor (which rested on a corollary now in Section 25) remain omitted, since no
constituent proved them.

**Status labels that matter.** Lemma 2.23 has a proof sketch (standard closure of logspace oracle
transducers), as in 012e. Remarks 21.6 and 25.7 and Table 3 are computer results, labelled "by
computer". Propositions 17.3 and 17.4 are labelled standard. The containments in Sections 10 and 11
are presented as certificates for known containments, not as new containments. Theorem 1.2 (the
capped depth-first search, $`\mathrm{STCON}_{\mathrm{sf}}\in\mathrm{LOGDCFL}\subseteq\mathrm{SC}^2`$)
was obtained independently by Cheng and Wu (arXiv:2609.23603, Appendix D); Theorem 1.1 and the
certified-lift proof are ours.

**Verification.** All constituent scripts are in [`verification/`](verification/README.md), in five
subfolders; every script finishing within about three minutes was rerun (all passed); two long runs
(`check_obstructions.py`, about 10 min, and `check_density.py 8 6`, about 7 min) were not rerun and
their recorded outputs are included.
