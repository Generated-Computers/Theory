<p align="center"><img src="assets/header.png" alt="P = NC?" width="100%"></p>

# Readme

This repository contains mathematical manuscripts and supporting proof artifacts produced by
Generated Computers on the parallel complexity of circuit evaluation. Most of them concern
Sequential NOR, the P-complete recurrence $`x_0 = 1`$, $`x_i = \mathrm{NOR}(x_{i-1}, x_{j_i})`$
with $`0 \le j_i < i`$. Family 012 concerns the space complexity of directed reachability in graphs
with few walks.

The manuscripts were written together with an AI system and are shared as working research:
new results, released early so that others can read them, check them and build on them. Each
manuscript's README says what is proved in full, what is sketched, conditional or numerical,
and what was corrected relative to the notes it was rewritten from.

Everything here is aimed at the question on the banner: can everything computable in
polynomial time also be computed in polylogarithmic parallel time? The question is still open,
and the manuscripts work on it from both sides. Some put large families of instances of
P-complete problems into NC or quasiNC: random inputs, low-defect instances, instances with few
long paths, constant-frontier computations. Others pin down exactly what a fast parallel
algorithm would have to do, or show why natural approaches fail. The neighbouring questions come
up too: P versus BPNC, quasiNC and SC, and whether P admits polynomial parallel speedups (SP, EP).

## Navigating the collection

The current catalogue contains 60 manuscripts organized into 12 result families. A family
groups related papers: a principal result, companion arguments, consequences or barriers.

- Start with the [overview](overview.pdf) for descriptions of the families.
- The [`preprints/`](preprints/) directory contains, for each manuscript, the PDF and a README
  with the citation and the status of its results; 44 of them also have the `verification/`
  scripts used for computer checks.
- The [Lean library](lean/README.md) and the [formalization catalogue](lean/formalization.yaml)
  describe the formal proofs, their associated papers, and the Comparator configurations. Every
  manuscript of families 001–011 has at least one formalized main result: 472 theorems in all, proved without `sorry`
  and with only the standard axioms. The formalizations cover the mathematical content of the
  papers (correctness of constructions and reductions, invariants, exact counts, identities);
  complexity classes, logspace computability, depth bounds and probability bounds are not
  formalized. Each family's scope page in [`lean/docs/`](lean/docs/) says what is and is not.
  The five manuscripts of family 012 are not formalized yet.

## How the results were produced

The manuscripts were rewritten from two sources: 48 internal research notes written from
17 August to 7 September 2026 (2,637 pages), and the work on random and smoothed Sequential
NOR done from 27 October to 3 November 2026. On 27 October 2026 the notes were reviewed and
95 results were scored for correctness and value. On 3 November 2026 every result that
survived the review was rewritten as a standalone paper. On 21 November 2026 a 72-page note of
9 September 2026 on strongly-few reachability was rewritten as the five manuscripts of family 012.

- **Proofs were checked against the sources.** Gaps were filled where possible; otherwise the
  proof is labelled a sketch.
- **Finite claims were checked by computer.** The scripts are in each manuscript's
  `verification/` folder.
- **Errors in the sources were corrected or the results dropped.** Each manuscript's README
  lists these.
- **Prior work is attributed.** Where the notes had missed known results, the rewrite credits
  them.

## Versions and citations

Corrections and revisions will be recorded as new versions, with previously released versions
remaining accessible.

To cite an individual manuscript, use the BibTeX block in its directory.
