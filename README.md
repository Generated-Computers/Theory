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

## Papers

The 60 manuscripts are consolidated into nine self-contained papers and three short notes, organised by problem and thesis. Each folder in [`papers/`](papers/) has the PDF, a README with the abstract, the main results and their status, the manuscripts it consolidates, and the `verification/` scripts. The paper on random and smoothed instances extends family 001: its hardness reaches every noise level up to 0.4468, its algorithms work on every base above noise 0.7288, and it comes with Lean proofs of the deterministic lemmas of its embeddings.

| | Paper | Families |
| --- | --- | --- |
| 1 | [Sequential NOR on Random and Smoothed Instances](papers/1-Sequential-NOR-on-Random-and-Smoothed-Instances/paper.pdf) | 001 |
| 2 | [Strongly-Few Reachability, Mangroves and Logspace](papers/2-Strongly-Few-Reachability-Mangroves-and-Logspace/paper.pdf) | 012 |
| 3 | [Newton's Method, Horn Saturation and Strahler Rank](papers/3-Newtons-Method-Horn-Saturation-and-Strahler-Rank/paper.pdf) | 001, 002, 005, 006 |
| 4 | [A₅ Circuits Between NC² and P-Completeness](papers/4-A5-Circuits-Between-NC2-and-P-Completeness/paper.pdf) | 004, 005 |
| 5 | [Normal Forms and NC Compilers for Sequential NOR](papers/5-Normal-Forms-and-NC-Compilers-for-Sequential-NOR/paper.pdf) | 006, 007, 009, 010, 011 |
| 6a | [Structural Parameters That Put Circuit Evaluation in NC](papers/6a-Structural-Parameters-That-Put-Circuit-Evaluation-in-NC/paper.pdf) | 003, 004, 005, 007, 008, 010 |
| 6b | [NC Fragments of SC and Control-Trace Reductions](papers/6b-NC-Fragments-of-SC-and-Control-Trace-Reductions/paper.pdf) | 005, 006, 008, 010 |
| 7a | [Barriers to Speeding Up Circuit Evaluation](papers/7a-Barriers-to-Speeding-Up-Circuit-Evaluation/paper.pdf) | 003, 005, 007, 009, 010 |
| 7b | [Circuit Evaluation by Flows and Linear Programs](papers/7b-Circuit-Evaluation-by-Flows-and-Linear-Programs/paper.pdf) | 003 |
| N1 | [Stable Semisort Is Exactly as Hard as Padded Sorting (note)](papers/N1-Stable-Semisort-Is-Exactly-as-Hard-as-Padded-Sorting/paper.pdf) | 011 |
| N2 | [Stable Colors Do Not Certify Symmetry (note)](papers/N2-Stable-Colors-Do-Not-Certify-Symmetry/paper.pdf) | 004 |
| N3 | [Inner Product Has Affine-Cover Number 2ᵐ (note)](papers/N3-Inner-Product-Has-Affine-Cover-Number-2m/paper.pdf) | 008 |

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
On 24 November 2026 the 60 manuscripts were consolidated into nine papers and three short notes;
the paper on random and smoothed instances was replaced by a stronger version that extends the
hardness from noise 1/64 to every level below 4/9. On 28 November 2026 that paper was replaced by a newer version, with hardness up to 0.4468 and an algorithm for every base above 0.7288, after a section-by-section check.

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
