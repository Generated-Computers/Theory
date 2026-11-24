# Computer checks for "Normal Forms and NC Compilers for Sequential NOR"

Plain Python 3, standard library only (one optional C helper in `two_pages_independent/`).
Run every script from this folder, for example `python3 census_query_checks.py`. The checks guard
against indexing errors; no proof in the paper depends on them. Appendix A of the paper describes
them. All scripts below were rerun on 24 November 2026 for this consolidation, except where noted;
times are wall-clock on a laptop.

| Script | Source preprint | What it checks | Command | Result (24 Nov 2026) |
|---|---|---|---|---|
| `seqnor_two_pages.py` | Two Pages Suffice for P-Completeness | The two-page construction of Section 4.3: the three gadget tables on all inputs; 300 random NOR circuits with 2–8 gates (instances up to n = 131,245): slot program, array, value at every block output, $`0\le j_i<i`$, no same-page crossings (sweep checker, plus naive checker for the 26 instances with n < 3000); 450 random arrays with all six cell types; one-page control | `python3 seqnor_two_pages.py [seed]` | gadgets verified; 0 mismatches, 0 crossings; control 73,558 crossings (25 s) |
| `monotone_check.py` | Two Pages | Monotonicity after complementing odd layers for NOR-only arrays (Proposition 4.6), 3000 random arrays | `python3 monotone_check.py` | 0 violations (1 s) |
| `gadget_search.py` | Two Pages | Breadth-first search that finds the COPY, NOR and SWAP gadgets of Table 1 | `python3 gadget_search.py` | prints the three gadgets (33 s) |
| `two_pages_independent/run_all.py` (uses `ref_check.py`) | Two Pages | A second implementation of the two-page construction written from the paper's text: all NOR circuits with ≤ 4 gates, adversarial families up to n = 391,097, random circuits and arrays, exhaustive small arrays; values, same-page crossings, bipartiteness | `cd two_pages_independent && python3 run_all.py .` | no failures, 0 same-page crossings; output as in `run_all.out` (87 s, run on a copy) |
| `two_pages_independent/brute_circuits.py` + `brute.c`, `mutants_and_sec3.py`, `control.py` | Two Pages | Brute-force pairwise crossing test on all circuits with ≤ 4 gates (about 3.2·10^11 arc pairs); mutated constructions are caught; checks of Section 3.2 | `cc -O2 brute.c -o brute && python3 brute_circuits.py .` etc. | **not rerun** (the brute-force run is long); originally reported: no crossing, all mutants caught |
| `census_query_checks.py` | Sequential NOR Has Exactly Fibonacci-Many Traces | Census $`F_{N+1}`$, fibre formula and $`K_{N,q}`$ for N ≤ 8 by enumerating all N! arrays; spectrum sandwich (Theorem 6.13) | `python3 census_query_checks.py` | all agree; prints the table of Section 6.5 (< 1 s) |
| `check_core.py` | Sequential NOR Is Circuit Evaluation on Its Binary Core; Blockwise Guessing (identical script in both) | Descriptors against the trace, triangularity, block recovery on the core (Theorem 12.13) and residual block recovery (Theorem 12.5) for g ∈ {1, 2, 3, ⌈log₂(n+1)⌉, n} with exactly one valid branch per stage; embedding of Theorem 7.7 on 3000 random circuits | `python3 check_core.py [NMAX]` (default NMAX = 7) | NMAX = 7: 5,913 arrays (3 s); NMAX = 8: 46,233 arrays (46 s); 3000 circuits; all pass. `check_core.out` is the original output for NMAX = 8 |
| `check_006g.py` | Few Long Paths Put Sequential NOR in QuasiNC | Imports `check_core.py` (rerunning its checks for n ≤ 7); the path family (Lemma 16.8, Theorem 16.9, Remark 16.10) for L ≤ 7; arcs and lower bound of Proposition 16.11 for L ≤ 8 | `python3 check_006g.py` | passed (3 s). The source folder lacked `check_core.py`; it is present here |
| `check_seqnor.py` | Exact Cut Contraction for P-Complete Sequential Circuits | Greedy-MIS identity and jump rule for n ≤ 8 (46,233 arrays); cut externalization with reconstruction on 46,391 circuit–cut pairs; crossing-area identity; numbers of the padding counterexample | `python3 check_seqnor.py` | all OK (1 s) |
| `check_lac.py` | Exact Cut Contraction | LAC → indexed recurrence (2000 trials); trace-resolved RSM → LAC over Z (500 programs); nilpotent-inverse identity; elimination rounds (1000 trials) | `python3 check_lac.py` | all OK (< 1 s) |
| `wavefront.py` | NOR Shift Registers Are Tiling Rotations | For D ≤ 14: two-sweep landing, rotation, extension bit, preperiod ≤ 2 and period dividing D+1, collapse of the six non-affine rules | `python3 wavefront.py` | all True (4 s) |
| `lag_sequence.py` | NOR Shift Registers | Periodicity $`x_{i+D+1}=x_i`$ for 2D ≤ i ≤ 5D, D ≤ 12; unique NOR polarity of the eight non-affine gates | `python3 lag_sequence.py` | ok (< 1 s) |
| `homogeneous_template_checks.py` | Homogeneous Sequential NOR Grids Lie in NC1 | Lemmas 17.9–17.12 exhaustively for H ≤ 5, W ≤ 6; transfer classification for H ≤ 6; closure of the 80-map set for H ≤ 8 | `python3 homogeneous_template_checks.py` | 0 violations; size 80 and closed for H = 3..8 (4 s) |
| `fibonacci_row_checks.py` | Three NC Compilers for Sequential NOR Grids | $`T^3=T`$, stability criterion and count, rank recurrence and minimum, injective rows, atom factorization for W ≤ 10; constant image of the two-row block for W ≤ 12 | `python3 fibonacci_row_checks.py` | all pass (1 s) |
| `gamma_index_checks.py` | Three NC Compilers | INDEX gadget for m ≤ 5; Γ of alternating rows; Γ ≤ min(H, W+1) | `python3 gamma_index_checks.py` | ok (< 1 s) |

The Reset Normal Form, Parameterized NC Compilers and Runwise Portfolio manuscripts had no
verification scripts; the checks they report (exhaustive checks of the reset normal forms for
n ≤ 8, random regression checks of phase repair and the interval rules) are described in Appendix A
of the paper but cannot be rerun from this folder.
