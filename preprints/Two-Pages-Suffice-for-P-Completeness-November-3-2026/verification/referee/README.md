# Independent check of the two-page theorem

These scripts were written on 3 November 2026 by an independent automated referee, from the
paper's TeX source only, without reusing the paper's own checker in `verification/`.

- `ref_check.py`: builds the reduction CVP → NOR circuit → slot program → array → Sequential NOR
  instance, evaluates Sequential NOR directly, compares every block output with the array value,
  and checks crossings on each page.
- `run_all.py` (output `run_all.out`): runs the checks on all NOR circuits with at most 4 gates,
  on adversarial families (chains, wide, high fan-out, far references, alternating) and on random
  circuits and arrays.
- `brute_circuits.py` with `brute.c`: brute-force test of every same-page pair of arcs (compile
  with `cc -O2 brute.c -o brute`).
- `mutants_and_sec3.py`, `control.py`: controls showing that broken variants of the construction
  are caught, and the checks of Section 3.

Results: no value mismatch, no same-page crossing, and a bipartite crossing graph on every
instance; every mutated construction was caught.

Usage: each script takes this folder as its first argument, for example
`cc -O2 brute.c -o brute && python3 run_all.py .` (from inside `verification/referee/`).
