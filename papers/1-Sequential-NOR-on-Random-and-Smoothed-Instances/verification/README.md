# Verification

Programs behind the computations of the paper. Appendix A of the paper says what each one does
and how to run it.

- [`scripts/`](scripts/): the programs that the proofs and remarks cite. Programs that are part of
  a proof work in exact rational or interval arithmetic; the others are simulations.
- [`independent-checks/`](independent-checks/): programs written independently of `scripts/`,
  from the definitions in the paper, to re-check sections of it. Appendix A says which section
  each folder checks.
- [`exploration/`](exploration/): records of searches that are not part of any proof, with their
  negative results.

Comments inside the programs may refer to theorems by the global numbers of the source version
of the paper (for example "Theorem 160"); the paper now numbers its statements by section.
