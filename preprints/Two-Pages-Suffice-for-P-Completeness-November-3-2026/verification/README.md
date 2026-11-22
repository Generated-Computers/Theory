# Checking scripts for the two-page construction

Plain Python 3, no dependencies. Run from any directory:

```
python3 seqnor_two_pages.py [seed]   # default seed 2026; about 25 s
python3 monotone_check.py            # about 5 s
python3 gadget_search.py             # about 35 s
```

`seqnor_two_pages.py` implements the construction of the paper exactly: NOR circuit,
then slot program, then NOR/OR array built from the three gadgets, then Sequential NOR
instance (2-cell constant blocks, uniform 8-cell blocks in serpentine order, 4-cell
tail) with the two-page assignment. With the default seed it checks:

- the three gadget tables (SWAP, COPY, NOR) on all inputs, including that a gadget
  never reads a column outside its three columns;
- 300 random NOR circuits with 2 to 8 gates (instances up to n = 131,245): the slot
  program, the array, the Sequential NOR value at every block output and at the final
  position, the constraint 0 <= j_i < i, and the absence of same-page crossings with a
  sweep checker; the 26 instances with n < 3000 are also checked with the naive
  pairwise checker;
- 450 random arrays (width 1 to 7, depth 1 to 9, all six cell types): value at every
  block output and at the output position, and no same-page crossings, with both the
  sweep and the naive pairwise checker. As a control, putting all arcs on one page
  gives 73,558 crossings, so the checkers do detect crossings.

Output with the default seed: 0 mismatches and 0 same-page crossings everywhere.

`monotone_check.py` checks, on 3000 random small arrays with one NOR gate per cell,
that complementing the odd layers makes the output monotone in the layer-0 values
(0 violations). This is the observation that makes such arrays planar monotone circuits.

`gadget_search.py` is the breadth-first search that found the gadgets; it prints them
(its fourth column is never read and can be replaced by copy cells).

These checks support the proofs in the paper; the proofs do not depend on them.
