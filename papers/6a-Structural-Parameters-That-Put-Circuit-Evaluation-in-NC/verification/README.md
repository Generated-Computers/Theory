# Computer checks

Plain Python 3 scripts, standard library only. Run each from this folder (`fanout_checks.py`
imports `a5lib.py`, and `rank_vs_fvs.py` reads `graphchecks.py` from the current directory):

```
cd verification
python3 <script>.py
```

The scripts were copied unchanged from the constituent preprints; there were no name clashes.
Results below are from a rerun on 24 November 2026 (Python 3.9). Section and theorem numbers refer
to `../paper.pdf`.

| Script | Source preprint | What it checks | Rerun result |
|---|---|---|---|
| `check_47_41.py` | Catalyst Height | Level structure of the catalyst-height compiler (Thm 4.6) and the factor-two rounding bound (Thm 4.12) on 500 random circuits each; $`\chi=\lceil h/2\rceil`$ for matched rails, $`h\le 8`$ (Sec. 4.5). Also contains checks for the companion manuscript on fractional covers (group 7a). | `catalyst compiler level checks: 500  rounding checks: 500`; rails verified for `h <= 8`. 3.6 s. |
| `a5checks.py` | Few Disjoint Cycles | $`A_5`$ root-domain classification (Thm 6.15) over all 3600 pairs; descriptor composition (Lemma 6.13); square-root counts in $`A_5`$; also commutator/gadget sanity checks. | Size distributions `[(0,2686),(3,400),(4,225),(5,288),(60,1)]` and `[(0,900),(1,2640),(16,60)]`, 0 violations; all other checks `True`/ok. 11.1 s. |
| `graphchecks.py` | Few Disjoint Cycles | Greedy feedback set of Thm 6.6 against brute-force cycle packings (400 random multigraphs, 3–11 vertices); escape switching and Strahler ranks on the stress family (Thm 6.10 (ii), (iii)); brute-force cycle packing of $`S_{4,6}`$ (Thm 6.10 (v)). | First three checks: `greedy FVS tests: 400 violations 0`, `escape switching rounds == layers: True`, `Strahler ranks equal layer index: True` (within seconds). The final brute-force cycle packing of the 56-vertex $`S_{4,6}`$ did **not** finish within 3 minutes and was not rerun to completion. |
| `rank_vs_fvs.py` | Few Disjoint Cycles | Inequality (6.1) $`\mathrm{sr}(C)\le (h+1)(\log_2((\kappa+1)s)+1)`$ on 3000 random circuits (Remark 6.9). | `instances 3000 violations ... 0 max ratio 0.24`. 3.9 s. |
| `fanout_checks.py` (+ `a5lib.py`) | Fanout Height | Fanout skeleton, formula regions, level evaluation, $`d\le h`$, merging of equal fanout nodes on 300 random $`A_5`$ programs (Thm 5.3); Hopf identities (Lemma 5.10); flattening rank 60 of $`\Delta_2`$ (Prop. 5.11). | All OK; flattening rank 60. 0.1 s. |
| `seqnor_check.py` | Fanout Height | Prop. 5.5 ($`H`$ = set of parents, $`d=h`$) on 2000 random Sequential NOR instances. | OK. 0.1 s. |
| `moving_frame_compact.py` | Constant Frontier | Moving-frame compiler (Thm 9.6) on random instances, cycle-plus-transposition words (Cor. 9.9), and the compact-frontier reachability criterion (Lemma 8.15, Thm 8.17). | `moving frame ok`, `cycle+transposition ok`, `compact frontier ok`. 0.4 s. |
| `table_iteration.py` | Nested Reads | Global table iteration (Thm 8.7) and the fixed-point lemma (Lemma 8.8) on 3000 random machines; ranks of lag programs. | `random machines ok: 3000`; $`A_N=\lfloor (N-1)/d\rfloor`$ on the listed lags. 0.2 s. |
| `copy_program.py` | Nested Reads | Prop. 8.10 on copy programs of lag 2–6. | `copy program ok`. 0.1 s. |
