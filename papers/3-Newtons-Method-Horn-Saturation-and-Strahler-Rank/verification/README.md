# Verification scripts

Scripts for *Newton's Method, Horn Saturation and Strahler Rank*. They check finite or arithmetic
claims and reproduce experiments; none of them replaces a proof. Theorem and section numbers refer
to `../paper.pdf`.

Two of the five constituent manuscripts shipped scripts:

- `random-seqnor/` is the script folder of *A P-Complete Problem in Average-Case NC*, copied
  unchanged. That folder is shared with the smoothed-analysis manuscripts, so it also contains
  scripts for the Kleene–prefix iteration and smoothed instances. Those results are in the group-1
  paper *Sequential NOR on Random and Smoothed Instances*, not in this paper; their scripts are kept
  for completeness and were not rerun here.
- `menger/` holds the scripts of *Menger's Theorem Inside One Strahler Layer* (`a5_checks.py`,
  `a5lib.py`, `horn_checks.py`), copied unchanged.

The other three manuscripts (*The First-Collision Law of Newton's Method over GF(2)*, *Newton's
Method Evaluates Circuits in Strahler-Rank Rounds*, *Horn Saturation in Strahler-Rank Reachability
Rounds*) report computer checks (Appendix B, items 2–4) whose scripts were never part of the
repository.

No paths had to be changed: the scripts refer only to files inside their own folder. Comments of the
form "NOTE.md §…" and "paper Section …" point to the working notes and section numbers of the
original manuscripts, not to this paper.

All Python scripts are plain Python 3 with the standard library. Run them with `python3 -I`; the
C programs build with `cc -O2 file.c -o name -lm`. Scripts that import `core.py` take the folder that
contains it as their first argument.

## This paper: Newton's method on Sequential NOR (`random-seqnor/`)

| Script | What it checks | Paper | Command | Rerun on 24 Nov 2026 |
|---|---|---|---|---|
| `check_constants.py` | Exact log-space evaluation of the window-lemma recursion at 11,202 values of ln f in [200, 1e20]: (P2), depth bounds of (P3), Phase 1 c ≤ 1, proviso X ≤ β, ln c₁/ln f ≤ 3/128, R₀ bound, failure budget ≤ 0.26 | §5.5, App. B(1) | `python3 -I check_constants.py` | yes, 1 s: "all assertions passed"; worst η = 0.0046, worst total budget 0.25625, worst ln X = −93.9, worst Phase-1 ln c = −16.1 |
| `worstcase.c` | Exhaustive maximum of Newton rounds from the standard start over all n! parent arrays | Prop. 4.11, Table 5 | `./worstcase 13` | yes for N = 12 (21 s): maxima 0,1,1,1,2,2,3,3,4,4,5,5 for n = 1..12, equal to ⌊(n−1)/2⌋ for n ≥ 3 and 1 at n = 2; maximisers for odd n ≥ 7 are W_n. N = 13 (about 6.2·10⁹ arrays, several minutes) not rerun |
| `wn_check.py` | The family W_n: E₁ = {5,6}, f_t = 2t+3, T_n = ⌊(n−1)/2⌋ for 6 ≤ n ≤ 400 | Prop. 4.11(b) | `python3 -I wn_check.py` | yes, 5 s: "failures: 0" |
| `exp_rank.py` | Level process equals the Strahler recursion; level survival product formula; ρ(n)/√n | Thm. 5.1, App. A | `python3 -I exp_rank.py .` | yes, 8 s: level process matches on 300 instances; survival 0.2190 (empirical) vs 0.2193 (formula); ρ/√n = 1.539, 1.582, 1.587 at n = 10⁴, 10⁵, 10⁶ (limit 1.5958) |
| `structure_checks.py` | Trace = lexicographically first MIS; binary-core deficit; live width at n/2; density of ones | Prop. 5.14, Thm. 5.15, Cor. 5.17, Table 4 | `python3 -I structure_checks.py` | yes, 1 s: MIS identity on 2000 instances; table rows 20.8/19.5/0.2519/0.38207, 26.0/26.4/0.2496/0.38244, 34.2/33.3/0.2500/0.38222 (as in Table 4) |
| `phi_check.py` | Reset-set iteration Φ on j_i = max(0, i−2): ⌈n/3⌉ changing rounds for n ≤ 300 | §9, item 4 | `python3 -I phi_check.py` | yes, 1 s: no mismatches; random n = 256, 1024, 4096: 9.5, 13.7, 20.1 changing rounds |
| `core.py` | Reference Python implementation (trace, Newton step, trajectories, Strahler rank) | — | library | — |
| `newton.c` | Newton fronts and window statistics on random instances (Table 2) | App. A | `./newton n seed` | yes at n = 2²⁰, seeds 1–4: 18, 17, 18, 18 rounds (Table 2 mean 17.5); density of ones 0.3818–0.3822 |
| `xcheck.py` | C implementation `newton` against the Python reference: identical fronts | App. A | `python3 -I xcheck.py DIR` (DIR holds `core.py` and the compiled `newton`) | yes, 1 s: MATCH for seeds 11, 12, 13 (n = 3000) |
| `newton2.c` | Adds pre-front mass m₀ and previous-round window mass W per round | App. A ("Other checks") | `./newton2 n seed` | not rerun |
| `newton3.c` | Depth hierarchy p_ℓ, w_ℓ (Table 3) and pathwise check of the witness inequality | Lemma 5.7(i), Table 3 | `./newton3 n seed` | yes at n = 2¹⁶, seed 7: 15 rounds, 983,040 witness checks, 0 violations. The 2²² runs of Table 3 were not rerun |
| `exp6.py` | Newton from the standard and a random start, and naive peeling, at n = 2¹⁰…2¹⁶ | App. A ("Other checks") | `python3 -I exp6.py .` | yes, 5 s: standard 9, 10.7, 11.7, 13.5; random start 8, 10.2, 12, 13; peeling 47.5, 60.3, 84.5, 101.5 |
| `exp3.py` | Front ratios and window masses per round | App. A | `python3 -I exp3.py . n seed instances` | not rerun |
| `summ.py`, `summ2.py`, `summ3.py`, `summ4.py` | Summaries of `newton`, `newton2`, `newton3` run directories (`runs/`, `runs2/`, `runs3/`, not shipped) into the numbers of App. A | App. A | `python3 -I summK.py DIR` | not rerun (the run directories are not in the repository) |

## Group-1 material in `random-seqnor/` (not rerun)

`smooth.c`, `smooth_check.py`, `smooth_flags.py`, `runall.sh`, `smooth_runall.out`, `fronts.py`,
`gadget_search.py`, `kp_check.py`, `kp_constants.py`, `kp_density.py`, `kp_greedy.c`, `kp_probe.c`,
`kp_runall.sh`/`.out`, `kpr_check.py`, `kpr_witness.py`, `kpr_meanfield.py`, `kpr_relax.c`/`.sh`/`.out`,
`kpr_edge.sh`/`.out`, `kpr_last.sh`/`.out`, `kpr_runall.sh`/`.out`, `nogo_check.py`,
`nogo_block.sh`/`.out`, `blockbase.c` and the folder `evolve/` (with `results/`) concern smoothed
instances, the Kleene–prefix iteration and its relevance-pruned variant, and an algorithm search.
Their header comments state what each one checks. They belong to *Sequential NOR on Random and Smoothed Instances* and are not used in this paper.

## One Strahler layer (`menger/`)

| Script | What it checks | Paper | Command | Rerun on 24 Nov 2026 |
|---|---|---|---|---|
| `horn_checks.py` | Rank-layer reachability lemma and the monotone layer operator on 400 random Horn systems; max-flow vs brute-force minimum vertex cut on 109 layers | Lemma 7.2, Thm. 7.4, App. B(5) | `python3 -I horn_checks.py` | yes, < 1 s: "OK on 400 systems", "109 instances OK" |
| `a5_checks.py` | Side-premise star in A₅ for t = 3 (C-pattern equals B-pattern, all 8 patterns), plus checks for the group-4 hypergraph and portal results | Prop. 7.7, App. B(5) | `python3 -I a5_checks.py` | yes, 22 s: all checks OK; "patterns realised: 8 of 8" |
| `a5lib.py` | Helper library for A₅ (even permutations of {0,…,4}) | — | library | — |
