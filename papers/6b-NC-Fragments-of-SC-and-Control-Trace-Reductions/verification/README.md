# Verification scripts

Computer checks for *NC Fragments of SC and Control-Trace Reductions* (Appendix A of `paper.pdf`).
All scripts are plain Python 3 with no dependencies outside the standard library, use fixed random
seeds, and are run from this folder with `python3 <script>.py`. No proof in the paper depends on them.

| Script | Source preprint | What it checks | Run time / last output (24 Nov 2026) |
|---|---|---|---|
| `lr_check.py` | An SCᵏ-Complete Problem with an NC³ Fragment | Transcript leaves (Lemma 4.9), pair merge (Lemma 5.1) and syndrome recompression (Theorem 5.3) along the canonical tree, against direct simulation on 150 random instances (≤ 5 data bits, ≤ 14 stages) | 0.2 s; `checked 3418 (u,x) pairs; violations 0 ; max merge rank seen 5` |
| `kernel_checks.py` | Control Observability Erases Payload in Trace Generation | Ladder identities of Theorem 10.2 for 1 ≤ r ≤ 11, 2 ≤ w ≤ 8; payload erasure (Theorem 10.8) on 400 random affine history machines over GF(101) with 2 ≤ d ≤ 4 (the first run of Appendix A), with a negative control | 0.2 s; `ladders ... OK`, `identical address/branch/control traces in 400 random tests`, `negative control ...: 398 cases` |
| `a5_checks.py` | Exponential-State Portals with Constant-Depth Transfer | Full-capacity portal and hard-coefficient switch for t = 2 (Theorem 11.3, Proposition 11.4); also checks for other preprints of the collection (hypergraph realization, star barrier, side-premise star) that are not used in this paper | 22 s; all lines `OK`, `full-capacity portal / hard-coefficient switch (t=2): OK` |
| `fanout_checks.py` (imports `a5lib.py`) | Exponential-State Portals with Constant-Depth Transfer | Formula-forest property (Lemma 11.14), evaluation in topological order of fanout nodes (Theorem 11.15), merging of equal fanout nodes (≤ 60 classes) on 300 random A5 programs; also fanout-skeleton levels and Hopf identities used by other papers | 0.1 s; `fanout height: level evaluation correct, d<=h, merged d<=c<=60 on 300 random SLPs; ...`, `Hopf identities ...: OK`, `flattening rank of copy tensor Delta_2: 60` |
| `horn_checks.py` | Exponential-State Portals with Constant-Depth Transfer | Rank-layer reachability (Lemma 11.1) and the monotone layer operator (Theorem 11.9) against minimum ranks on 400 random Horn systems; also a vertex-Menger check used by another paper | 0.1 s; `rank-layer reachability lemma and monotone layer operator: OK on 400 systems`, `vertex Menger ...: 109 instances OK` |
| `a5lib.py` | Exponential-State Portals with Constant-Depth Transfer | Helper module (A5 as even permutations of {0,...,4}); not run on its own | — |

All scripts were rerun on 24 November 2026; each finished in under 30 seconds. The second
payload-erasure run (4 ≤ d ≤ 6) reported in Appendix A, and the checks of the fan-out
normalization (Theorem 8.9) and of the surjectivity family (Theorem 8.11), were made with scripts
that are not part of this repository; they were not rerun. Script names are unchanged from the
source preprints (no clashes), and no paths needed fixing; `fanout_checks.py` must be run from this
folder so that it finds `a5lib.py`.
