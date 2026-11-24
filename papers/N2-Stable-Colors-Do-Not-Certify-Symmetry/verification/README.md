# Verification scripts

| Script | Source preprint | What it checks |
|---|---|---|
| `frucht_strahler.py` | Stable Colors Do Not Certify Symmetry | Builds the Frucht graph from LCF code $`[-5,-2,-4,2,5,-2,2,5,-2,-5,4,2]`$; checks 12 vertices, 18 edges, all degrees 3; counts automorphisms by exhaustive backtracking (1); runs color refinement on the colored incidence graph (stable after 1 round with classes of sizes 12 and 18) — Theorem 3.1. Checks the Burnside count of Theorem 4.1 is at least $`d^q/q`$ for $`2\le d\le5`$, $`q\le 11`$. The remaining checks (Strahler rank via reachability phases, rank-by-rank evaluation, leaf bound, quotient circuits) were in the script of the source preprint and concern Strahler-rank compilers; they are not used in this paper. |

Run: `python3 verification/frucht_strahler.py` (Python 3, standard library only; under 1 s).

Output of the run on 24 November 2026:

```
Frucht: vertices 12 edges 18 degrees {3}
Frucht automorphism group order: 1
incidence graph: stable color classes Counter({1: 18, 0: 12}) after 1 round(s)
C_q orbit counts >= d^q/q: True
rank via reachability phases == recursive rank: True
layered (rank-by-rank) evaluation correct: True
leaves of unfolding >= 2^rank: True
quotient by earliest representatives acyclic and value-preserving: True
```
