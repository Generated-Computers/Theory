# Verification scripts

Scripts for [A₅ Circuits Between NC² and P-Completeness](../paper.pdf). All are plain Python 3
using only the standard library; A₅ is realized as permutations of five points composed right
to left. Run each from any directory with `python3 <script>`; `prime_core_gadget.py` imports
`check_a5.py` from its own folder. All scripts were rerun on 24 November 2026 and each finishes in
under 30 seconds; the outputs below are from that run.

| Script | Source preprint(s) | What it checks | Paper reference |
|---|---|---|---|
| `check_a5.py` | identical copies in 004a (Pigeonhole collisions), 004b (Invisible to solvable groups), 004c (Nineteen orbits), 004d (One entry / two entries) | basic facts of A₅; power permutations and unit-power reversibility; generation by (12345),(123) with words of length ≤ 6; every element a commutator; commutator-tower values for d ≤ 6; census of pairs by generated subgroup; metabelian proper two-generated subgroups; 19 free orbits and Aut(A₅) of order 120; 171 pairwise projections; explicit mirror word; Fibonacci cycle structure; 61-probe colorings; Boolean gadgets; dominator condensation on 300 random programs; soundness, completeness and rank layering of the value/equality calculus on 12 random small programs | Lemma 6.5, Thm 6.6, Thm 4.2, Table 1, Thm 6.12, Thm 6.14 and the example after Cor 6.16, Remark 6.4, Sec. 7.1, Lemma 3.2, Thm 3.3, Thm 5.6, Thm 7.9, Thm 7.12 |
| `prime_core_gadget.py` | 004d | fraction of prime nodes in two-generator programs built from random Boolean circuits (measurement for the remark on limits of the normal form) | Remark 5.11 |
| `a5checks.py` | 004f (Opening cycles) | gadget identities; descriptor composition; symbolic cycle opening by brute force on 60 random cycles; mixer opening, inverse and bijectivity; also root-domain sizes of ready return maps and square-root counts (used for the ready-cycle classification of the group-6a paper, not in this paper) | Lemma 9.2, Thm 9.3, Lemma 9.11 |
| `frucht_strahler.py` | 004g (Barrington gadgets meet Strahler rank) | rank by reachability phases equals recursive rank; layer-by-layer evaluation; unfolding bound; quotient by earliest representatives; also Frucht-graph checks belonging to the separate note N2 (not used here) | Lemmas 10.4, 10.7, Thm 10.8, Cor 10.11 |
| `a5_checks.py` | 005b (Every hypergraph) | 61-probe selector as functions; essential support of collision blocks; bijectivity of x ↦ LxR; star barrier (i); also two checks for other manuscripts (005c, 005d), not used here | Thms 7.2, 8.3, 8.5 |
| `a5lib.py` | 005b | helper with the permutation arithmetic; not imported by `a5_checks.py` | — |

Theorem numbers refer to `paper.pdf`.

## Output of the last run

### `python3 check_a5.py`
```
A5 element orders: {1: 1, 2: 15, 3: 20, 5: 24}
exponent of A5 is 30; x^-1 = x^29 for all x
x -> x^a is a permutation of A5 iff gcd(a,30)=1 (all a in Z_30)
R_{a,b} bijective iff b in U_30, L_{a,b} bijective iff a in U_30 (all 900 pairs)
<(12345),(123)> = A5; max word length over P^+-1,Q^+-1 = 6
every element of A5 is a commutator [a,b] (both conventions)
commutator tower: val(R_{g,d}) = g for all g and d <= 6
ordered pairs by |<x,y>|: {1: 1, 2: 45, 3: 80, 4: 30, 5: 144, 6: 180, 10: 360, 12: 480, 60: 2280}, total 3600
58 distinct proper 2-generated subgroups, all with trivial second derived subgroup
2280 generating pairs; S5-conjugation acts freely; 19 orbits of size 120
|Aut(A5)| = 120 (all automorphisms are conjugations by S5)
all 171 pairwise projections of the 19 representatives generate A5 x A5
mirror word (rl, conv 0): identity on all 1320 cold pairs, non-identity on 1920 hot pairs = 16 full orbits
mirror word (rl, conv 1): identity on all 1320 cold pairs, non-identity on 1920 hot pairs = 16 full orbits
mirror word (lr, conv 0): identity on all 1320 cold pairs, non-identity on 1920 hot pairs = 16 full orbits
mirror word (lr, conv 1): identity on all 1320 cold pairs, non-identity on 1920 hot pairs = 16 full orbits
T(x,y)=(xy,x) on A5^2: cycle lengths {1: 1, 3: 25, 4: 6, 6: 90, 8: 10, 12: 20, 14: 60, 16: 30, 20: 6, 50: 24}; max 50
61-probe colorings: each has exactly one colliding pair {0, j+1}
gadget identities c^-1 a c = b, [a,b] = (14235), d^-1 [a,b] d = a hold (right-to-left): True
NOT(x)=a x^4 and AND(x,y)=d^-1 [x, c^-1 y c] d realise NOT/AND on {e,a}
dominator power condensation verified on 300 random two-generator SLPs (n<=39, 40 assignments each)
value/equality calculus: sound, complete, and layered reachability equals min Strahler rank on 12 random SLPs
```

### `python3 prime_core_gadget.py` (last three lines; the first lines repeat the output of `check_a5.py`)
```
Boolean gates 50: SLP nodes 438, prime nodes 331, fraction 0.756
Boolean gates 100: SLP nodes 750, prime nodes 542, fraction 0.723
Boolean gates 200: SLP nodes 1512, prime nodes 1107, fraction 0.732
```

### `python3 a5checks.py`
```
Thm11 eps=+1 size distribution [(0, 2686), (3, 400), (4, 225), (5, 288), (60, 1)]
Thm11 eps=-1 size distribution [(0, 900), (1, 2640), (16, 60)]
Thm11 violations [] 0
c^-1 a c == b: True
[a,b] == (1 4 2 3 5): True
d^-1 [a,b] d == a: True
all even: True
NOT/AND gadgets correct: True
AND gadget with 4th powers correct: True
descriptor composition formula ok
symbolic cycle opening: brute-force assignment count == root count on 60 random cycles
mixer opening y^2 = x^-1 v equivalent: True
mixer bijective: True
mixer inverse formula: True
square-root counts by class order: [((1, 16), 1), ((2, 0), 15), ((3, 1), 20), ((5, 1), 24)]
class orders count Counter({5: 24, 3: 20, 2: 15, 1: 1})
```

### `python3 frucht_strahler.py`
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

### `python3 a5_checks.py`
```
selector: every g has exactly one collision {0, j+1}: OK
hypergraph realization: essential support == e on 30 random hyperedges: OK
x -> LxR bijective: OK
star barrier (i): for each fixed h1 the collision of block i takes 60 values: OK
full-capacity portal / hard-coefficient switch (t=2): OK
side-premise star in A5: C-pattern equals B-pattern; patterns realised: 8 of 8
```
