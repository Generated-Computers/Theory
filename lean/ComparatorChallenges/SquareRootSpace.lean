import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Card

/-! Comparator challenge for manuscript 006c (A P-Complete Problem in Square-Root Space). -/


/-!
# Sequential NOR: basic definitions

A parent array of length `n` is modelled as a function `j : ℕ → ℕ` with `j i < i` for
`1 ≤ i ≤ n` (the values `j 0` and `j i`, `i > n`, are irrelevant).  Its trace is
`x 0 = 1`, `x i = NOR (x (i-1)) (x (j i))`.

The arc of position `i` (`1 ≤ i ≤ n`) is `(j i, i)`; every position is the right endpoint of
exactly one arc, so a page assignment is a function of the right endpoint.
-/

namespace GC.SeqNORNormalForms

/-- Boolean NOR. -/
def nor (a b : Bool) : Bool := !(a || b)

/-- `j` is a parent array of length `n`: `j i < i` for every `1 ≤ i ≤ n`. -/
def IsParentArray (n : ℕ) (j : ℕ → ℕ) : Prop :=
  ∀ i, 1 ≤ i → i ≤ n → j i < i

/-- The Sequential NOR trace: `x 0 = true` and `x (i+1) = NOR (x i) (x (j (i+1)))`.
(If `j (i+1) ≥ i+1`, which never happens for a parent array, a junk value is used.) -/
def trace (j : ℕ → ℕ) : ℕ → Bool
  | 0 => true
  | i + 1 => nor (trace j i) (if h : j (i + 1) < i + 1 then trace j (j (i + 1)) else true)
termination_by i => i

/-- Two arcs `(a,b)` and `(a',b')` (with `a < b`, `a' < b'`) cross if their endpoints
strictly interleave. -/
def Cross (a b a' b' : ℕ) : Prop :=
  (a < a' ∧ a' < b ∧ b < b') ∨ (a' < a ∧ a < b' ∧ b' < b)

/-- A `k`-page assignment of the arcs `(j i, i)`, `1 ≤ i ≤ n`: arcs on the same page do not
cross. -/
def IsPageAssignment (n : ℕ) (j : ℕ → ℕ) (k : ℕ) (page : ℕ → Fin k) : Prop :=
  ∀ i i', 1 ≤ i → i ≤ n → 1 ≤ i' → i' ≤ n → page i = page i' → ¬ Cross (j i) i (j i') i'

/-- `pg(j) ≤ k`: the arcs of `j` have a `k`-page assignment. -/
def PageNumberLE (n : ℕ) (j : ℕ → ℕ) (k : ℕ) : Prop :=
  ∃ page : ℕ → Fin k, IsPageAssignment n j k page

/-- A NOR circuit with `G ≥ 2` gates: wires `w 0 = 1`, `w 1 = 0` and
`w g = NOR (w (a g)) (w (b g))` for `2 ≤ g ≤ G`, with `a g, b g < g`. -/
structure NorCircuit where
  G : ℕ
  a : ℕ → ℕ
  b : ℕ → ℕ

/-- Well-formedness of a NOR circuit. -/
def NorCircuit.Valid (C : NorCircuit) : Prop :=
  2 ≤ C.G ∧ ∀ g, 2 ≤ g → g ≤ C.G → C.a g < g ∧ C.b g < g

/-- The wire values of a NOR circuit. -/
def NorCircuit.wire (C : NorCircuit) : ℕ → Bool
  | 0 => true
  | 1 => false
  | g + 2 => nor (if h : C.a (g + 2) < g + 2 then C.wire (C.a (g + 2)) else false)
                 (if h : C.b (g + 2) < g + 2 then C.wire (C.b (g + 2)) else false)
termination_by g => g

/-! ### Elementary lemmas -/

end GC.SeqNORNormalForms


/-!
# 006c: the counting obstruction for reset sets, and the subdivision embedding

Reset sets are represented on the positive positions: `R⋆ ∩ [1,n] = {i : x_{j_i} = 1}`.
-/

namespace GC.SeqNORNormalForms

/-- The reset set `R⋆ ∩ {1, …, n} = {i ∈ [1,n] : x_{j_i} = 1}` of an instance. -/
def resetFinset (n : ℕ) (j : ℕ → ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter (fun i => trace j (j i) = true)

/-- The instance of Theorem 6.1: `j_1 = 0`, `j_i = 0` for `i ∈ S`, `j_i = 1` otherwise. -/
def surjInstance (S : Finset ℕ) (i : ℕ) : ℕ := if i ≤ 1 then 0 else if i ∈ S then 0 else 1

/-- **Theorem 6.1 of 006c.** For every `S ⊆ {2, …, n}` the instance `surjInstance S` has
reset set `{1} ∪ S`. -/
theorem surject_instance (n : ℕ) (hn : 1 ≤ n) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 2 n) :
    IsParentArray n (surjInstance S) ∧ resetFinset n (surjInstance S) = insert 1 S := by
  sorry

/-- **Theorem 6.1 of 006c (exact range of reset sets).** The reset sets of instances of
length `n ≥ 1` are exactly the subsets of `{1, …, n}` that contain `1`. -/
theorem reset_sets_exact (n : ℕ) (hn : 1 ≤ n) (T : Finset ℕ) :
    (∃ j, IsParentArray n j ∧ resetFinset n j = T) ↔ T ⊆ Finset.Icc 1 n ∧ 1 ∈ T := by
  sorry

/-- **Theorem 6.1 of 006c (count).** There are exactly `2^{n-1}` such sets. -/
theorem reset_sets_card (n : ℕ) (hn : 1 ≤ n) :
    ((Finset.Icc 1 n).powerset.filter (fun T => 1 ∈ T)).card = 2 ^ (n - 1) := by
  sorry

/-! ### The graph `H_j` (Section 4) -/

/-- The edges of the graph `H_j`: `i - 1 → i` and `j_i → i` for `1 ≤ i ≤ n`. -/
def HEdge (n : ℕ) (j : ℕ → ℕ) (u v : ℕ) : Prop := 1 ≤ v ∧ v ≤ n ∧ (u = v - 1 ∨ u = j v)

/-- **Section 4 of 006c (the source's embedding claim is false).** No graph `H_j` contains two
distinct vertices `c, d` that both have the same two distinct in-neighbours `a, b`. Hence the
directed acyclic graph with sources `a, b` and two vertices `c, d` with in-neighbours `{a, b}`
is not a subgraph of any Sequential NOR graph on the same vertices, under any placement. -/
theorem not_subgraph (n : ℕ) (j : ℕ → ℕ) (hj : IsParentArray n j) (a b c d : ℕ) (hab : a ≠ b)
    (hcd : c ≠ d) (hac : HEdge n j a c) (hbc : HEdge n j b c) (had : HEdge n j a d)
    (hbd : HEdge n j b d) : False := by
  sorry

/-- **Lemma 4.3 of 006c (subdivision embedding).** Let a DAG on `v_1, …, v_N` (topological
order) have at most two in-neighbours per vertex, given by `p1 k` (first) and `p2 k`
(second), all `< k`. Put `P(v_k) = 2k`, helper `u_k = 2k - 1`, `j_{2k} = P(a)` for the first
in-neighbour `a` (or `0`), `j_{u_k} = P(b)` for the second in-neighbour `b` (or `0`). Then
`H_j` contains the edge `P(a) → 2k` and the path `P(b) → u_k → 2k`. -/
theorem subdivision_embed (N : ℕ) (p1 p2 : ℕ → Option ℕ)
    (hp1 : ∀ k a, p1 k = some a → 1 ≤ a ∧ a < k) (hp2 : ∀ k b, p2 k = some b → 1 ≤ b ∧ b < k) :
    let j : ℕ → ℕ := fun i =>
      if i % 2 = 0 then (match p1 (i / 2) with | some a => 2 * a | none => 0)
      else (match p2 ((i + 1) / 2) with | some b => 2 * b | none => 0)
    IsParentArray (2 * N) j ∧
    (∀ k a, 1 ≤ k → k ≤ N → p1 k = some a → HEdge (2 * N) j (2 * a) (2 * k)) ∧
    (∀ k b, 1 ≤ k → k ≤ N → p2 k = some b →
      HEdge (2 * N) j (2 * b) (2 * k - 1) ∧ HEdge (2 * N) j (2 * k - 1) (2 * k)) := by
  sorry

end GC.SeqNORNormalForms


/-!
# 006c, Theorem 5.1: fan-out normalization

The construction of the proof of Theorem 5.1, written with explicit indices. Positions `0`
and `1` (`j_1 = 0`, a rail) come first; round `i = 1, …, n` starts at `S_i`
(`S_1 = 2`, `S_{i+1} = S_i + 3i + 2`) and consists of
* for `k = 0, …, i-1` the positions `a = S_i + 3k` (parent `B_k`, the bus of the previous
  round) and `b = S_i + 3k + 1` (parent the current rail `S_i + 3k - 1`), and for
  `k ≤ i - 2` the position `c = S_i + 3k + 2` (parent `a`), the new rail;
* `y = S_i + 3i - 1` with parent `B'_{j_i} = S_i + 3 j_i + 1`;
* `g₁ = S_i + 3i` with parent the rail before step 2 (`S_i + 3i - 4`) and
  `g₂ = S_i + 3i + 1` with parent `y` (the new rail).
The bus before round `i ≥ 2` is `B_k = S_{i-1} + 3k + 1` (`k ≤ i - 2`) and
`B_{i-1} = y` of round `i - 1`; before round `1` it is `(0)`. The output is `y` of round `n`,
at position `S_n + 3n - 1`.
-/

namespace GC.SeqNORNormalForms

/-- `S_i`, the first position of round `i ≥ 1`. -/
def fanStart : ℕ → ℕ
  | 0 => 2
  | 1 => 2
  | i + 2 => fanStart (i + 1) + 3 * (i + 1) + 2

/-- The bus position `B_k` before round `i`. -/
def busPrev (i k : ℕ) : ℕ :=
  if i ≤ 1 then 0
  else if k + 2 ≤ i then fanStart (i - 1) + 3 * k + 1
  else fanStart (i - 1) + 3 * (i - 1) - 1

/-- The parent of the position `S_i + m` of round `i`. -/
def fanParent (j : ℕ → ℕ) (i m : ℕ) : ℕ :=
  if m = 3 * i - 1 then fanStart i + 3 * j i + 1
  else if m = 3 * i then fanStart i + 3 * i - 4
  else if m = 3 * i + 1 then fanStart i + 3 * i - 1
  else if m % 3 = 0 then busPrev i (m / 3)
  else fanStart i + m - 2

theorem exists_round (p : ℕ) : ∃ i, p < fanStart (i + 1) := by
  sorry

/-- The round containing position `p ≥ 2`. -/
def roundOf (p : ℕ) : ℕ := Nat.find (exists_round p)

/-- **Theorem 5.1 of 006c (the instance).** The fan-out normalized parent array. -/
def fanout (j : ℕ → ℕ) (p : ℕ) : ℕ :=
  if p ≤ 1 then 0 else fanParent j (roundOf p) (p - fanStart (roundOf p))

/-- Its length `S_n + 3n - 1`. -/
def fanLen (n : ℕ) : ℕ := fanStart n + 3 * n - 1

/-- The lengths for `n = 1, …, 7` are `4, 12, 23, 37, 54, 74, 97`, as reported in 006c. -/
theorem fanLen_values :
    fanLen 1 = 4 ∧ fanLen 2 = 12 ∧ fanLen 3 = 23 ∧ fanLen 4 = 37 ∧ fanLen 5 = 54 ∧
      fanLen 6 = 74 ∧ fanLen 7 = 97 := by
  sorry

section

variable (j : ℕ → ℕ)

/-- Candidate children of a position: every position `q` with `fanout j q = p` lies in this
set of at most two elements. -/
def fanChildren (p : ℕ) : Finset ℕ :=
  if p = 0 then {1, fanStart 1}
  else if p = 1 then {fanStart 1 + 1, fanStart 1 + 3}
  else
    let i := roundOf p
    let m := p - fanStart i
    if m = 3 * i - 1 then {fanStart i + 3 * i + 1, fanStart (i + 1) + 3 * i}
    else if m = 3 * i + 1 then {fanStart (i + 1) + 1}
    else if m % 3 = 1 then {fanStart (i + 1) + (m - 1), fanStart i + 3 * i - 1}
    else if m % 3 = 2 then {fanStart i + m + 2, fanStart i + 3 * i}
    else {fanStart i + m + 2}

/-- **Theorem 5.1 of 006c (fan-out normalization).** For every parent array `j` of length
`n ≥ 1`, `fanout j` is a parent array of length `S_n + 3n - 1 = O(n²)` with the same output
bit, in which every position is the parent of at most two positions. -/
theorem fanout_normalization (n : ℕ) (hn : 1 ≤ n) (hj : IsParentArray n j) :
    IsParentArray (fanLen n) (fanout j) ∧
    trace (fanout j) (fanLen n) = trace j n ∧
    (∀ p, ((Finset.Icc 1 (fanLen n)).filter (fun q => fanout j q = p)).card ≤ 2) ∧
    fanLen n ≤ 3 * n * n + 2 * n + 1 := by
  sorry

end

end GC.SeqNORNormalForms
