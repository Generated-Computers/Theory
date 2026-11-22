import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Nat.Basic

/-! Comparator challenge for manuscript 006b (A Reset Normal Form for a P-Complete Problem). -/


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
# 006b: the reset normal form of Sequential NOR

A position `i ≥ 1` is a reset if `x_{j_i} = 1`; a virtual reset sits at `-1`. Sets
`R ⊆ {-1, 1, …, n}` containing `-1` are represented by their indicator `R : ℕ → Bool` on
the positive positions (position `0` is never a reset, and `-1 ∈ R` is implicit).
-/

namespace GC.SeqNORNormalForms

/-- `pred_R(p) = max {r ∈ R : r ≤ p}` for `R ∋ -1`, `R ⊆ {-1, 1, 2, …}`. -/
def predR (R : ℕ → Bool) : ℕ → ℤ
  | 0 => -1
  | p + 1 => if R (p + 1) then ((p + 1 : ℕ) : ℤ) else predR R p

/-- The reset set `R⋆ = {-1} ∪ {i ≥ 1 : x_{j_i} = 1}` (on positive positions). -/
def resetSet (j : ℕ → ℕ) (i : ℕ) : Bool := decide (1 ≤ i) && trace j (j i)

/-- The reset operator `Φ(R) = {-1} ∪ {i ∈ [1,n] : j_i - pred_R(j_i) is odd}`. -/
def resetOp (n : ℕ) (j : ℕ → ℕ) (R : ℕ → Bool) (i : ℕ) : Bool :=
  decide (1 ≤ i ∧ i ≤ n ∧ ((j i : ℤ) - predR R (j i)) % 2 = 1)

/-- Two candidate sets agree on the positions `1, …, m`. -/
def AgreeUpTo (m : ℕ) (R R' : ℕ → Bool) : Prop := ∀ i, 1 ≤ i → i ≤ m → R i = R' i

/-- **Theorem 3.1 of 006b (reset-predecessor normal form).** For `0 ≤ i ≤ n`,
`x_i = (i - pred_{R⋆}(i)) mod 2`, and for `1 ≤ i ≤ n`, `i ∈ R⋆` iff `j_i - pred_{R⋆}(j_i)` is
odd. -/
theorem reset_normal_form (n : ℕ) (j : ℕ → ℕ) (hj : IsParentArray n j) :
    (∀ i, i ≤ n → (trace j i = true ↔ ((i : ℤ) - predR (resetSet j) i) % 2 = 1)) ∧
    (∀ i, 1 ≤ i → i ≤ n →
      (resetSet j i = true ↔ ((j i : ℤ) - predR (resetSet j) (j i)) % 2 = 1)) := by
  sorry

/-- **Theorem 3.1 (stage-wise form) / Proposition 3.3 (fixed point).** `R⋆` is a fixed point
of `Φ` on the positions `1, …, n`. -/
theorem resetOp_fixed (n : ℕ) (j : ℕ → ℕ) (hj : IsParentArray n j) :
    AgreeUpTo n (resetOp n j (resetSet j)) (resetSet j) := by
  sorry

/-- **Lemma 3.4 of 006b (first disagreement).** Let `q ∈ [1,n]` be the least position where
`R` and `Φ(R)` disagree. Then `R` agrees with `R⋆` below `q`, `q ∈ R⋆ ↔ q ∈ Φ(R)`, and
hence `q` is the first error of `R`. -/
theorem first_disagreement (n : ℕ) (j : ℕ → ℕ) (hj : IsParentArray n j) (R : ℕ → Bool)
    (q : ℕ) (hq : 1 ≤ q) (hqn : q ≤ n) (hdis : R q ≠ resetOp n j R q)
    (hmin : AgreeUpTo (q - 1) R (resetOp n j R)) :
    AgreeUpTo (q - 1) R (resetSet j) ∧ resetSet j q = resetOp n j R q ∧ R q ≠ resetSet j q := by
  sorry

/-- **Proposition 3.3 of 006b (uniqueness).** `R⋆` is the unique fixed point of `Φ` on the
positions `1, …, n`. -/
theorem resetOp_unique (n : ℕ) (j : ℕ → ℕ) (hj : IsParentArray n j) (R : ℕ → Bool)
    (hR : AgreeUpTo n (resetOp n j R) R) : AgreeUpTo n R (resetSet j) := by
  sorry

theorem resetOp_iterate_n (n : ℕ) (j : ℕ → ℕ) (hj : IsParentArray n j) (R₀ : ℕ → Bool)
    (t : ℕ) (ht : n ≤ t) : AgreeUpTo n ((resetOp n j)^[t] R₀) (resetSet j) := by
  sorry

/-- **Remark 3.6(b) of 006b.** `Φ²` is not monotone: for `j = (0,0,2,1,4)`,
`A = {-1,3,5} ⊆ B = {-1,1,2,3,4,5}` but `Φ²(A) = {-1,1,2,5} ⊄ Φ²(B) = {-1,1,2}`. -/
theorem resetOp_sq_not_monotone :
    let j : ℕ → ℕ := fun i => if i = 1 then 0 else if i = 2 then 0 else if i = 3 then 2
      else if i = 4 then 1 else if i = 5 then 4 else 0
    let A : ℕ → Bool := fun i => decide (i = 3 ∨ i = 5)
    let B : ℕ → Bool := fun i => decide (1 ≤ i ∧ i ≤ 5)
    (∀ i, A i = true → B i = true) ∧
    (∀ i, i ≤ 6 → resetOp 5 j (resetOp 5 j A) i = decide (i = 1 ∨ i = 2 ∨ i = 5)) ∧
    (∀ i, i ≤ 6 → resetOp 5 j (resetOp 5 j B) i = decide (i = 1 ∨ i = 2)) := by
  sorry

/-- **Proposition 3.2 of 006b (event queue).** With child lists `C_s = {i > s : j_i = s}` and
pending events `E_t = ⋃_{s ≤ t, x_s = 1} C_s ∩ {t+1, …, n}`: `x_i = 1` iff `x_{i-1} = 0` and
`i ∉ E_{i-1}`. -/
theorem event_queue (n : ℕ) (j : ℕ → ℕ) (hj : IsParentArray n j) (i : ℕ) (hi : 1 ≤ i)
    (hin : i ≤ n) :
    let E : ℕ → ℕ → Prop := fun t m => t < m ∧ m ≤ n ∧ ∃ s, s ≤ t ∧ trace j s = true ∧ j m = s
    (trace j i = true ↔ trace j (i - 1) = false ∧ ¬ E (i - 1) i) ∧
    (∀ m, E i m ↔ (E (i - 1) m ∧ m ≠ i) ∨ (trace j i = true ∧ i < m ∧ m ≤ n ∧ j m = i)) := by
  sorry

/-- **Theorem 3.7 of 006b (realizable traces).** Every string `z_0, …, z_n` with `z_0 = 1`,
`z_1 = 0` and no two consecutive ones is the trace of the parent array `j_1 = 0`,
`j_i = 1` if `z_i = 1` and `j_i = 0` if `z_i = 0`. -/
theorem realizable_traces (n : ℕ) (z : ℕ → Bool) (hz0 : z 0 = true) (hz1 : 1 ≤ n → z 1 = false)
    (hcons : ∀ i, 1 ≤ i → i ≤ n → z i = true → z (i - 1) = false) :
    let j : ℕ → ℕ := fun i => if i ≤ 1 then 0 else if z i then 1 else 0
    IsParentArray n j ∧ ∀ i, i ≤ n → trace j i = z i := by
  sorry

end GC.SeqNORNormalForms
