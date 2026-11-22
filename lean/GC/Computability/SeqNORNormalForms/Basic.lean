import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Nat.Basic

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

theorem trace_zero (j : ℕ → ℕ) : trace j 0 = true := by
  rw [trace]

theorem trace_succ (j : ℕ → ℕ) (i : ℕ) (h : j (i + 1) < i + 1) :
    trace j (i + 1) = nor (trace j i) (trace j (j (i + 1))) := by
  rw [trace]; simp [h]

theorem trace_at (j : ℕ → ℕ) (i : ℕ) (hi : 1 ≤ i) (h : j i < i) :
    trace j i = nor (trace j (i - 1)) (trace j (j i)) := by
  obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  simpa using trace_succ j i h

/-- A step of the recurrence with an explicit parent. -/
theorem trace_step (j : ℕ → ℕ) (i p : ℕ) (hi : 1 ≤ i) (hj : j i = p) (hp : p < i) :
    trace j i = nor (trace j (i - 1)) (trace j p) := by
  rw [trace_at j i hi (hj ▸ hp), hj]

theorem NorCircuit.wire_zero (C : NorCircuit) : C.wire 0 = true := by rw [NorCircuit.wire]

theorem NorCircuit.wire_one (C : NorCircuit) : C.wire 1 = false := by rw [NorCircuit.wire]

theorem NorCircuit.wire_gate (C : NorCircuit) (g : ℕ) (hg : 2 ≤ g) (ha : C.a g < g)
    (hb : C.b g < g) : C.wire g = nor (C.wire (C.a g)) (C.wire (C.b g)) := by
  obtain ⟨g, rfl⟩ : ∃ g', g = g' + 2 := ⟨g - 2, by omega⟩
  rw [NorCircuit.wire]; simp [ha, hb]

theorem cross_symm {a b a' b' : ℕ} : Cross a b a' b' → Cross a' b' a b := by
  unfold Cross; omega

/-- **Lemma 2.1 of 006a** (elementary facts). -/
theorem basic_facts (n : ℕ) (j : ℕ → ℕ) (hj : IsParentArray n j) (i : ℕ) (hi : 1 ≤ i)
    (hin : i ≤ n) :
    (trace j i = true ↔ trace j (i - 1) = false ∧ trace j (j i) = false) ∧
    (trace j (i - 1) = true → trace j i = false) ∧
    (trace j (i - 1) = false → trace j i = !trace j (j i)) ∧
    (j i = 0 → trace j i = false) := by
  have h := trace_at j i hi (hj i hi hin)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h]; cases trace j (i - 1) <;> cases trace j (j i) <;> simp [nor]
  · intro h1; rw [h, h1]; simp [nor]
  · intro h1; rw [h, h1]; simp [nor]
  · intro h0; rw [h, h0, trace_zero]; simp [nor]

end GC.SeqNORNormalForms
