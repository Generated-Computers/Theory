import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Nat.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.Ring.Basic

/-! Comparator challenge for manuscript 006d (The First-Collision Law of Newton's Method over GF(2)). -/


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
# 006d: Newton's method over GF(2) for Sequential NOR — the first-collision law

`F_i(x) = x_i + G_i(x)`, with `G_i = 1 + x_{i-1}` at a NOT gate (`j_i = i - 1`) and
`G_i = (1 + x_{i-1})(1 + x_{j_i})` otherwise. A Newton round is `x ↦ x + d` with
`J(x) d = F(x)`, where `J(x)` is the unit lower-triangular Jacobian with respect to
`x_1, …, x_n` (convention `d_0 = 0`). We define `d` by forward substitution and prove that it
solves `J(x) d = F(x)`.
-/

namespace GC.SeqNORNormalForms

/-- Embedding of `Bool` into `𝔽₂`. -/
def toF2 (b : Bool) : ZMod 2 := if b then 1 else 0

/-- `G_i(x)`. -/
def newtonG (j : ℕ → ℕ) (x : ℕ → ZMod 2) (i : ℕ) : ZMod 2 :=
  if j i = i - 1 then 1 + x (i - 1) else (1 + x (i - 1)) * (1 + x (j i))

/-- `F_i(x) = x_i + G_i(x)`. -/
def newtonF (j : ℕ → ℕ) (x : ℕ → ZMod 2) (i : ℕ) : ZMod 2 := x i + newtonG j x i

/-- Coordinates `1, …, n` of a vector, with the convention `z_0 = 0`. -/
def dropZero (z : ℕ → ZMod 2) (k : ℕ) : ZMod 2 := if k = 0 then 0 else z k

/-- Row `i` of `J(x) z`: `z_i + z_{i-1}` at a NOT gate and
`z_i + (1 + x_{j_i}) z_{i-1} + (1 + x_{i-1}) z_{j_i}` at a binary gate (with `z_0 = 0`). -/
def jacMul (j : ℕ → ℕ) (x z : ℕ → ZMod 2) (i : ℕ) : ZMod 2 :=
  z i + (if j i = i - 1 then dropZero z (i - 1)
    else (1 + x (j i)) * dropZero z (i - 1) + (1 + x (i - 1)) * dropZero z (j i))

/-- The Newton direction `d = J(x)^{-1} F(x)`, by forward substitution (`d_0 = 0`). -/
def newtonDir (j : ℕ → ℕ) (x : ℕ → ZMod 2) : ℕ → ZMod 2
  | 0 => 0
  | i + 1 => newtonF j x (i + 1) +
      (if j (i + 1) = i then (if i = 0 then 0 else newtonDir j x i)
        else (1 + x (j (i + 1))) * (if i = 0 then 0 else newtonDir j x i) +
          (1 + x i) * (if h : j (i + 1) < i + 1 then
            (if j (i + 1) = 0 then 0 else newtonDir j x (j (i + 1))) else 0))
termination_by i => i

/-- One Newton round `x⁺ = x + d`. -/
def newtonStep (j : ℕ → ℕ) (x : ℕ → ZMod 2) (i : ℕ) : ZMod 2 := x i + newtonDir j x i

/-- The trace as a vector over `𝔽₂`. -/
def traceF2 (j : ℕ → ℕ) (i : ℕ) : ZMod 2 := toF2 (trace j i)

/-- The collision vector `q_i(e) = e_{i-1} e_{j_i}` at binary gates, `0` at NOT gates. -/
def collision (j : ℕ → ℕ) (e : ℕ → ZMod 2) (i : ℕ) : ZMod 2 :=
  if j i = i - 1 then 0 else e (i - 1) * e (j i)

section

variable (j : ℕ → ℕ)

/-- `d` solves the triangular system `J(x) d = F(x)`, so `newtonStep` is a Newton round. -/
theorem jacMul_newtonDir (x : ℕ → ZMod 2) (i : ℕ) (hi : 1 ≤ i) (hj : j i < i) :
    jacMul j x (newtonDir j x) i = newtonF j x i := by
  sorry

/-- **Lemma 2.1 of 006d (exact error identity).** For `x_0 = 1`, with `e = x + y` and
`e⁺ = x⁺ + y`, `J(x) e⁺ = q(e)` on the rows `1, …, n`. -/
theorem error_identity (n : ℕ) (hj : IsParentArray n j) (x : ℕ → ZMod 2) (hx0 : x 0 = 1)
    (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
    jacMul j x (newtonStep j x + traceF2 j) i = collision j (x + traceF2 j) i := by
  sorry

/-- **Theorem 2.2 of 006d (first-collision law).** Let `x_0 = 1`, `e = x + y`,
`e⁺ = x⁺ + y`. If `e` vanishes on `0, …, m-1` then `q(e)` vanishes on `1, …, m+1`, and the
new error vanishes up to the first collision `s(q(e))` and equals `q` there. In particular the
first error advances by at least two positions per round:
`e` vanishes below `m` ⟹ `e⁺` vanishes below `m + 2` (on `0, …, n`). -/
theorem first_collision_law (n : ℕ) (hj : IsParentArray n j) (x : ℕ → ZMod 2)
    (hx0 : x 0 = 1) :
    (∀ m, m ≤ n → (∀ i, 1 ≤ i → i < m → collision j (x + traceF2 j) i = 0) →
      (∀ i, i < m → (newtonStep j x + traceF2 j) i = 0) ∧
      (1 ≤ m → (newtonStep j x + traceF2 j) m = collision j (x + traceF2 j) m)) ∧
    (∀ m, (∀ i, i < m → (x + traceF2 j) i = 0) →
      ∀ i, i ≤ n → i < m + 2 → (newtonStep j x + traceF2 j) i = 0) := by
  sorry

/-- **Corollary 2.3 of 006d.** From every start `x⁽⁰⁾` with `x⁽⁰⁾_0 = 1`, after `t` Newton
rounds the iterate agrees with the trace on `0, …, 2t`; hence Newton's method reaches the
trace (on `0, …, n`) within `⌈n/2⌉` rounds. -/
theorem newton_rounds (n : ℕ) (hj : IsParentArray n j) (x₀ : ℕ → ZMod 2) (hx0 : x₀ 0 = 1) :
    ∀ t i, i ≤ n → i ≤ 2 * t → ((newtonStep j)^[t] x₀) i = traceF2 j i := by
  sorry

/-- **Corollary 2.3 of 006d (round count).** Newton's method is exact on `0, …, n` after
`⌈n/2⌉ = (n+1)/2` rounds, from every start with `x_0 = 1`. -/
theorem newton_converges (n : ℕ) (hj : IsParentArray n j) (x₀ : ℕ → ZMod 2) (hx0 : x₀ 0 = 1)
    (t : ℕ) (ht : (n + 1) / 2 ≤ t) : ∀ i, i ≤ n → ((newtonStep j)^[t] x₀) i = traceF2 j i := by
  sorry

/-- **Corollary 2.3 of 006d (standard start).** From `(1, 0, …, 0)` Newton's method is exact after
`⌈(n-1)/2⌉ = n/2` rounds. -/
theorem newton_converges_std (n : ℕ) (hj : IsParentArray n j) (t : ℕ) (ht : n / 2 ≤ t) :
    ∀ i, i ≤ n → ((newtonStep j)^[t] (fun k => if k = 0 then 1 else 0)) i = traceF2 j i := by
  sorry

end

/-- **Proposition 2.5 of 006d.** For `j = (0, 0, 1)` the trace is `y = (1,0,0,1)`; for
`x = (1,1,1,0)` the error is `e = (0,1,1,1)`, position `3` has no active transport parent
(`x_1 = x_2 = 1`), but `q_3(e) = e_2 e_1 = 1`. -/
theorem collision_without_active_parent :
    let j : ℕ → ℕ := fun i => if i = 3 then 1 else 0
    let x : ℕ → ZMod 2 := fun i => if i = 0 then 1 else if i = 1 then 1 else if i = 2 then 1
      else 0
    (traceF2 j 0 = 1 ∧ traceF2 j 1 = 0 ∧ traceF2 j 2 = 0 ∧ traceF2 j 3 = 1) ∧
    ((x + traceF2 j) 1 = 1 ∧ (x + traceF2 j) 2 = 1 ∧ (x + traceF2 j) 3 = 1) ∧
    x 1 = 1 ∧ x 2 = 1 ∧ collision j (x + traceF2 j) 3 = 1 := by
  sorry

end GC.SeqNORNormalForms
