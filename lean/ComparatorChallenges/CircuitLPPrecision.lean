import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Fin
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Logic.Relation
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-! Comparator challenge for result family 003 (generated from the solution files: the
definitions are verbatim, the main theorems are stated with `sorry`). -/

namespace GC.FlowCircuits

/-- A Boolean value as the real number `0` or `1`. -/
def b2r (b : Bool) : ℝ := if b then 1 else 0

/-- A vertex of a monotone circuit: an input with a fixed value, or a gate
(`isAnd = true` for AND, `false` for OR) with two children. -/
inductive Node (n : ℕ) where
  | input (b : Bool)
  | gate (isAnd : Bool) (c₁ c₂ : Fin n)

/-- A monotone fan-in-two circuit on `Fin n`, children have smaller index. -/
structure MonCircuit (n : ℕ) where
  node : Fin n → Node n
  topo : ∀ v a c₁ c₂, node v = .gate a c₁ c₂ → c₁ < v ∧ c₂ < v

namespace MonCircuit

variable {n : ℕ}

/-- The Boolean value of a vertex. -/
def val (C : MonCircuit n) (v : Fin n) : Bool :=
  match h : C.node v with
  | .input b => b
  | .gate a c₁ c₂ =>
    have := C.topo v a c₁ c₂ h
    if a then val C c₁ && val C c₂ else val C c₁ || val C c₂
termination_by v
decreasing_by all_goals first | exact this.1 | exact this.2

variable (C : MonCircuit n)

end MonCircuit

end GC.FlowCircuits

namespace GC.FlowCircuits

open Finset

namespace MonCircuit

variable {n : ℕ} (C : MonCircuit n)

/-- Feasibility for the circuit LP of Section 4: every variable in `[0,1]`, inputs fixed, and
for `z = x ∨ y`: `z ≥ x`, `z ≥ y`, `z ≤ x + y`; for `z = x ∧ y`: `z ≤ x`, `z ≤ y`,
`z ≥ x + y - 1`. -/
def LPFeasible (x : Fin n → ℝ) : Prop :=
  ∀ v, (0 ≤ x v ∧ x v ≤ 1) ∧ (∀ b, C.node v = .input b → x v = b2r b) ∧
    (∀ c₁ c₂, C.node v = .gate false c₁ c₂ → x c₁ ≤ x v ∧ x c₂ ≤ x v ∧ x v ≤ x c₁ + x c₂) ∧
    (∀ c₁ c₂, C.node v = .gate true c₁ c₂ → x v ≤ x c₁ ∧ x v ≤ x c₂ ∧ x c₁ + x c₂ - 1 ≤ x v)

/-- **Theorem 4.1 (sparse circuit LP; Dobkin–Lipton–Reiss).** The circuit LP of a monotone
circuit with fixed inputs has exactly one feasible point, the vector of gate values. -/
theorem circuitLP_unique (x : Fin n → ℝ) :
    C.LPFeasible x ↔ x = fun v => b2r (C.val v) := by
  sorry

end MonCircuit

/-- `δ = 1 / (2 (F_{n+1} - 1))`. -/
noncomputable def fibDelta (n : ℕ) : ℝ := 1 / (2 * ((Nat.fib (n + 1) : ℝ) - 1))

/-- The point `x̃_i = δ (F_{i+1} - 1)`. -/
noncomputable def fibPoint (n i : ℕ) : ℝ := fibDelta n * ((Nat.fib (i + 1) : ℝ) - 1)

/-- **Theorem 4.2 (exponentially accurate feasibility is necessary).** For the Fibonacci OR ladder
`x_0 = x_1 = 0`, `x_i = x_{i-1} ∨ x_{i-2}` (`2 ≤ i ≤ n`), whose exact value vector is `0`, the
point `x̃` satisfies `x̃_0 = x̃_1 = 0`, `x̃_n = 1/2`, all box constraints and lower OR inequalities
exactly, and violates every upper OR inequality `x_i ≤ x_{i-1} + x_{i-2}` by exactly `δ`. -/
theorem fib_precision (n : ℕ) (hn : 2 ≤ n) :
    fibPoint n 0 = 0 ∧ fibPoint n 1 = 0 ∧ fibPoint n n = 1 / 2 ∧
    (∀ i ≤ n, 0 ≤ fibPoint n i ∧ fibPoint n i ≤ 1) ∧
    ∀ i, i + 2 ≤ n →
      fibPoint n (i + 1) ≤ fibPoint n (i + 2) ∧ fibPoint n i ≤ fibPoint n (i + 2) ∧
      fibPoint n (i + 2) - (fibPoint n (i + 1) + fibPoint n i) = fibDelta n := by
  sorry

open Real in
theorem fibDelta_bounds (n : ℕ) (hn : 2 ≤ n) :
    1 / (2 * goldenRatio ^ n) ≤ fibDelta n ∧ fibDelta n ≤ 1 / goldenRatio ^ (n - 1) := by
  sorry

/-- The matrix `T_m` of the upper OR inequalities `x_i - x_{i-1} - x_{i-2} ≤ 0` (`2 ≤ i ≤ n`) on
the columns `x_2, …, x_n` (`m = n - 1`): ones on the diagonal, minus ones on the first two
subdiagonals. -/
def ladderMatrix (m : ℕ) : Matrix (Fin m) (Fin m) ℤ := fun i j =>
  (if j = i then 1 else 0) - (if j.val + 1 = i.val then 1 else 0) -
    (if j.val + 2 = i.val then 1 else 0)

/-- `det T_m = 1`. -/
theorem ladder_det (m : ℕ) : (ladderMatrix m).det = 1 := by
  sorry

/-- **Theorem 4.3 (Fibonacci subdeterminant).** The `(m-1) × (m-1)` minor of `T_m` obtained by
deleting the first row and the last column has absolute value `F_m` (here `m = k + 1`). -/
theorem ladder_minor (k : ℕ) :
    |((ladderMatrix (k + 1)).submatrix Fin.succ Fin.castSucc).det| = Nat.fib (k + 1) := by
  sorry

namespace MonCircuit

variable {n : ℕ} (C : MonCircuit n)

/-- The selected child of an OR gate under an OR strategy `σ` (`σ v = false` selects the first
child, `true` the second). -/
def sel (σ : Fin n → Bool) (v c₁ c₂ : Fin n) : Fin n := if σ v then c₂ else c₁

/-- The non-selected child. -/
def unsel (σ : Fin n → Bool) (v c₁ c₂ : Fin n) : Fin n := if σ v then c₁ else c₂

/-- Edges of the strategy graph: both child edges of an AND gate, the selected child edge of an
OR gate. -/
def StratEdge (σ : Fin n → Bool) (v c : Fin n) : Prop :=
  ∃ c₁ c₂, (C.node v = .gate true c₁ c₂ ∧ (c = c₁ ∨ c = c₂)) ∨
    (C.node v = .gate false c₁ c₂ ∧ c = sel σ v c₁ c₂)

/-- The losing set `L_σ`: vertices from which a false input is reachable in the strategy
graph. -/
def Losing (σ : Fin n → Bool) (v : Fin n) : Prop :=
  ∃ w, Relation.ReflTransGen (C.StratEdge σ) v w ∧ C.node w = .input false

/-- An escape: an OR gate in `L_σ` whose non-selected child lies outside `L_σ`. -/
def Escape (σ : Fin n → Bool) (v : Fin n) : Prop :=
  C.Losing σ v ∧ ∃ c₁ c₂, C.node v = .gate false c₁ c₂ ∧ ¬ C.Losing σ (unsel σ v c₁ c₂)

/-- Simultaneous escape switching: every escape switches to its other child. -/
noncomputable def switch (σ : Fin n → Bool) : Fin n → Bool := by
  classical
  exact fun v => if C.Escape σ v then !σ v else σ v

variable {C}

/-- **Theorem 5.2 (v), and "`L_σ` contains every false vertex".** A vertex outside `L_σ` is
true. -/
theorem val_true_of_not_losing (σ : Fin n → Bool) (v : Fin n) (hv : ¬ C.Losing σ v) :
    C.val v = true := by
  sorry

/-- **Theorem 5.2 (iv).** If there is no escape, every vertex of `L_σ` is false (in particular
the output, if it lies in `L_σ`). -/
theorem val_false_of_losing (σ : Fin n → Bool) (hno : ∀ v, ¬ C.Escape σ v) (v : Fin n)
    (hv : C.Losing σ v) : C.val v = false := by
  sorry

/-- **Theorem 5.2 (i).** Simultaneous switching shrinks the losing set:
`L_{σ'} ⊆ L_σ`. -/
theorem losing_antitone (σ : Fin n → Bool) (v : Fin n) (hv : C.Losing (C.switch σ) v) :
    C.Losing σ v := by
  sorry

/-- **Theorem 5.2 (ii).** Every switched gate lies outside `L_{σ'}`. -/
theorem switched_not_losing (σ : Fin n → Bool) (v : Fin n) (he : C.Escape σ v) :
    ¬ C.Losing (C.switch σ) v := by
  sorry

end MonCircuit

namespace MonCircuit

variable {n : ℕ}

/-- The Strahler rank (Definition 5.3): inputs have rank `0`; a gate whose two children coincide
has the rank of that child; a gate with distinct children of ranks `r₁ ≥ r₂` has rank `r₁` if
`r₁ > r₂` and `r₁ + 1` if `r₁ = r₂`. -/
def sr (C : MonCircuit n) (v : Fin n) : ℕ :=
  match h : C.node v with
  | .input _ => 0
  | .gate a c₁ c₂ =>
    have := C.topo v a c₁ c₂ h
    if c₁ = c₂ then sr C c₁ else
      if sr C c₁ = sr C c₂ then sr C c₁ + 1 else max (sr C c₁) (sr C c₂)
termination_by v
decreasing_by all_goals first | exact this.1 | exact this.2

/-- The rank-biased start: every OR gate selects a child of maximum rank. -/
def rankStart (C : MonCircuit n) (v : Fin n) : Bool :=
  match C.node v with
  | .gate _ c₁ c₂ => decide (C.sr c₁ < C.sr c₂)
  | .input _ => false

/-- The strategy after `k` rounds of simultaneous escape switching from the rank-biased start. -/
noncomputable def strat (C : MonCircuit n) (k : ℕ) : Fin n → Bool :=
  (C.switch)^[k] C.rankStart

variable {C : MonCircuit n}

/-- **Theorem 5.5 (rank-biased escape bound).** Starting from the strategy that selects at every
OR gate a child of maximum Strahler rank, after `k ≥ sr(v)` rounds of simultaneous escape
switching every true vertex `v` lies outside the losing set. -/
theorem true_not_losing (v : Fin n) (hv : C.val v = true) :
    ∀ k, C.sr v ≤ k → ¬ C.Losing (C.strat k) v := by
  sorry

/-- **Theorem 5.5, conclusion.** If every vertex has Strahler rank at most `r`, then after `r`
rounds the losing set is exactly the set of false vertices, there is no escape, and the output
`o` is decided by membership in `L_r`. So the circuit is decided after computing at most `r + 1`
losing sets `L_0, …, L_r`. -/
theorem rank_bound (r : ℕ) (hr : ∀ v, C.sr v ≤ r) :
    (∀ v, C.Losing (C.strat r) v ↔ C.val v = false) ∧ (∀ v, ¬ C.Escape (C.strat r) v) := by
  sorry

end MonCircuit

end GC.FlowCircuits
