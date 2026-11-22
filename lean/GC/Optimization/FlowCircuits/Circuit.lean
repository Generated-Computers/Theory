import Mathlib.Data.Fintype.Fin
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Basic.Real.Basic

/-!
# Monotone circuits in topological order

A monotone circuit on vertices `Fin n`: every vertex is an input with a fixed Boolean value or an
AND/OR gate with two children (which may coincide) of smaller index. `MonCircuit.val` is the value
of a vertex. Used by manuscripts 003d and 003f.
-/

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

lemma val_input {v : Fin n} {b : Bool} (h : C.node v = .input b) : C.val v = b := by
  rw [val]; split <;> simp_all

lemma val_gate {v : Fin n} {a : Bool} {c₁ c₂ : Fin n} (h : C.node v = .gate a c₁ c₂) :
    C.val v = if a then C.val c₁ && C.val c₂ else C.val c₁ || C.val c₂ := by
  rw [val]; split <;> simp_all

end MonCircuit

end GC.FlowCircuits
