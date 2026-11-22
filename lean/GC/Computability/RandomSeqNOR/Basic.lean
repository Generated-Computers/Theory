import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Sequential NOR: instances, traces, and the GF(2) calculus

An instance of Sequential NOR is a pointer sequence `j₁, j₂, …` with `0 ≤ jᵢ < i`.
We work with infinite pointer sequences (the "infinite embedding" of the papers); a length-`n`
instance is the restriction to `1, …, n`, and all quantities at positions `≤ n` depend only on
`j₁, …, jₙ` (see `trace_congr`).

The trace is `x*₀ = 1`, `x*ᵢ = NOR(x*ᵢ₋₁, x*_{jᵢ}) = (1 + x*ᵢ₋₁)(1 + x*_{jᵢ})` over `GF(2) = ZMod 2`.
-/

namespace GC.RandomSeqNOR

/-- A Sequential NOR instance (infinite pointer sequence): gate `i ≥ 1` reads `i - 1` and `j i`,
with `j i < i`. The value `j 0` is irrelevant. -/
structure Inst where
  /-- The pointer of gate `i`. -/
  j : ℕ → ℕ
  /-- Pointers go strictly backwards. -/
  j_lt : ∀ i, 0 < i → j i < i

/-- `NOR` over `GF(2)`: `NOR(a, b) = (1 + a)(1 + b)`. -/
def nor (a b : ZMod 2) : ZMod 2 := (1 + a) * (1 + b)

/-- Majority over `GF(2)`: `MAJ(a, b, c) = ab + bc + ca`. -/
def maj (a b c : ZMod 2) : ZMod 2 := a * b + b * c + c * a

/-- The trace `x*` of an instance: `x*₀ = 1`, `x*ᵢ = (1 + x*ᵢ₋₁)(1 + x*_{jᵢ})`. -/
def trace (P : Inst) : ℕ → ZMod 2
  | 0 => 1
  | i + 1 => (1 + trace P i) * (1 + trace P (P.j (i + 1)))
termination_by i => i
decreasing_by
  · omega
  · exact P.j_lt (i + 1) (Nat.succ_pos i)

/-- Gate `i ≥ 1` is a NOT gate when `jᵢ = i - 1`. -/
def IsNot (P : Inst) (i : ℕ) : Prop := P.j i + 1 = i

instance (P : Inst) (i : ℕ) : Decidable (IsNot P i) := by unfold IsNot; infer_instance

theorem trace_zero (P : Inst) : trace P 0 = 1 := by rw [trace]

theorem trace_succ (P : Inst) (i : ℕ) :
    trace P (i + 1) = (1 + trace P i) * (1 + trace P (P.j (i + 1))) := by rw [trace]


/-! ### Arithmetic in `GF(2)` -/

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a; decide

theorem zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  revert a; decide

theorem zmod2_mul_self (a : ZMod 2) : a * a = a := by
  revert a; decide

theorem zmod2_add_eq_zero_iff (a b : ZMod 2) : a + b = 0 ↔ a = b := by
  revert a b; decide

theorem zmod2_ne_one_iff (a : ZMod 2) : a ≠ 1 ↔ a = 0 := by
  revert a; decide

theorem zmod2_mul_eq_zero_of_not (a b : ZMod 2) (h : ¬ (a = 1 ∧ b = 1)) : a * b = 0 := by
  revert a b; decide

/-! ### Basic facts about the trace -/

theorem IsNot.lt {P : Inst} {i : ℕ} (h : IsNot P i) : 0 < i := by
  unfold IsNot at h; omega

theorem isNot_succ_iff (P : Inst) (i : ℕ) : IsNot P (i + 1) ↔ P.j (i + 1) = i := by
  unfold IsNot; omega

/-- Gate `1` always reads position `0`. -/
theorem j_one (P : Inst) : P.j 1 = 0 := by
  have := P.j_lt 1 one_pos; omega

/-- `x*₁ = 0` in every instance. -/
theorem trace_one (P : Inst) : trace P 1 = 0 := by
  rw [trace_succ, trace_zero, j_one, trace_zero]; decide

/-- A NOT gate complements its predecessor. -/
theorem trace_succ_of_isNot (P : Inst) (i : ℕ) (h : IsNot P (i + 1)) :
    trace P (i + 1) = 1 + trace P i := by
  rw [trace_succ, (isNot_succ_iff P i).1 h, zmod2_mul_self]

/-- The trace is a NOR of its two inputs. -/
theorem trace_succ_eq_nor (P : Inst) (i : ℕ) :
    trace P (i + 1) = nor (trace P i) (trace P (P.j (i + 1))) := trace_succ P i

/-- Ones are never adjacent in the trace. -/
theorem trace_succ_eq_zero_of_eq_one (P : Inst) {i : ℕ} (h : trace P i = 1) :
    trace P (i + 1) = 0 := by
  rw [trace_succ, h]
  generalize trace P (P.j (i + 1)) = b
  revert b; decide

/-- Adaptedness: the trace on `[0, n]` depends only on the pointers `j₁, …, jₙ`. -/
theorem trace_congr {P Q : Inst} {n : ℕ} (h : ∀ i, 0 < i → i ≤ n → P.j i = Q.j i) :
    ∀ i ≤ n, trace P i = trace Q i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    cases i with
    | zero => rw [trace_zero, trace_zero]
    | succ i =>
      have hj := h (i + 1) (Nat.succ_pos i) hi
      have hlt := P.j_lt (i + 1) (Nat.succ_pos i)
      rw [trace_succ, trace_succ, ih i (by omega) (by omega), hj,
        ih (Q.j (i + 1)) (by omega) (by omega)]

end GC.RandomSeqNOR
