import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Fib.Basic

/-!
# Sequential NOR and the grid normal form: shared definitions

Shared definitions of result family 009 ("Grid compilers and trace counting").

* `nor`, the Boolean NOR.
* `ParentArray N`: legal parent arrays `j = (j_1, …, j_N)` with `0 ≤ j_i < i`.  The entry
  `j i` (for `i : Fin N`) is the parent of position `i + 1`, so it lives in `Fin (i + 1)`.
* `trace j : Fin (N + 1) → Bool`: the Sequential NOR trace `x_0 = 1`,
  `x_i = NOR(x_{i-1}, x_{j_i})`.
* `rowMap` and `grid`: the grid normal form
  `X_{0,j} = T_j`, `X_{i,0} = L_i`, `X_{i,j} = (X_{i,j-1} ⊕ α_i) ∧ (X_{i-1,j} ⊕ β_{i,j})`,
  with all words indexed by `ℕ` (only the indices `1 ≤ i ≤ H`, `1 ≤ j ≤ W` matter).
-/

namespace GC.GridCompilers

/-- Boolean NOR. -/
def nor (a b : Bool) : Bool := !(a || b)

/-- Legal parent arrays of length `N`: the entry for position `i + 1` is a parent `< i + 1`. -/
abbrev ParentArray (N : ℕ) := (i : Fin N) → Fin (i.val + 1)

/-- The Sequential NOR values `x_0, x_1, …` of a parent array (`false` beyond `N`). -/
def traceAux {N : ℕ} (j : ParentArray N) : ℕ → Bool
  | 0 => true
  | k + 1 =>
    if h : k < N then nor (traceAux j k) (traceAux j (j ⟨k, h⟩).val) else false
termination_by k => k
decreasing_by all_goals omega

/-- The Sequential NOR trace `(x_0, …, x_N)` of a legal parent array. -/
def trace {N : ℕ} (j : ParentArray N) : Fin (N + 1) → Bool := fun i => traceAux j i.val

/-- The set of all traces of legal parent arrays of length `N`. -/
def traceSet (N : ℕ) : Finset (Fin (N + 1) → Bool) := Finset.univ.image trace

/-- One row of the grid normal form, `y_0 = ℓ`, `y_j = (y_{j-1} ⊕ a) ∧ (x_j ⊕ b_j)`, where
`x` is the north word, `a` the row polarity, `ℓ` the west bit and `b` the cell word. -/
def rowMap (a ℓ : Bool) (b x : ℕ → Bool) : ℕ → Bool
  | 0 => ℓ
  | j + 1 => (Bool.xor (rowMap a ℓ b x j) a) && (Bool.xor (x (j + 1)) (b (j + 1)))

/-- The grid normal form: `grid T L α β i j = X_{i,j}`. -/
def grid (T L α : ℕ → Bool) (β : ℕ → ℕ → Bool) : ℕ → ℕ → Bool
  | 0 => T
  | i + 1 => rowMap (α (i + 1)) (L (i + 1)) (β (i + 1)) (grid T L α β i)

/-- `x` has no two adjacent ones among the positions `1, …, W`. -/
def IsFibOn (W : ℕ) (x : ℕ → Bool) : Prop :=
  ∀ j, 1 ≤ j → j < W → ¬ (x j = true ∧ x (j + 1) = true)

end GC.GridCompilers
