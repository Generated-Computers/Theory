import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Lattice.Nat
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# Comparator challenge: A Runwise Portfolio of NC Grid Compilers (009c)

Self-contained statement file (imports only Mathlib). The definitions are copied verbatim
from the solution files; the main theorems are stated with `sorry`.
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

namespace GC.GridCompilers

variable (W : ℕ) (β : ℕ → ℕ → Bool)

/-- The columns `1 ≤ j ≤ W` that vary on the row interval `[a, b)`. -/
def varCols (a b : ℕ) : Finset ℕ :=
  (Finset.Icc 1 W).filter (fun j => ∃ i ∈ Finset.Ioo a b, β i j ≠ β a j)

/-- The weight `w(a, b) = 1 + v(a, b)` of the row block `[a, b)`. -/
def blockWeight (a b : ℕ) : ℕ := 1 + (varCols W β a b).card

/-- The cost of the partition of rows `a, a + 1, …` into consecutive blocks of the given
heights. -/
def partitionCost : ℕ → List ℕ → ℕ
  | _, [] => 0
  | a, h :: hs => blockWeight W β a (a + h) + partitionCost (a + h) hs

/-- A partition of the rows `1, …, H` into consecutive blocks, given by its block heights. -/
def IsRowPartition (H : ℕ) (l : List ℕ) : Prop := (∀ h ∈ l, 1 ≤ h) ∧ l.sum = H

/-- `Γ(β)`: the least cost of a partition of the rows `1, …, H` into consecutive blocks. -/
noncomputable def Gamma (H : ℕ) : ℕ :=
  sInf {c | ∃ l, IsRowPartition H l ∧ partitionCost W β 1 l = c}

variable {W β}

/-- Rows `i` and `i'` carry different cell words on the columns `1, …, W`. -/
def RowsDiffer (W : ℕ) (β : ℕ → ℕ → Bool) (i i' : ℕ) : Prop :=
  ∃ j ∈ Finset.Icc 1 W, β i j ≠ β i' j

open Classical in
/-- The number of maximal segments of equal cell words among the rows `1, …, H`. -/
noncomputable def numSegments (W : ℕ) (β : ℕ → ℕ → Bool) (H : ℕ) : ℕ :=
  1 + ((Finset.Ico 1 H).filter (fun i => RowsDiffer W β i (i + 1))).card

open Classical in
/-- Number of segment boundaries `i` (rows `i`, `i+1` differ) with `a ≤ i < e`. -/
noncomputable def numBoundaries (W : ℕ) (β : ℕ → ℕ → Bool) (a e : ℕ) : ℕ :=
  ((Finset.Ico a e).filter (fun i => RowsDiffer W β i (i + 1))).card

/-- **Lower bound for `Γ`** (009c, Lemma 4.1). If the cell words of the rows `1, …, H`
pairwise differ, when they differ, in at least `d` columns, and the rows form `g` maximal
segments of equal cell words, then `Γ ≥ min(g, d + 1)`. -/
theorem gamma_ge_min_segments (H d : ℕ) (hH : 1 ≤ H)
    (hdist : ∀ i i', 1 ≤ i → i ≤ H → 1 ≤ i' → i' ≤ H → RowsDiffer W β i i' →
      d ≤ ((Finset.Icc 1 W).filter (fun j => β i j ≠ β i' j)).card) :
    min (numSegments W β H) (d + 1) ≤ Gamma W β H := by
  sorry

end GC.GridCompilers

namespace GC.GridCompilers

section Portfolio

variable {B N Y : Type*}

/-- A compiler for active blocks: on a block `b` it either fails (`none`) or passes and returns
the trace as a function of the north word. Its pass bit `(c b).isSome` depends only on `b`. -/
abbrev BlockCompiler (B N Y : Type*) := B → Option (N → Y)

/-- A compiler is sound for the semantics `truth` if every output it returns is the true trace. -/
def Sound (truth : B → N → Y) (c : BlockCompiler B N Y) : Prop :=
  ∀ b f, c b = some f → ∀ n, f n = truth b n

/-- The portfolio of a finite list of compilers: run all of them and keep the output of the first
passing one. -/
def portfolio : List (BlockCompiler B N Y) → BlockCompiler B N Y
  | [], _ => none
  | c :: cs, b => match c b with
    | some f => some f
    | none => portfolio cs b

/-- **Finite portfolios** (009c, Lemma 3.1), pass bit: the portfolio passes on a block iff some
compiler of the list passes on it. -/
theorem portfolio_isSome_iff (cs : List (BlockCompiler B N Y)) (b : B) :
    (portfolio cs b).isSome ↔ ∃ c ∈ cs, (c b).isSome := by
  sorry

/-- **Finite portfolios** (009c, Lemma 3.1), soundness: if every compiler of the list is sound,
so is the portfolio. -/
theorem portfolio_sound (truth : B → N → Y) (cs : List (BlockCompiler B N Y))
    (hcs : ∀ c ∈ cs, Sound truth c) : Sound truth (portfolio cs) := by
  sorry

end Portfolio

/-- The cell words of the second run of Proposition 4.2: `L` rows `I = 0^W` followed by `L` rows
`Q = 0^{W-1} 1`. -/
def twoBandCells (W L : ℕ) : ℕ → ℕ → Bool := fun i j => decide (L < i ∧ j = W)

/-- **Proposition 4.2, second run** (009c): `L` rows `I` followed by `L` rows `Q` have `Γ ≤ 2`. -/
theorem gamma_twoBandCells (W L : ℕ) (hL : 1 ≤ L) : Gamma W (twoBandCells W L) (L + L) ≤ 2 := by
  sorry

/-- **Common cores** (009c, Proposition 5.1): if all rows `1, …, H` share their first `m` cells
and have `s` further cells (so `W = m + s`), then `Γ ≤ min(H, 1 + s)`. -/
theorem gamma_common_core (H m s : ℕ) (β : ℕ → ℕ → Bool)
    (hcore : ∀ i i', 1 ≤ i → i ≤ H → 1 ≤ i' → i' ≤ H → ∀ j, 1 ≤ j → j ≤ m → β i j = β i' j) :
    Gamma (m + s) β H ≤ min H (1 + s) := by
  sorry

end GC.GridCompilers
