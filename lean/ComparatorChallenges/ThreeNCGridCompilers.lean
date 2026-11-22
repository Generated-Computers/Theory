import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Lattice.Nat
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Group.WithOne.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Real.Sqrt

/-!
# Comparator challenge: Three NC Compilers for Sequential NOR Grids (009b)

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

/-- **Bounds for `Γ`** (009b, Lemma 3.1): for `H ≥ 1`, `1 ≤ Γ(β) ≤ min(H, W + 1)`. -/
theorem gamma_bounds (H : ℕ) (hH : 1 ≤ H) :
    1 ≤ Gamma W β H ∧ Gamma W β H ≤ min H (W + 1) := by
  sorry

end GC.GridCompilers

namespace GC.GridCompilers

/-- Rows alternating between `0^W` (odd rows) and `1^W` (even rows). -/
def altCells : ℕ → ℕ → Bool := fun i _ => decide (i % 2 = 0)

/-- **Example 3.5(b)**, corrected: if the rows alternate between `0^W` and `1^W`, then
`Γ = min(H, W + 1)` (the source states `Γ = H`, which holds only when `H ≤ W + 1`). -/
theorem gamma_alternating (H W : ℕ) (hH : 1 ≤ H) :
    Gamma W altCells H = min H (W + 1) := by
  sorry

/-- The row `I = (0^W, 0)`. -/
def rowI (x : ℕ → Bool) : ℕ → Bool := rowMap true false (fun _ => false) x

/-- The row `Q = (0^{W-1} 1, 0)`. -/
def rowQ (W : ℕ) (x : ℕ → Bool) : ℕ → Bool := rowMap true false (fun j => decide (j = W)) x

/-- **Proposition 4.5** (009b) / Proposition 2.4 (009c): the row `I` is the identity on
`𝓕_W`. -/
theorem rowI_eq (W : ℕ) (x : ℕ → Bool) (hx : IsFibOn W x) :
    ∀ j, 1 ≤ j → j ≤ W → rowI x j = x j := by
  sorry

/-- **Proposition 4.5** (009b) / Proposition 2.4 (009c): `Q` is an involution of `𝓕_W`, hence
a bijection. -/
theorem rowQ_involutive (W : ℕ) (hW : 1 ≤ W) (x : ℕ → Bool) (hx : IsFibOn W x) :
    ∀ j, 1 ≤ j → j ≤ W → rowQ W (rowQ W x) j = x j := by
  sorry

/-- The first row `(1010⋯, 0)` of the constant-image pair `S`. -/
def payloadRow1 (x : ℕ → Bool) : ℕ → Bool := rowMap true false (fun j => decide (j % 2 = 1)) x

/-- The second row `(1^W, 1)` of the constant-image pair `S`. -/
def payloadRow2 (y : ℕ → Bool) : ℕ → Bool := rowMap true true (fun _ => true) y

/-- **Example 5.4** (009b) / Proposition 2.4 (009c): the two rows `(1010⋯, 0)` and
`(1^W, 1)`, applied in this order, map every Fibonacci word to the single word `0101⋯`. -/
theorem payload_const (W : ℕ) (x : ℕ → Bool) (hx : IsFibOn W x) :
    ∀ j, j ≤ W → payloadRow2 (payloadRow1 x) j = decide (j % 2 = 0) := by
  sorry

/-- The INDEX instance of §6.1 as a legal parent array of length `2m + 3`: for `k = 1, …, m`,
`j_{2k-1} = 0`, `j_{2k} = 0` if `y_k = 0` and `2k - 1` if `y_k = 1`; then the query
`j_{2m+1} = 0`, `j_{2m+2} = 2t`, `j_{2m+3} = 2m + 2`. Entry `i` is the parent of position
`i + 1`; `y` and `t` are `0`-indexed (`y_k` is `y ⟨k - 1, _⟩`, `t` is `t.val + 1`). -/
def indexArray (m : ℕ) (y : Fin m → Bool) (t : Fin m) : ParentArray (2 * m + 3) := fun i =>
  if h : i.val < 2 * m then
    (if i.val % 2 = 1 ∧ y ⟨i.val / 2, by omega⟩ = true then ⟨i.val, by omega⟩ else ⟨0, by omega⟩)
  else if h2 : i.val = 2 * m then ⟨0, by omega⟩
  else if h3 : i.val = 2 * m + 1 then ⟨2 * (t.val + 1), by omega⟩
  else ⟨2 * m + 2, by have := i.isLt; omega⟩

/-- The payload part `j_1, …, j_{2m}` of the INDEX instance. -/
def indexPayload (m : ℕ) (y : Fin m → Bool) : List ℕ :=
  List.ofFn (fun i : Fin (2 * m) =>
    if i.val % 2 = 1 ∧ y ⟨i.val / 2, by omega⟩ = true then i.val else 0)

/-- The query part `j_{2m+1}, j_{2m+2}, j_{2m+3}` of the INDEX instance. -/
def indexQuery (m : ℕ) (t : Fin m) : List ℕ := [0, 2 * (t.val + 1), 2 * m + 2]

/-- **The INDEX gadget** (009b, §6.1): the last value of the INDEX instance is `y_t`. -/
theorem index_trace_last (m : ℕ) (y : Fin m → Bool) (t : Fin m) :
    trace (indexArray m y t) (Fin.last _) = y t := by
  sorry

/-- **Proposition 6.1(a)** (009b): a deterministic one-pass evaluator (state space `σ`,
transition `δ`, start `s₀`, output `out`) that computes `x_N` on all INDEX instances of length
`2m + 3` reaches distinct states after the payloads of distinct `y`. -/
theorem onePass_injective {σ : Type*} (δ : σ → ℕ → σ) (s₀ : σ) (out : σ → Bool) (m : ℕ)
    (hcorrect : ∀ y t, out ((List.ofFn (fun i => (indexArray m y t i).val)).foldl δ s₀) =
      trace (indexArray m y t) (Fin.last _)) :
    Function.Injective (fun y : Fin m → Bool => (indexPayload m y).foldl δ s₀) := by
  sorry

/-- **Proposition 6.1(a)** (009b), counting form: at least `2^m` states. -/
theorem card_states_ge {σ : Type*} [Fintype σ] (δ : σ → ℕ → σ) (s₀ : σ) (out : σ → Bool)
    (m : ℕ) (hcorrect : ∀ y t, out ((List.ofFn (fun i => (indexArray m y t i).val)).foldl δ s₀) =
      trace (indexArray m y t) (Fin.last _)) :
    2 ^ m ≤ Fintype.card σ := by
  sorry

/-- **Proposition 6.1(c)** (009b), monoid form: a context-independent associative summary has at
least `2^m` elements. -/
theorem summary_card {S : Type*} [Monoid S] [Fintype S] (φ : ℕ → ℕ → S) (out : S → Bool)
    (m : ℕ) (hcorrect : ∀ y t,
      out (List.ofFn (fun i : Fin (2 * m + 3) => φ (i.val + 1) (indexArray m y t i).val)).prod =
        trace (indexArray m y t) (Fin.last _)) :
    2 ^ m ≤ Fintype.card S := by
  sorry

/-- **Proposition 6.1(c)** (009b), semigroup form: if `S` is a semigroup, `φ_p(j_p) ∈ S`, and
`x_N` is a function of the product `φ_1(j_1) ⋯ φ_N(j_N)` (computed in `S`, written here in
`WithOne S` where a nonempty product of elements of `S` is an element of `S`), then
`|S| ≥ 2^m`. -/
theorem semigroup_summary_card {S : Type*} [Semigroup S] [Fintype S] (φ : ℕ → ℕ → S)
    (out : WithOne S → Bool) (m : ℕ) (hcorrect : ∀ y t,
      out (List.ofFn (fun i : Fin (2 * m + 3) =>
        (φ (i.val + 1) (indexArray m y t i).val : WithOne S))).prod =
        trace (indexArray m y t) (Fin.last _)) :
    2 ^ m ≤ Fintype.card S := by
  sorry

/-- **Proposition 6.1(c)** (009b), matrix bound, as corrected in 009b: if the summary consists of
`d × d` matrices over a finite semiring `K` with `|K| ≥ 2`, then `2^m ≤ |K|^{d²}`, hence
`d ≥ √(m / log₂|K|)` (the source claimed `d ≥ m / log₂|K|`). -/
theorem matrix_summary_dim {K : Type*} [Semiring K] [Fintype K] (hK : 2 ≤ Fintype.card K)
    (d m : ℕ) (φ : ℕ → ℕ → Matrix (Fin d) (Fin d) K) (out : Matrix (Fin d) (Fin d) K → Bool)
    (hcorrect : ∀ y t,
      out (List.ofFn (fun i : Fin (2 * m + 3) => φ (i.val + 1) (indexArray m y t i).val)).prod =
        trace (indexArray m y t) (Fin.last _)) :
    2 ^ m ≤ Fintype.card K ^ (d ^ 2) ∧
      Real.sqrt (m / Real.logb 2 (Fintype.card K)) ≤ d := by
  sorry

end GC.GridCompilers
