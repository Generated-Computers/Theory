import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Option
import Mathlib.Order.Nat

/-!
# Comparator challenge: Homogeneous Sequential NOR Grids (009a)

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

variable (T L α : ℕ → Bool) (β : ℕ → ℕ → Bool)

/-- **Active rows** (009a, Lemma 3.1, formula). -/
theorem active_row_formula {i : ℕ} (hα : α (i + 1) = true) (j : ℕ) :
    grid T L α β (i + 1) (j + 1) =
      (!grid T L α β (i + 1) j && Bool.xor (grid T L α β i (j + 1)) (β (i + 1) (j + 1))) := by
  sorry

/-- **Active rows** (009a, Lemma 3.1): no two adjacent ones in an active row (this includes the
west bit `X_{i,0} = L_i`, so in particular the output lies in `𝓕_W` for every `W`). -/
theorem active_row_noAdj {i : ℕ} (hα : α (i + 1) = true) (j : ℕ) :
    ¬ (grid T L α β (i + 1) j = true ∧ grid T L α β (i + 1) (j + 1) = true) := by
  sorry

/-- **Reset rows** (009a, Lemma 3.2, formula): on a reset row,
`X_{i,j} = L_i ∧ ⋀_{1 ≤ t ≤ j} (N_t ⊕ β_{i,t})`. -/
theorem reset_row_iff {i : ℕ} (hα : α (i + 1) = false) (j : ℕ) :
    grid T L α β (i + 1) j = true ↔
      L (i + 1) = true ∧ ∀ t, 1 ≤ t → t ≤ j → Bool.xor (grid T L α β i t) (β (i + 1) t) = true := by
  sorry

/-- **Reset rows** (009a, Lemma 3.2, threshold form): the output of a reset row on columns
`1, …, W` is a threshold word `1^q 0^{W-q}`. -/
theorem reset_row_threshold {i : ℕ} (hα : α (i + 1) = false) (W : ℕ) :
    ∃ q ≤ W, ∀ j, 1 ≤ j → j ≤ W → (grid T L α β (i + 1) j = true ↔ j ≤ q) := by
  sorry

/-- **Remark 3.3** (orientation). With `W = 2`, `T = 00`, `L = (0,0)`, `α = (0,1)`,
`β = (00, 01)`, the reset row is `00` and the following active row is `01`. -/
theorem orientation_example :
    let T : ℕ → Bool := fun _ => false
    let L : ℕ → Bool := fun _ => false
    let α : ℕ → Bool := fun i => decide (i = 2)
    let β : ℕ → ℕ → Bool := fun i j => decide (i = 2 ∧ j = 2)
    (grid T L α β 1 1, grid T L α β 1 2) = (false, false) ∧
      (grid T L α β 2 1, grid T L α β 2 2) = (false, true) := by
  sorry

section Homogeneous

variable (b : ℕ → Bool)

/-- The homogeneous grid: every row active, every row carrying the cell word `b`. -/
abbrev homGrid : ℕ → ℕ → Bool := grid T L (fun _ => true) (fun _ => b)

/-- **Zero columns reset** (009a, Lemma 4.1): if `b_j = 0` then
`X_{i,j} = T_j ∧ ⋀_{r=1}^{i} ¬X_{r,j-1}`. -/
theorem zero_column_iff {j : ℕ} (hb : b (j + 1) = false) (i : ℕ) :
    homGrid T L b i (j + 1) = true ↔
      T (j + 1) = true ∧ ∀ r, 1 ≤ r → r ≤ i → homGrid T L b r j = false := by
  sorry

/-- A zero column is a vertical threshold word `1^s 0^{H-s}`. -/
theorem zero_column_threshold {j : ℕ} (hb : b (j + 1) = false) (H : ℕ) :
    ∃ s ≤ H, ∀ i, 1 ≤ i → i ≤ H → (homGrid T L b i (j + 1) = true ↔ i ≤ s) := by
  sorry

/-- **Diagonal collapse** (009a, Lemma 4.2). Let `c ≤ d` be a dense slab (`b_t = 1` for
`c ≤ t ≤ d`, with `c ≥ 1`). For `i ≥ 3` and `c + 2 ≤ j ≤ d`, `X_{i,j} = X_{i-1,j-1}`. -/
theorem diagonal_collapse {c d : ℕ} (hc : 1 ≤ c) (hslab : ∀ t, c ≤ t → t ≤ d → b t = true)
    {i j : ℕ} (hi : 3 ≤ i) (hj : c + 2 ≤ j) (hjd : j ≤ d) :
    homGrid T L b i j = homGrid T L b (i - 1) (j - 1) := by
  sorry

/-- Iterated diagonal collapse: `X_{i,j} = X_{i-t,j-t}` for `t ≤ min(i-2, j-c-1)`. -/
theorem diagonal_collapse_iterate {c d : ℕ} (hc : 1 ≤ c)
    (hslab : ∀ t, c ≤ t → t ≤ d → b t = true) {i j : ℕ} (hjd : j ≤ d) :
    ∀ t, t + 2 ≤ i → t + c + 1 ≤ j → homGrid T L b i j = homGrid T L b (i - t) (j - t) := by
  sorry

/-- **Diagonal collapse, consequence** (009a, Lemma 4.2): every cell of a dense slab (rows
`≥ 1`, columns `c ≤ j ≤ d`) is a copy of a slab cell in rows `1, 2` or columns `c, c + 1`. -/
theorem slab_cell_copy {c d : ℕ} (hc : 1 ≤ c) (hslab : ∀ t, c ≤ t → t ≤ d → b t = true)
    {i j : ℕ} (hi : 1 ≤ i) (hcj : c ≤ j) (hjd : j ≤ d) :
    ∃ i' j', 1 ≤ i' ∧ c ≤ j' ∧ (i' ≤ 2 ∨ j' ≤ c + 1) ∧
      homGrid T L b i j = homGrid T L b i' j' := by
  sorry

/-- **No vertical 000** (009a, Lemma 4.3). In a dense slab `c ≤ d` (`c ≥ 1`), for
`c + 1 ≤ j ≤ d` there is no `i` with `X_{i-2,j} = X_{i-1,j} = X_{i,j} = 0`. The paper states
this for `3 ≤ i ≤ H`; it also holds for `i = 2`. -/
theorem no_vertical_000 {c d : ℕ} (hc : 1 ≤ c) (hslab : ∀ t, c ≤ t → t ≤ d → b t = true)
    {i j : ℕ} (hi : 2 ≤ i) (hj : c + 1 ≤ j) (hjd : j ≤ d) :
    ¬ (homGrid T L b (i - 2) j = false ∧ homGrid T L b (i - 1) j = false ∧
      homGrid T L b i j = false) := by
  sorry

end Homogeneous

/-- `A_H = {0, 1, 2, H}` as a subset of `{0, …, H}`. -/
def rankSet (H : ℕ) : Finset (Fin (H + 1)) := {0, 1, 2, Fin.last H}

/-- `f ∈ 𝒢_H`: `f(0), f(1) ∈ A_H`, and on `{2, …, H}` the map is the identity or a constant in
`A_H`. -/
def InTransferClass (H : ℕ) (f : Fin (H + 1) → Fin (H + 1)) : Prop :=
  f 0 ∈ rankSet H ∧ f 1 ∈ rankSet H ∧
    ((∀ s : Fin (H + 1), 2 ≤ s.val → f s = s) ∨
      ∃ c ∈ rankSet H, ∀ s : Fin (H + 1), 2 ≤ s.val → f s = c)

instance (H : ℕ) : DecidablePred (InTransferClass H) := by
  intro f; unfold InTransferClass; infer_instance

/-- The finite set `𝒢_H`. -/
def transferClass (H : ℕ) : Finset (Fin (H + 1) → Fin (H + 1)) :=
  Finset.univ.filter (InTransferClass H)

/-- **Closure** (009a, Lemma 4.5): for `H ≥ 3`, `𝒢_H` is closed under composition. -/
theorem transferClass_comp {H : ℕ} (hH : 3 ≤ H) {f g : Fin (H + 1) → Fin (H + 1)}
    (hf : InTransferClass H f) (hg : InTransferClass H g) : InTransferClass H (f ∘ g) := by
  sorry

/-- **Lemma 4.4/4.5, count**: for `H ≥ 3`, `|𝒢_H| ≤ 80`. -/
theorem card_transferClass_le {H : ℕ} (hH : 3 ≤ H) : (transferClass H).card ≤ 80 := by
  sorry

end GC.GridCompilers
