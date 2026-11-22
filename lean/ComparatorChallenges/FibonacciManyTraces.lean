import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Comparator challenge: Sequential NOR Has Exactly Fibonacci-Many Traces (009d)

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

variable {N : ℕ}

/-- The coordinate of the parent of position `i + 1`, as an index of the trace. -/
def parentIdx (j : ParentArray N) (i : Fin N) : Fin (N + 1) := ⟨(j i).val, by omega⟩

/-- The census words: `x_0 = 1`, `x_1 = 0` (when `N ≥ 1`), and no two adjacent ones. -/
def IsCensusWord (x : Fin (N + 1) → Bool) : Prop :=
  x 0 = true ∧ (∀ h : 1 ≤ N, x ⟨1, by omega⟩ = false) ∧
    ∀ i : Fin N, ¬ (x i.castSucc = true ∧ x i.succ = true)

/-- Words of length `n` with no two adjacent ones, built recursively. -/
def fibWords : (n : ℕ) → Finset (Fin n → Bool)
  | 0 => Finset.univ
  | 1 => Finset.univ
  | n + 2 => (fibWords (n + 1)).image (Fin.cons (α := fun _ => Bool) false) ∪
      (fibWords n).image
        (fun y => Fin.cons (α := fun _ => Bool) true (Fin.cons (α := fun _ => Bool) false y))

/-- No two adjacent ones. -/
def NoAdj {n : ℕ} (x : Fin n → Bool) : Prop :=
  ∀ (i : ℕ) (h : i + 1 < n), ¬ (x ⟨i, by omega⟩ = true ∧ x ⟨i + 1, h⟩ = true)

/-- The canonical parent array of a census word: parent `1` where the word has a one,
parent `0` elsewhere. -/
def censusArray (x : Fin (N + 1) → Bool) : ParentArray N := fun i =>
  if x i.succ then ⟨min 1 i.val, by omega⟩ else ⟨0, by omega⟩

/-- **Census, characterization** (009d, Theorem 2.1). A word `(x_0, …, x_N)` is the trace of
a legal parent array of length `N` iff `x_0 = 1`, `x_1 = 0` and `x_{i-1} x_i = 0` for all `i`. -/
theorem census_mem_iff (x : Fin (N + 1) → Bool) : x ∈ traceSet N ↔ IsCensusWord x := by
  sorry

/-- **Census, count** (009d, Theorem 2.1). The set of Sequential NOR traces of length `N`, over
all legal parent arrays, has exactly `F_{N+1}` elements (with `F_1 = F_2 = 1`). -/
theorem census_card (N : ℕ) : (traceSet N).card = Nat.fib (N + 1) := by
  sorry

/-- The factor `A_i(x) = {p < i : NOR(x_{i-1}, x_p) = x_i}` (for the position `i + 1`). -/
def A (x : Fin (N + 1) → Bool) (i : Fin N) : Finset (Fin (i.val + 1)) :=
  Finset.univ.filter (fun p => nor (x i.castSucc) (x ⟨p.val, by omega⟩) = x i.succ)

/-- The fibre of a word: the legal parent arrays with that trace. -/
def fibre (x : Fin (N + 1) → Bool) : Finset (ParentArray N) :=
  Finset.univ.filter (fun j => trace j = x)

/-- **Fibres** (009d, Theorem 2.2, product structure). For a word with `x_0 = 1` (in particular
for every trace), the set of legal arrays with trace `x` is the product `∏_i A_i(x)`. -/
theorem fibre_eq_piFinset (x : Fin (N + 1) → Bool) (hx0 : x 0 = true) :
    fibre x = Fintype.piFinset (A x) := by
  sorry

/-- **Fibres** (009d, Theorem 2.2, factor sizes). For a trace `x`, `c_i(x) = |A_i(x)|` is the
number of available parents if `x_{i-1} = 1`, the number of earlier zeros if
`x_{i-1} = 0, x_i = 1`, and the number of earlier ones if `x_{i-1} = 0, x_i = 0`. -/
theorem card_A (x : Fin (N + 1) → Bool) (hx : x ∈ traceSet N) (i : Fin N) :
    (A x i).card =
      if x i.castSucc then i.val + 1
      else if x i.succ then
        (Finset.univ.filter (fun t : Fin (i.val + 1) => x ⟨t.val, by omega⟩ = false)).card
      else (Finset.univ.filter (fun t : Fin (i.val + 1) => x ⟨t.val, by omega⟩ = true)).card := by
  sorry

/-- **Fibres** (009d, Theorem 2.2, last identity): `∑_x ∏_i c_i(x) = N!`. -/
theorem sum_prod_card_A (N : ℕ) :
    ∑ x ∈ traceSet N, ∏ i : Fin N, (A x i).card = N.factorial := by
  sorry

/-- **Causal projection** (009d, Lemma 3.1). If two legal arrays agree outside a set `D` of
coordinates and their traces agree on `D`, the traces are equal. -/
theorem causal_projection (j j' : ParentArray N) (D : Set (Fin N))
    (hD : ∀ i, i ∉ D → (j i).val = (j' i).val)
    (hT : ∀ i ∈ D, trace j i.succ = trace j' i.succ) : trace j = trace j' := by
  sorry

section Encodings

variable {α : Type*} [Fintype α]

open Classical in
/-- The parent-variation set `D` of an encoding. -/
noncomputable def varSet (E : α → ParentArray N) : Finset (Fin N) :=
  Finset.univ.filter (fun i => ∃ a a', E a i ≠ E a' i)

open Classical in
/-- The trace-variation set `D_Tr` of an encoding (coordinates `i + 1` of the trace). -/
noncomputable def traceVarSet (E : α → ParentArray N) : Finset (Fin N) :=
  Finset.univ.filter (fun i => ∃ a a', trace (E a) i.succ ≠ trace (E a') i.succ)

/-- **Corollary 3.2**, first inequality: the traces of a decodable encoding are determined by
their restriction to `D ∩ D_Tr`, so `|𝓜| ≤ 2^{|D ∩ D_Tr|}`. -/
theorem card_le_two_pow_card_D_inter_DTr (E : α → ParentArray N)
    (R : (Fin (N + 1) → Bool) → α) (hR : ∀ a, R (trace (E a)) = a) :
    Fintype.card α ≤ 2 ^ (varSet E ∩ traceVarSet E).card := by
  sorry

/-- **Corollary 3.2**, second inequality: `|𝓜| ≤ ∏_{i ∈ D} k_i` with `k_i = |{E(a)_i}|`. -/
theorem card_le_prod_varSet (E : α → ParentArray N)
    (R : (Fin (N + 1) → Bool) → α) (hR : ∀ a, R (trace (E a)) = a) :
    Fintype.card α ≤
      ∏ i ∈ varSet E, (Finset.univ.image (fun a => E a i)).card := by
  sorry

/-- **Corollary 3.2**, third inequality: a decodable encoding at length `N` has at most
`F_{N+1}` messages. -/
theorem card_le_fib (E : α → ParentArray N) (R : (Fin (N + 1) → Bool) → α)
    (hR : ∀ a, R (trace (E a)) = a) : Fintype.card α ≤ Nat.fib (N + 1) := by
  sorry

/-- **Capacity, deterministic case** (009d, Theorem 4.2 with `δ = 0`): if a trace-only decoder
outputs lists of at most `L` messages and always lists the encoded message, then there are at
most `L · F_{N+1}` messages. -/
theorem deterministic_capacity_le (E : α → ParentArray N)
    (R : (Fin (N + 1) → Bool) → Finset α) (L : ℕ) (hR : ∀ x, (R x).card ≤ L)
    (hdec : ∀ a, a ∈ R (trace (E a))) : Fintype.card α ≤ L * Nat.fib (N + 1) := by
  sorry

end Encodings

/-- **Capacity, deterministic case, attainment** (009d, Theorem 4.2 with `δ = 0`): there is an
encoding of exactly `L · F_{N+1}` messages with a trace-only decoder that outputs lists of at
most `L` messages and always lists the encoded message. -/
theorem deterministic_capacity_attained (N L : ℕ) :
    ∃ (α : Type) (_ : Fintype α) (E : α → ParentArray N)
      (R : (Fin (N + 1) → Bool) → Finset α),
      Fintype.card α = L * Nat.fib (N + 1) ∧ (∀ x, (R x).card ≤ L) ∧
        ∀ a, a ∈ R (trace (E a)) := by
  sorry

/-- Traces of lengths `1, …, M` number `∑_{n=1}^M F_{n+1} = F_{M+3} - 2` (used in Theorem 4.2
for messages of different lengths). -/
theorem sum_census_card (M : ℕ) :
    ∑ n ∈ Finset.Icc 1 M, (traceSet n).card + 2 = Nat.fib (M + 3) := by
  sorry

end GC.GridCompilers
