import GC.Combinatorics.GridCompilers.FibonacciTraces
import GC.Combinatorics.GridCompilers.RowPartitions
import Mathlib.Algebra.Group.WithOne.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Real.Sqrt

/-!
# Three NC compilers for Sequential NOR grids (manuscript 009b): exact lemmas

The compilers themselves (Theorems 3.4, 4.7, 5.3) and their depth bounds are *not*
formalized. We formalize:

* `gamma_bounds` (Lemma 3.1, in `RowPartitions.lean`) and `gamma_alternating`
  (Example 3.5(b), in the corrected form `Γ = min(H, W + 1)`).
* Exact row facts on the Fibonacci carrier: `rowI_eq` and `rowQ_involutive` (the two
  injective rows of Proposition 4.5 are the identity and an involution), `payload_const`
  (Example 5.4: the two rows `(1010⋯, 0)`, `(1^W, 1)` map every Fibonacci word to `0101⋯`).
* The INDEX gadget of §6.1 (`index_trace_last`) and Proposition 6.1(a),(c):
  `onePass_injective`, `card_states_ge`, `summary_injective`, `semigroup_summary_card`,
  and the matrix bound in the corrected form `d ≥ √(m / log₂|K|)` (`matrix_summary_dim`).
-/

namespace GC.GridCompilers

/-! ### Example 3.5(b): alternating rows -/

/-- Rows alternating between `0^W` (odd rows) and `1^W` (even rows). -/
def altCells : ℕ → ℕ → Bool := fun i _ => decide (i % 2 = 0)

/-- **Example 3.5(b)**, corrected: if the rows alternate between `0^W` and `1^W`, then
`Γ = min(H, W + 1)` (the source states `Γ = H`, which holds only when `H ≤ W + 1`). -/
theorem gamma_alternating (H W : ℕ) (hH : 1 ≤ H) :
    Gamma W altCells H = min H (W + 1) := by
  classical
  apply le_antisymm (gamma_bounds H hH).2
  have hdiff : ∀ i i', RowsDiffer W altCells i i' → (i % 2 = 0 ↔ ¬ i' % 2 = 0) := by
    rintro i i' ⟨j, -, hj⟩
    simp only [altCells] at hj
    by_cases h1 : i % 2 = 0 <;> by_cases h2 : i' % 2 = 0 <;> simp_all
  have hlow := gamma_ge_min_segments (W := W) (β := altCells) H W hH (by
    intro i i' _ _ _ _ hd
    have := hdiff i i' hd
    rw [Finset.filter_true_of_mem]
    · simp
    · intro j _
      simp only [altCells]
      by_cases h1 : i % 2 = 0 <;> simp_all)
  rcases Nat.eq_zero_or_pos W with rfl | hW
  · have : 1 ≤ Gamma 0 altCells H := (gamma_bounds H hH).1
    omega
  · have hseg : numSegments W altCells H = H := by
      rw [numSegments, Finset.filter_true_of_mem]
      · simp; omega
      · intro i _
        refine ⟨1, Finset.mem_Icc.2 ⟨le_rfl, hW⟩, ?_⟩
        simp only [altCells]
        by_cases h : i % 2 = 0
        · have : (i + 1) % 2 = 1 := by omega
          simp [h, this]
        · have : (i + 1) % 2 = 0 := by omega
          simp [h, this]
    rw [hseg] at hlow
    exact hlow

/-! ### Row facts on the Fibonacci carrier -/

/-- The row `I = (0^W, 0)`. -/
def rowI (x : ℕ → Bool) : ℕ → Bool := rowMap true false (fun _ => false) x

/-- The row `Q = (0^{W-1} 1, 0)`. -/
def rowQ (W : ℕ) (x : ℕ → Bool) : ℕ → Bool := rowMap true false (fun j => decide (j = W)) x

/-- On a Fibonacci word, the active row with west bit `0` and a cell word that vanishes on
`1, …, k` copies the word on `1, …, k`. -/
theorem rowMap_copy (W : ℕ) (b x : ℕ → Bool) (hx : IsFibOn W x) (k : ℕ)
    (hb : ∀ j, 1 ≤ j → j ≤ k → b j = false) (hk : k ≤ W) :
    ∀ j, 1 ≤ j → j ≤ k → rowMap true false b x j = x j := by
  intro j
  induction j with
  | zero => intro h; omega
  | succ j ih =>
    intro _ hj
    rw [rowMap, Bool.xor_true, hb (j + 1) (by omega) hj, Bool.xor_false]
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp [rowMap]
    · rw [ih hj0 (by omega)]
      have := hx j hj0 (by omega)
      cases h1 : x j <;> cases h2 : x (j + 1) <;> simp_all

/-- **Proposition 4.5** (009b) / Proposition 2.4 (009c): the row `I` is the identity on
`𝓕_W`. -/
theorem rowI_eq (W : ℕ) (x : ℕ → Bool) (hx : IsFibOn W x) :
    ∀ j, 1 ≤ j → j ≤ W → rowI x j = x j :=
  rowMap_copy W _ x hx W (fun _ _ _ => rfl) le_rfl

/-- The row `Q` copies the first `W - 1` letters. -/
theorem rowQ_eq_of_lt (W : ℕ) (x : ℕ → Bool) (hx : IsFibOn W x) :
    ∀ j, 1 ≤ j → j < W → rowQ W x j = x j := by
  intro j h1 h2
  exact rowMap_copy W _ x hx (W - 1) (fun j _ hj => by simp; omega) (by omega) j h1 (by omega)

/-- The row `Q` toggles the last letter when the letter before it is `0`. -/
theorem rowQ_last (W : ℕ) (hW : 2 ≤ W) (x : ℕ → Bool) (hx : IsFibOn W x) :
    rowQ W x W = (!x (W - 1) && !x W) := by
  obtain ⟨V, rfl⟩ : ∃ V, W = V + 2 := ⟨W - 2, by omega⟩
  rw [rowQ, rowMap, Bool.xor_true]
  have := rowQ_eq_of_lt (V + 2) x hx (V + 1) (by omega) (by omega)
  rw [rowQ] at this
  rw [this]
  simp

theorem rowQ_isFibOn (W : ℕ) (x : ℕ → Bool) : IsFibOn W (rowQ W x) := by
  intro j _ _ ⟨h1, h2⟩
  rw [rowQ, rowMap, Bool.xor_true] at h2
  rw [rowQ] at h1
  simp [h1] at h2

/-- **Proposition 4.5** (009b) / Proposition 2.4 (009c): `Q` is an involution of `𝓕_W`, hence
a bijection. -/
theorem rowQ_involutive (W : ℕ) (hW : 1 ≤ W) (x : ℕ → Bool) (hx : IsFibOn W x) :
    ∀ j, 1 ≤ j → j ≤ W → rowQ W (rowQ W x) j = x j := by
  intro j h1 h2
  have hQ := rowQ_isFibOn W x
  rcases Nat.lt_or_ge j W with hj | hj
  · rw [rowQ_eq_of_lt W _ hQ j h1 hj, rowQ_eq_of_lt W x hx j h1 hj]
  · obtain rfl : j = W := by omega
    rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · obtain rfl : j = 1 := by omega
      simp [rowQ, rowMap]
    · rw [rowQ_last j hj2 _ hQ, rowQ_last j hj2 x hx, rowQ_eq_of_lt j x hx (j - 1) (by omega)
        (by omega)]
      have := hx (j - 1) (by omega) (by omega)
      rw [show j - 1 + 1 = j by omega] at this
      cases h1 : x (j - 1) <;> cases h2 : x j <;> simp_all

/-- The first row `(1010⋯, 0)` of the constant-image pair `S`. -/
def payloadRow1 (x : ℕ → Bool) : ℕ → Bool := rowMap true false (fun j => decide (j % 2 = 1)) x

/-- The second row `(1^W, 1)` of the constant-image pair `S`. -/
def payloadRow2 (y : ℕ → Bool) : ℕ → Bool := rowMap true true (fun _ => true) y

theorem payloadRow1_even (W : ℕ) (x : ℕ → Bool) (hx : IsFibOn W x) :
    ∀ k, 2 * k ≤ W → payloadRow1 x (2 * k) = false := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    have e : 2 * (k + 1) = (2 * k + 1) + 1 := by ring
    rw [e, payloadRow1, rowMap, Bool.xor_true]
    have hc : decide ((2 * k + 1 + 1) % 2 = 1) = false := by simp; omega
    rw [hc, Bool.xor_false]
    cases hxk : x (2 * k + 1 + 1)
    · simp
    · have hprev : x (2 * k + 1) = false := by
        have := hx (2 * k + 1) (by omega) (by omega)
        cases h : x (2 * k + 1) <;> simp_all
      have hy : rowMap true false (fun j => decide (j % 2 = 1)) x (2 * k + 1) = true := by
        rw [rowMap, Bool.xor_true, hprev]
        have := ih (by omega)
        rw [payloadRow1] at this
        rw [this]
        simp
      rw [hy]; rfl

/-- **Example 5.4** (009b) / Proposition 2.4 (009c): the two rows `(1010⋯, 0)` and
`(1^W, 1)`, applied in this order, map every Fibonacci word to the single word `0101⋯`. -/
theorem payload_const (W : ℕ) (x : ℕ → Bool) (hx : IsFibOn W x) :
    ∀ j, j ≤ W → payloadRow2 (payloadRow1 x) j = decide (j % 2 = 0) := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    rw [payloadRow2, rowMap, Bool.xor_true, Bool.xor_true]
    have ih' := ih (by omega)
    rw [payloadRow2] at ih'
    rw [ih']
    rcases Nat.even_or_odd j with ⟨k, hk⟩ | ⟨k, hk⟩
    · have : j % 2 = 0 := by omega
      simp [this]; omega
    · have h1 : (j + 1) % 2 = 0 := by omega
      have : j % 2 = 1 := by omega
      have hy := payloadRow1_even W x hx (k + 1) (by omega)
      rw [show 2 * (k + 1) = j + 1 by omega] at hy
      simp [this, h1, hy]

/-! ### The INDEX gadget (§6.1) -/

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

theorem indexArray_list (m : ℕ) (y : Fin m → Bool) (t : Fin m) :
    List.ofFn (fun i => (indexArray m y t i).val) = indexPayload m y ++ indexQuery m t := by
  rw [List.ofFn_add, indexPayload, indexQuery]
  congr 1
  · apply List.ofFn_inj.2
    funext i
    simp only [indexArray, Fin.val_castLE, i.isLt, dif_pos]
    split_ifs <;> rfl
  · simp [List.ofFn_succ, indexArray]

private theorem indexArray_val (m : ℕ) (y : Fin m → Bool) (t : Fin m) (i : ℕ)
    (hi : i < 2 * m + 3) : (indexArray m y t ⟨i, hi⟩ : ℕ) =
      if h : i < 2 * m then
        (if i % 2 = 1 ∧ y ⟨i / 2, by omega⟩ = true then i else 0)
      else if i = 2 * m then 0 else if i = 2 * m + 1 then 2 * (t.val + 1) else 2 * m + 2 := by
  simp only [indexArray]
  split_ifs <;> rfl

/-- The payload part of the INDEX trace: `x_{2k-1} = 0` and `x_{2k} = y_k`. -/
theorem index_trace_payload (m : ℕ) (y : Fin m → Bool) (t : Fin m) (k : ℕ) (hk : k < m) :
    traceAux (indexArray m y t) (2 * k + 1) = false ∧
      traceAux (indexArray m y t) (2 * k + 2) = y ⟨k, hk⟩ := by
  have h1 : traceAux (indexArray m y t) (2 * k + 1) = false := by
    rw [traceAux_succ _ _ (by omega), indexArray_val]
    rw [dif_pos (by omega), if_neg (by omega), traceAux_zero]
    simp [nor]
  refine ⟨h1, ?_⟩
  rw [show 2 * k + 2 = (2 * k + 1) + 1 by ring, traceAux_succ _ _ (by omega), indexArray_val,
    dif_pos (by omega), h1]
  have hk2 : (2 * k + 1) / 2 = k := by omega
  by_cases hy : y ⟨k, hk⟩ = true
  · rw [if_pos ⟨by omega, by simpa [hk2] using hy⟩, h1, hy]; rfl
  · rw [if_neg (fun h => hy (by simpa [hk2] using h.2)), traceAux_zero]
    simp only [Bool.not_eq_true] at hy
    rw [hy]; rfl

/-- **The INDEX gadget** (009b, §6.1): the last value of the INDEX instance is `y_t`. -/
theorem index_trace_last (m : ℕ) (y : Fin m → Bool) (t : Fin m) :
    trace (indexArray m y t) (Fin.last _) = y t := by
  have h1 : traceAux (indexArray m y t) (2 * m + 1) = false := by
    rw [traceAux_succ _ _ (by omega), indexArray_val, dif_neg (by omega), if_pos rfl,
      traceAux_zero]
    simp [nor]
  have h2 : traceAux (indexArray m y t) (2 * m + 2) = !y t := by
    rw [traceAux_succ _ _ (by omega), indexArray_val, dif_neg (by omega), if_neg (by omega),
      if_pos rfl, h1, show 2 * (t.val + 1) = 2 * t.val + 2 by ring,
      (index_trace_payload m y t t.val t.isLt).2]
    cases y t <;> rfl
  show traceAux (indexArray m y t) (2 * m + 2 + 1) = y t
  rw [traceAux_succ _ _ (by omega), indexArray_val, dif_neg (by omega), if_neg (by omega),
    if_neg (by omega), h2]
  cases y t <;> rfl

/-! ### Proposition 6.1(a): one-pass evaluators -/

/-- **Proposition 6.1(a)** (009b): a deterministic one-pass evaluator (state space `σ`,
transition `δ`, start `s₀`, output `out`) that computes `x_N` on all INDEX instances of length
`2m + 3` reaches distinct states after the payloads of distinct `y`. -/
theorem onePass_injective {σ : Type*} (δ : σ → ℕ → σ) (s₀ : σ) (out : σ → Bool) (m : ℕ)
    (hcorrect : ∀ y t, out ((List.ofFn (fun i => (indexArray m y t i).val)).foldl δ s₀) =
      trace (indexArray m y t) (Fin.last _)) :
    Function.Injective (fun y : Fin m → Bool => (indexPayload m y).foldl δ s₀) := by
  intro y y' h
  funext t
  have e := hcorrect y t
  have e' := hcorrect y' t
  rw [indexArray_list, List.foldl_append, index_trace_last] at e e'
  simp only at h
  rw [← e, ← e', h]

/-- **Proposition 6.1(a)** (009b), counting form: at least `2^m` states. -/
theorem card_states_ge {σ : Type*} [Fintype σ] (δ : σ → ℕ → σ) (s₀ : σ) (out : σ → Bool)
    (m : ℕ) (hcorrect : ∀ y t, out ((List.ofFn (fun i => (indexArray m y t i).val)).foldl δ s₀) =
      trace (indexArray m y t) (Fin.last _)) :
    2 ^ m ≤ Fintype.card σ := by
  have := Fintype.card_le_of_injective _ (onePass_injective δ s₀ out m hcorrect)
  simpa using this

/-! ### Proposition 6.1(c): associative summaries -/

/-- **Proposition 6.1(c)** (009b), injectivity: in a context-independent associative summary
(a monoid `S`, maps `φ_p(j_p) ∈ S` for the positions `p = 1, …, N`, and an output map with
`x_N = out(φ_1(j_1) ⋯ φ_N(j_N))` on the INDEX instances), distinct payloads have distinct
prefix products. -/
theorem summary_injective {S : Type*} [Monoid S] (φ : ℕ → ℕ → S) (out : S → Bool) (m : ℕ)
    (hcorrect : ∀ y t,
      out (List.ofFn (fun i : Fin (2 * m + 3) => φ (i.val + 1) (indexArray m y t i).val)).prod =
        trace (indexArray m y t) (Fin.last _)) :
    Function.Injective (fun y : Fin m → Bool =>
      (List.ofFn (fun i : Fin (2 * m) => φ (i.val + 1)
        (if i.val % 2 = 1 ∧ y ⟨i.val / 2, by omega⟩ = true then i.val else 0))).prod) := by
  intro y y' h
  funext t
  have split : ∀ y : Fin m → Bool,
      (List.ofFn (fun i : Fin (2 * m + 3) => φ (i.val + 1) (indexArray m y t i).val)).prod =
        (List.ofFn (fun i : Fin (2 * m) => φ (i.val + 1)
          (if i.val % 2 = 1 ∧ y ⟨i.val / 2, by omega⟩ = true then i.val else 0))).prod *
        (φ (2 * m + 1) 0 * (φ (2 * m + 2) (2 * (t.val + 1)) * φ (2 * m + 3) (2 * m + 2))) := by
    intro y
    rw [List.ofFn_add, List.prod_append]
    congr 1
    · congr 1
      apply List.ofFn_inj.2
      funext i
      have := indexArray_val m y t i.val (by omega)
      rw [dif_pos i.isLt] at this
      exact congrArg _ this
    · simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
      show φ (2 * m + 1) (indexArray m y t ⟨2 * m, by omega⟩ : ℕ) *
        (φ (2 * m + 2) (indexArray m y t ⟨2 * m + 1, by omega⟩ : ℕ) *
          φ (2 * m + 3) (indexArray m y t ⟨2 * m + 2, by omega⟩ : ℕ)) = _
      rw [indexArray_val, indexArray_val, indexArray_val, dif_neg (by omega), if_pos rfl,
        dif_neg (by omega), if_neg (by omega), if_pos rfl, dif_neg (by omega), if_neg (by omega),
        if_neg (by omega)]
  have e := hcorrect y t
  have e' := hcorrect y' t
  rw [split, index_trace_last] at e e'
  simp only at h
  rw [← e, ← e', h]

/-- **Proposition 6.1(c)** (009b), monoid form: a context-independent associative summary has at
least `2^m` elements. -/
theorem summary_card {S : Type*} [Monoid S] [Fintype S] (φ : ℕ → ℕ → S) (out : S → Bool)
    (m : ℕ) (hcorrect : ∀ y t,
      out (List.ofFn (fun i : Fin (2 * m + 3) => φ (i.val + 1) (indexArray m y t i).val)).prod =
        trace (indexArray m y t) (Fin.last _)) :
    2 ^ m ≤ Fintype.card S := by
  have := Fintype.card_le_of_injective _ (summary_injective φ out m hcorrect)
  simpa using this

theorem prod_coe_withOne {S : Type*} [Semigroup S] :
    ∀ (l : List S), l ≠ [] → ∃ c : S, (l.map ((↑) : S → WithOne S)).prod = c
  | [], h => absurd rfl h
  | [a], _ => ⟨a, by simp⟩
  | a :: b :: l, _ => by
    obtain ⟨c, hc⟩ := prod_coe_withOne (b :: l) (by simp)
    refine ⟨a * c, ?_⟩
    rw [List.map_cons, List.prod_cons, hc, WithOne.coe_mul]

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
  classical
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [pow_zero]; exact Fintype.card_pos_iff.2 ⟨φ 0 0⟩
  have hinj := summary_injective (S := WithOne S) (fun p n => (φ p n : WithOne S)) out m hcorrect
  let P := fun y : Fin m → Bool =>
    (List.ofFn (fun i : Fin (2 * m) => ((φ (i.val + 1)
      (if i.val % 2 = 1 ∧ y ⟨i.val / 2, by omega⟩ = true then i.val else 0) : S) :
        WithOne S))).prod
  have hP : ∀ y, ∃ c : S, P y = c := by
    intro y
    have := prod_coe_withOne (List.ofFn (fun i : Fin (2 * m) => φ (i.val + 1)
      (if i.val % 2 = 1 ∧ y ⟨i.val / 2, by omega⟩ = true then i.val else 0)))
      (by simp; omega)
    simpa [P, List.map_ofFn, Function.comp_def] using this
  let Q : (Fin m → Bool) → S := fun y => (hP y).choose
  have hQ : Function.Injective Q := by
    intro y y' h
    apply hinj
    show P y = P y'
    rw [(hP y).choose_spec, (hP y').choose_spec]
    exact congrArg _ h
  simpa using Fintype.card_le_of_injective Q hQ

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
  have hinj := summary_injective φ out m hcorrect
  have hcard : 2 ^ m ≤ Fintype.card K ^ (d ^ 2) := by
    have := Fintype.card_le_of_injective (β := Fin d → Fin d → K) _ hinj
    simpa [Fintype.card_fun, ← pow_mul, sq] using this
  refine ⟨hcard, ?_⟩
  have hK' : (1 : ℝ) < Fintype.card K := by exact_mod_cast hK
  have hlog : 0 < Real.logb 2 (Fintype.card K) := Real.logb_pos (by norm_num) hK'
  have hm : (m : ℝ) ≤ (d : ℝ) ^ 2 * Real.logb 2 (Fintype.card K) := by
    have hc : ((2 : ℝ) ^ m) ≤ (Fintype.card K : ℝ) ^ (d ^ 2) := by exact_mod_cast hcard
    have := (Real.logb_le_logb (b := 2) (by norm_num) (by positivity) (by positivity)).2 hc
    rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at this
    push_cast at this
    linarith
  calc Real.sqrt (m / Real.logb 2 (Fintype.card K)) ≤ Real.sqrt ((d : ℝ) ^ 2) := by
        apply Real.sqrt_le_sqrt
        rw [div_le_iff₀ hlog]; exact hm
    _ = d := Real.sqrt_sq (by positivity)

end GC.GridCompilers
