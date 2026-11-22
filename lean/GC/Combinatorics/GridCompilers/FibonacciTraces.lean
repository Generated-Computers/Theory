import GC.Combinatorics.GridCompilers.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Sequential NOR has exactly Fibonacci-many traces (manuscript 009d)

* `census_mem_iff` (Theorem 2.1, characterization): a word `(x_0, …, x_N)` is a trace iff
  `x_0 = 1`, `x_1 = 0` and no two adjacent ones.
* `census_card` (Theorem 2.1, count): there are exactly `F_{N+1}` traces.
* `fibre_eq_piFinset`, `card_A`, `sum_prod_card_A` (Theorem 2.2): the fibre of a trace is the
  product `∏ A_i(x)`, the factor sizes, and `∑_x ∏_i c_i(x) = N!`.
* `causal_projection` (Lemma 3.1) and `card_le_two_pow_card_D_inter_DTr`, `card_le_fib`
  (Corollary 3.2).
* `deterministic_capacity_le`, `deterministic_capacity_attained` (Theorem 4.2, deterministic
  case `δ = 0`, `B = L`).
-/

namespace GC.GridCompilers

variable {N : ℕ}

/-! ### Basic facts about the trace -/

theorem traceAux_zero (j : ParentArray N) : traceAux j 0 = true := by
  rw [traceAux]

theorem traceAux_succ (j : ParentArray N) (k : ℕ) (h : k < N) :
    traceAux j (k + 1) = nor (traceAux j k) (traceAux j (j ⟨k, h⟩).val) := by
  rw [traceAux]; simp [h]

/-- The coordinate of the parent of position `i + 1`, as an index of the trace. -/
def parentIdx (j : ParentArray N) (i : Fin N) : Fin (N + 1) := ⟨(j i).val, by omega⟩

theorem trace_zero (j : ParentArray N) : trace j 0 = true := traceAux_zero j

theorem trace_succ (j : ParentArray N) (i : Fin N) :
    trace j i.succ = nor (trace j i.castSucc) (trace j (parentIdx j i)) := by
  simp only [trace, Fin.val_succ, Fin.val_castSucc, parentIdx]
  exact traceAux_succ j i.val i.isLt

/-! ### The census -/

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

theorem card_fibWords : ∀ n, (fibWords n).card = Nat.fib (n + 2)
  | 0 => by simp [fibWords]
  | 1 => by simp [fibWords]; rfl
  | n + 2 => by
    rw [fibWords, Finset.card_union_of_disjoint, Finset.card_image_of_injective,
      Finset.card_image_of_injective, card_fibWords (n + 1), card_fibWords n,
      Nat.fib_add_two (n := n + 2), add_comm]
    · intro a b hab
      exact Fin.cons_right_injective _ (Fin.cons_right_injective _ hab)
    · exact Fin.cons_right_injective _
    · rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [Finset.mem_image] at hx hx'
      obtain ⟨a, -, rfl⟩ := hx
      obtain ⟨b, -, hb⟩ := hx'
      have := congrFun hb 0
      simp at this

theorem mem_fibWords_iff : ∀ (n : ℕ) (x : Fin n → Bool), x ∈ fibWords n ↔ NoAdj x
  | 0, x => by
    simp only [fibWords, Finset.mem_univ, true_iff]; intro i h; omega
  | 1, x => by
    simp only [fibWords, Finset.mem_univ, true_iff]; intro i h; omega
  | n + 2, x => by
    rw [fibWords, Finset.mem_union, Finset.mem_image, Finset.mem_image]
    constructor
    · rintro (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
      · rw [mem_fibWords_iff] at hy
        intro i h
        cases i with
        | zero => simp
        | succ i =>
          have := hy i (by omega)
          simpa [Fin.cons] using this
      · rw [mem_fibWords_iff] at hy
        intro i h
        match i, h with
        | 0, _ => simp
        | 1, _ => simp
        | i + 2, h =>
          have := hy i (by omega)
          simpa [Fin.cons] using this
    · intro hx
      cases h0 : x 0 with
      | false =>
        left
        refine ⟨Fin.tail x, ?_, ?_⟩
        · rw [mem_fibWords_iff]
          intro i h
          exact hx (i + 1) (by omega)
        · rw [← h0]; exact Fin.cons_self_tail x
      | true =>
        right
        have h1 : x 1 = false := by
          have := hx 0 (by omega)
          cases h : x 1 <;> simp_all
        refine ⟨Fin.tail (Fin.tail x), ?_, ?_⟩
        · rw [mem_fibWords_iff]
          intro i h
          exact hx (i + 2) (by omega)
        · rw [← h0]
          conv_rhs => rw [← Fin.cons_self_tail x]
          congr 1
          rw [← Fin.cons_self_tail (Fin.tail x)]
          congr 1
          rw [← h1]; rfl

/-- A word satisfying `x_0 = 1` and all the Sequential NOR equations of `j` is its trace. -/
theorem trace_eq_of_equations (j : ParentArray N) (x : Fin (N + 1) → Bool) (hx0 : x 0 = true)
    (h : ∀ i : Fin N, nor (x i.castSucc) (x (parentIdx j i)) = x i.succ) : trace j = x := by
  have key : ∀ k (hk : k < N + 1), traceAux j k = x ⟨k, hk⟩ := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      cases k with
      | zero => rw [traceAux_zero]; exact hx0.symm
      | succ k =>
        have hp := (j ⟨k, by omega⟩).isLt
        rw [traceAux_succ _ k (by omega), ih k (by omega) (by omega),
          ih _ (by omega) (by omega)]
        exact h ⟨k, by omega⟩
  funext i
  exact key i.val i.isLt

/-- Necessity in the census: every trace is a census word. -/
theorem isCensusWord_trace (j : ParentArray N) : IsCensusWord (trace j) := by
  refine ⟨trace_zero j, fun h => ?_, fun i hi => ?_⟩
  · have e : (⟨1, by omega⟩ : Fin (N + 1)) = Fin.succ (⟨0, by omega⟩ : Fin N) := rfl
    have hp : parentIdx j ⟨0, by omega⟩ = 0 :=
      Fin.ext (Nat.lt_one_iff.mp (j ⟨0, by omega⟩).isLt)
    rw [e, trace_succ, hp]
    simp [trace_zero, nor]
  · obtain ⟨h1, h2⟩ := hi
    rw [trace_succ, h1] at h2
    simp [nor] at h2

/-- The canonical parent array of a census word: parent `1` where the word has a one,
parent `0` elsewhere. -/
def censusArray (x : Fin (N + 1) → Bool) : ParentArray N := fun i =>
  if x i.succ then ⟨min 1 i.val, by omega⟩ else ⟨0, by omega⟩

/-- Sufficiency in the census: every census word is the trace of `censusArray x`. -/
theorem trace_censusArray (x : Fin (N + 1) → Bool) (hx : IsCensusWord x) :
    trace (censusArray x) = x := by
  obtain ⟨h0, h1, hadj⟩ := hx
  apply trace_eq_of_equations _ _ h0
  intro i
  by_cases hs : x i.succ = true
  · have hi : 1 ≤ i.val := by
      by_contra hcon
      have : i.succ = ⟨1, by omega⟩ := by ext; simp; omega
      rw [this, h1 (by omega)] at hs
      exact Bool.false_ne_true hs
    have hc : x i.castSucc = false := by
      cases hcs : x i.castSucc
      · rfl
      · exact absurd ⟨hcs, hs⟩ (hadj i)
    have hp : parentIdx (censusArray x) i = ⟨1, by omega⟩ := by
      ext; simp [parentIdx, censusArray, hs]; omega
    rw [hp, hc, h1 (by omega), hs]; rfl
  · have hs' : x i.succ = false := by simpa using hs
    have hp : parentIdx (censusArray x) i = 0 := by
      ext; simp [parentIdx, censusArray, hs']
    rw [hp, h0, hs']; simp [nor]

/-- **Census, characterization** (009d, Theorem 2.1). A word `(x_0, …, x_N)` is the trace of
a legal parent array of length `N` iff `x_0 = 1`, `x_1 = 0` and `x_{i-1} x_i = 0` for all `i`. -/
theorem census_mem_iff (x : Fin (N + 1) → Bool) : x ∈ traceSet N ↔ IsCensusWord x := by
  constructor
  · intro hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hx
    exact isCensusWord_trace j
  · intro hx
    exact Finset.mem_image.2 ⟨censusArray x, Finset.mem_univ _, trace_censusArray x hx⟩

/-- Census words of length `M + 2` are `1 0 y` with `y` a word without adjacent ones. -/
theorem traceSet_succ_eq (M : ℕ) :
    traceSet (M + 1) = (fibWords M).image
      (fun y => Fin.cons (α := fun _ => Bool) true (Fin.cons (α := fun _ => Bool) false y)) := by
  ext x
  rw [census_mem_iff, Finset.mem_image]
  constructor
  · rintro ⟨h0, h1, hadj⟩
    refine ⟨Fin.tail (Fin.tail x), ?_, ?_⟩
    · rw [mem_fibWords_iff]
      intro i h hc
      exact hadj ⟨i + 2, by omega⟩ hc
    · rw [← h0]
      conv_rhs => rw [← Fin.cons_self_tail x]
      congr 1
      rw [← Fin.cons_self_tail (Fin.tail x)]
      congr 1
      rw [← h1 (by omega)]; rfl
  · rintro ⟨y, hy, rfl⟩
    rw [mem_fibWords_iff] at hy
    refine ⟨rfl, fun _ => rfl, ?_⟩
    rintro ⟨i, hi⟩
    match i, hi with
    | 0, _ => simp
    | 1, _ => rintro ⟨h, -⟩; exact Bool.false_ne_true h
    | i + 2, hi =>
      have := hy i (by omega)
      simpa [Fin.cons] using this

/-- **Census, count** (009d, Theorem 2.1). The set of Sequential NOR traces of length `N`, over
all legal parent arrays, has exactly `F_{N+1}` elements (with `F_1 = F_2 = 1`). -/
theorem census_card (N : ℕ) : (traceSet N).card = Nat.fib (N + 1) := by
  cases N with
  | zero =>
    show (traceSet 0).card = 1
    rw [Finset.card_eq_one]
    refine ⟨fun _ => true, ?_⟩
    ext x
    rw [census_mem_iff, Finset.mem_singleton]
    constructor
    · rintro ⟨h0, -, -⟩
      funext i
      rw [Fin.fin_one_eq_zero i, h0]
    · rintro rfl
      exact ⟨rfl, fun h => absurd h (by omega), fun i => i.elim0⟩
  | succ M =>
    rw [traceSet_succ_eq, Finset.card_image_of_injective, card_fibWords]
    intro a b hab
    exact Fin.cons_right_injective _ (Fin.cons_right_injective _ hab)

/-! ### Fibres -/

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
  ext j
  simp only [fibre, Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, A]
  constructor
  · rintro rfl i
    rw [trace_succ]; rfl
  · intro h
    exact trace_eq_of_equations j x hx0 h

/-- **Fibres** (009d, Theorem 2.2, factor sizes). For a trace `x`, `c_i(x) = |A_i(x)|` is the
number of available parents if `x_{i-1} = 1`, the number of earlier zeros if
`x_{i-1} = 0, x_i = 1`, and the number of earlier ones if `x_{i-1} = 0, x_i = 0`. -/
theorem card_A (x : Fin (N + 1) → Bool) (hx : x ∈ traceSet N) (i : Fin N) :
    (A x i).card =
      if x i.castSucc then i.val + 1
      else if x i.succ then
        (Finset.univ.filter (fun t : Fin (i.val + 1) => x ⟨t.val, by omega⟩ = false)).card
      else (Finset.univ.filter (fun t : Fin (i.val + 1) => x ⟨t.val, by omega⟩ = true)).card := by
  obtain ⟨-, -, hadj⟩ := (census_mem_iff x).1 hx
  unfold A
  split_ifs with h1 h2
  · have h2 : x i.succ = false := by
      cases h : x i.succ
      · rfl
      · exact absurd ⟨h1, h⟩ (hadj i)
    rw [Finset.filter_true_of_mem, Finset.card_univ, Fintype.card_fin]
    intro p _
    rw [h1, h2]; rfl
  · congr 1
    apply Finset.filter_congr
    intro p _
    have h1' : x i.castSucc = false := by simpa using h1
    rw [h1', h2]
    cases x ⟨p.val, by omega⟩ <;> simp [nor]
  · congr 1
    apply Finset.filter_congr
    intro p _
    have h1' : x i.castSucc = false := by simpa using h1
    have h2' : x i.succ = false := by simpa using h2
    rw [h1', h2']
    cases x ⟨p.val, by omega⟩ <;> simp [nor]

/-- Every factor of a trace is nonempty. -/
theorem one_le_card_A (x : Fin (N + 1) → Bool) (hx : x ∈ traceSet N) (i : Fin N) :
    1 ≤ (A x i).card := by
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hx
  have : j ∈ fibre (trace j) := by simp [fibre]
  rw [fibre_eq_piFinset _ (trace_zero j), Fintype.mem_piFinset] at this
  exact Finset.card_pos.2 ⟨_, this i⟩

/-- The number of legal parent arrays of length `N` is `N!`. -/
theorem card_parentArray (N : ℕ) : Fintype.card (ParentArray N) = N.factorial := by
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin]
  rw [Fin.prod_univ_eq_prod_range (fun i => i + 1), Finset.prod_range_add_one_eq_factorial]

/-- **Fibres** (009d, Theorem 2.2, last identity): `∑_x ∏_i c_i(x) = N!`. -/
theorem sum_prod_card_A (N : ℕ) :
    ∑ x ∈ traceSet N, ∏ i : Fin N, (A x i).card = N.factorial := by
  rw [← card_parentArray, ← Finset.card_univ,
    Finset.card_eq_sum_card_image trace Finset.univ]
  apply Finset.sum_congr rfl
  intro x hx
  have hx0 : x 0 = true := ((census_mem_iff x).1 hx).1
  rw [← Fintype.card_piFinset, ← fibre_eq_piFinset x hx0]
  rfl

/-! ### Causal projection -/

/-- **Causal projection** (009d, Lemma 3.1). If two legal arrays agree outside a set `D` of
coordinates and their traces agree on `D`, the traces are equal. -/
theorem causal_projection (j j' : ParentArray N) (D : Set (Fin N))
    (hD : ∀ i, i ∉ D → (j i).val = (j' i).val)
    (hT : ∀ i ∈ D, trace j i.succ = trace j' i.succ) : trace j = trace j' := by
  have key : ∀ k (hk : k < N + 1), traceAux j k = traceAux j' k := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      cases k with
      | zero => rw [traceAux_zero, traceAux_zero]
      | succ k =>
        by_cases hk' : (⟨k, by omega⟩ : Fin N) ∈ D
        · exact hT _ hk'
        · have hp := (j ⟨k, by omega⟩).isLt
          rw [traceAux_succ _ k (by omega), traceAux_succ _ k (by omega), ih k (by omega) (by omega),
            ← hD _ hk', ih _ (by omega) (by omega)]
  funext i
  exact key i.val i.isLt

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

omit [Fintype α] in
theorem trace_inj_of_recover (E : α → ParentArray N) (R : (Fin (N + 1) → Bool) → α)
    (hR : ∀ a, R (trace (E a)) = a) : Function.Injective (fun a => trace (E a)) := by
  intro a a' h
  rw [← hR a, ← hR a']
  exact congrArg R h

/-- **Corollary 3.2**, first inequality: the traces of a decodable encoding are determined by
their restriction to `D ∩ D_Tr`, so `|𝓜| ≤ 2^{|D ∩ D_Tr|}`. -/
theorem card_le_two_pow_card_D_inter_DTr (E : α → ParentArray N)
    (R : (Fin (N + 1) → Bool) → α) (hR : ∀ a, R (trace (E a)) = a) :
    Fintype.card α ≤ 2 ^ (varSet E ∩ traceVarSet E).card := by
  classical
  let S := varSet E ∩ traceVarSet E
  let Φ : α → (S → Bool) := fun a i => trace (E a) (i.val).succ
  have hinj : Function.Injective Φ := by
    intro a a' h
    apply trace_inj_of_recover E R hR
    apply causal_projection (E a) (E a') (varSet E)
    · intro i hi
      simp only [Finset.mem_coe, varSet, Finset.mem_filter, Finset.mem_univ, true_and,
        not_exists, not_not] at hi
      rw [hi a a']
    · intro i hi
      by_cases hi' : i ∈ traceVarSet E
      · have hiS : i ∈ S := Finset.mem_inter.2 ⟨hi, hi'⟩
        exact congrFun h ⟨i, hiS⟩
      · simp only [traceVarSet, Finset.mem_filter, Finset.mem_univ, true_and, not_exists,
          not_not] at hi'
        exact hi' a a'
  have := Fintype.card_le_of_injective Φ hinj
  simpa [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe] using this

/-- **Corollary 3.2**, second inequality: `|𝓜| ≤ ∏_{i ∈ D} k_i` with `k_i = |{E(a)_i}|`. -/
theorem card_le_prod_varSet (E : α → ParentArray N)
    (R : (Fin (N + 1) → Bool) → α) (hR : ∀ a, R (trace (E a)) = a) :
    Fintype.card α ≤
      ∏ i ∈ varSet E, (Finset.univ.image (fun a => E a i)).card := by
  classical
  let D := varSet E
  let Φ : α → ((i : D) → (Finset.univ.image (fun a => E a i.val) : Finset _)) :=
    fun a i => ⟨E a i.val, Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩⟩
  have hinj : Function.Injective Φ := by
    intro a a' h
    have hE : E a = E a' := by
      funext i
      by_cases hi : i ∈ D
      · have := congrFun h ⟨i, hi⟩
        simpa [Φ] using congrArg Subtype.val this
      · simp only [D, varSet, Finset.mem_filter, Finset.mem_univ, true_and, not_exists,
          not_not] at hi
        exact hi a a'
    exact trace_inj_of_recover E R hR (by simp [hE])
  have h2 := Fintype.card_le_of_injective Φ hinj
  rw [Fintype.card_pi] at h2
  simp only [Fintype.card_coe] at h2
  rwa [Finset.prod_coe_sort D (fun i => (Finset.univ.image (fun a => E a i)).card)] at h2

/-- **Corollary 3.2**, third inequality: a decodable encoding at length `N` has at most
`F_{N+1}` messages. -/
theorem card_le_fib (E : α → ParentArray N) (R : (Fin (N + 1) → Bool) → α)
    (hR : ∀ a, R (trace (E a)) = a) : Fintype.card α ≤ Nat.fib (N + 1) := by
  classical
  rw [← census_card N, ← Finset.card_univ,
    ← Finset.card_image_of_injective _ (trace_inj_of_recover E R hR)]
  apply Finset.card_le_card
  intro x hx
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hx
  exact Finset.mem_image.2 ⟨E a, Finset.mem_univ _, rfl⟩

/-- **Capacity, deterministic case** (009d, Theorem 4.2 with `δ = 0`): if a trace-only decoder
outputs lists of at most `L` messages and always lists the encoded message, then there are at
most `L · F_{N+1}` messages. -/
theorem deterministic_capacity_le (E : α → ParentArray N)
    (R : (Fin (N + 1) → Bool) → Finset α) (L : ℕ) (hR : ∀ x, (R x).card ≤ L)
    (hdec : ∀ a, a ∈ R (trace (E a))) : Fintype.card α ≤ L * Nat.fib (N + 1) := by
  classical
  rw [← Finset.card_univ, Finset.card_eq_sum_card_image (fun a => trace (E a)) Finset.univ]
  calc ∑ x ∈ Finset.univ.image (fun a => trace (E a)),
        (Finset.univ.filter (fun a => trace (E a) = x)).card
      ≤ ∑ _x ∈ Finset.univ.image (fun a => trace (E a)), L := by
        apply Finset.sum_le_sum
        intro x _
        refine le_trans (Finset.card_le_card ?_) (hR x)
        intro a ha
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
        rw [← ha]; exact hdec a
    _ = (Finset.univ.image (fun a => trace (E a))).card * L := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (traceSet N).card * L := by
        apply Nat.mul_le_mul_right
        apply Finset.card_le_card
        intro x hx
        obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hx
        exact Finset.mem_image.2 ⟨E a, Finset.mem_univ _, rfl⟩
    _ = L * Nat.fib (N + 1) := by rw [census_card, mul_comm]

end Encodings

/-- **Capacity, deterministic case, attainment** (009d, Theorem 4.2 with `δ = 0`): there is an
encoding of exactly `L · F_{N+1}` messages with a trace-only decoder that outputs lists of at
most `L` messages and always lists the encoded message. -/
theorem deterministic_capacity_attained (N L : ℕ) :
    ∃ (α : Type) (_ : Fintype α) (E : α → ParentArray N)
      (R : (Fin (N + 1) → Bool) → Finset α),
      Fintype.card α = L * Nat.fib (N + 1) ∧ (∀ x, (R x).card ≤ L) ∧
        ∀ a, a ∈ R (trace (E a)) := by
  classical
  refine ⟨(traceSet N) × Fin L, inferInstance, fun a => censusArray a.1.val,
    fun x => Finset.univ.filter (fun a => a.1.val = x), ?_, ?_, ?_⟩
  · rw [Fintype.card_prod, Fintype.card_coe, census_card, Fintype.card_fin, mul_comm]
  · intro x
    calc (Finset.univ.filter (fun a : (traceSet N) × Fin L => a.1.val = x)).card
        ≤ (Finset.univ : Finset (Fin L)).card := by
          apply Finset.card_le_card_of_injOn Prod.snd (fun _ _ => Finset.mem_coe.2
            (Finset.mem_univ _))
          intro a ha b hb hab
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha hb
          exact Prod.ext (Subtype.ext (ha.trans hb.symm)) hab
      _ = L := by simp
  · rintro ⟨⟨x, hx⟩, l⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (trace_censusArray x ((census_mem_iff x).1 hx)).symm

/-- Traces of lengths `1, …, M` number `∑_{n=1}^M F_{n+1} = F_{M+3} - 2` (used in Theorem 4.2
for messages of different lengths). -/
theorem sum_census_card (M : ℕ) :
    ∑ n ∈ Finset.Icc 1 M, (traceSet n).card + 2 = Nat.fib (M + 3) := by
  induction M with
  | zero => simp; rfl
  | succ M ih =>
    rw [Finset.sum_Icc_succ_top (by omega), census_card, add_right_comm, ih,
      Nat.fib_add_two (n := M + 2)]
    ring_nf

end GC.GridCompilers
