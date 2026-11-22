import GC.Computability.SCLadder.Basic
import Mathlib.Algebra.CharP.Two
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Manuscript 008e: few nonlinear gates per path — the affine core

* `triangular_product_identity` (Lemma `lem:product`): for a strictly lower triangular
  `M ∈ 𝔽₂^{n×n}` and `2^s ≥ n`, `(I + M)⁻¹ = ∏_{k<s} (I + M^{2^k})`;
* `region_solve` (Theorem `thm:regions`, algebraic core): the local equations of an affine region,
  `x = M x + N z + c` with `M` strictly lower triangular, have the unique solution
  `x = P z + e` with `P = S N`, `e = S c`, `S = ∏_{k<s} (I + M^{2^k})`;
* `depth_le_of_ref`, `depth_lt_of_barrier` (Lemma `lem:boundary`): the non-affine depth is
  monotone along references and strictly increases at barriers.

Circuit depth bounds, uniformity and the class `FNC` are not formalized.
-/

namespace GC.SCLadder

open Matrix

variable {n : ℕ}

/-- Strictly lower triangular: `M i j = 0` whenever `i ≤ j`. -/
def StrictLower (M : Matrix (Fin n) (Fin n) F) : Prop := ∀ i j, i ≤ j → M i j = 0

lemma StrictLower.pow_apply_eq_zero {M : Matrix (Fin n) (Fin n) F} (hM : StrictLower M) (k : ℕ) :
    ∀ i j : Fin n, (i : ℕ) < j + k → (M ^ k) i j = 0 := by
  induction k with
  | zero =>
    intro i j hij
    simp only [pow_zero]
    exact one_apply_ne (fun h => by subst h; omega)
  | succ k ih =>
    intro i j hij
    rw [pow_succ, mul_apply]
    apply Finset.sum_eq_zero
    intro l _
    by_cases hl : l ≤ j
    · rw [hM l j hl, mul_zero]
    · rw [ih i l (by rw [not_le] at hl; have : (j : ℕ) < l := hl; omega), zero_mul]

/-- A strictly lower triangular `n × n` matrix satisfies `M^k = 0` for `k ≥ n`. -/
lemma StrictLower.pow_eq_zero {M : Matrix (Fin n) (Fin n) F} (hM : StrictLower M) {k : ℕ}
    (hk : n ≤ k) : M ^ k = 0 := by
  ext i j
  exact hM.pow_apply_eq_zero k i j (by have := i.2; omega)

/-- The product `∏_{k<s} (I + M^{2^k})`, in increasing order of `k`. -/
def squaringProduct (M : Matrix (Fin n) (Fin n) F) (s : ℕ) : Matrix (Fin n) (Fin n) F :=
  ((List.range s).map fun k => 1 + M ^ (2 ^ k)).prod

lemma add_self_matrix (A : Matrix (Fin n) (Fin n) F) : A + A = 0 := by
  ext i j
  simp only [Matrix.add_apply, Matrix.zero_apply]
  exact CharTwo.add_self_eq_zero _

/-- Telescoping in characteristic two: `(I + M) ∏_{k<s} (I + M^{2^k}) = I + M^{2^s}`. -/
lemma one_add_mul_squaringProduct (M : Matrix (Fin n) (Fin n) F) (s : ℕ) :
    (1 + M) * squaringProduct M s = 1 + M ^ (2 ^ s) := by
  induction s with
  | zero => simp [squaringProduct]
  | succ s ih =>
    rw [squaringProduct, List.range_succ, List.map_append, List.prod_append, ← squaringProduct,
      ← mul_assoc, ih]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [add_mul, one_mul, mul_add, mul_one, ← pow_add, ← two_mul, ← pow_succ',
      add_assoc, ← add_assoc (M ^ 2 ^ s), add_self_matrix, zero_add]

/-- **Lemma `lem:product` (008e).** For a strictly lower triangular `M ∈ 𝔽₂^{n×n}` and
`2^s ≥ n`, the product `∏_{k<s} (I + M^{2^k})` is a two-sided inverse of `I + M`. -/
theorem triangular_product_identity {M : Matrix (Fin n) (Fin n) F} (hM : StrictLower M) {s : ℕ}
    (hs : n ≤ 2 ^ s) :
    (1 + M) * squaringProduct M s = 1 ∧ squaringProduct M s * (1 + M) = 1 ∧
      (1 + M)⁻¹ = squaringProduct M s := by
  have h1 : (1 + M) * squaringProduct M s = 1 := by
    rw [one_add_mul_squaringProduct, hM.pow_eq_zero hs, add_zero]
  have h2 : squaringProduct M s * (1 + M) = 1 := mul_eq_one_comm.mp h1
  exact ⟨h1, h2, inv_eq_right_inv h1⟩

/-- **Theorem `thm:regions` (008e), algebraic core.** Let the local equations of an affine region be
`x = M x + N z + c` over `𝔽₂`, with `M` strictly lower triangular in the gate order, `z` the values
on the incoming boundary and `2^s ≥ n`. Then `x` satisfies them if and only if
`x = P z + e` with `P = S N`, `e = S c`, `S = ∏_{k<s} (I + M^{2^k})`. In particular the solution
exists and is unique, and is given without enumerating boundary assignments. -/
theorem region_solve {m : ℕ} {M : Matrix (Fin n) (Fin n) F} (hM : StrictLower M) {s : ℕ}
    (hs : n ≤ 2 ^ s) (N : Matrix (Fin n) (Fin m) F) (c : Fin n → F) (z : Fin m → F)
    (x : Fin n → F) :
    x = M *ᵥ x + N *ᵥ z + c ↔
      x = (squaringProduct M s * N) *ᵥ z + squaringProduct M s *ᵥ c := by
  obtain ⟨h1, h2, -⟩ := triangular_product_identity hM hs
  set S := squaringProduct M s
  have hy : (S * N) *ᵥ z + S *ᵥ c = S *ᵥ (N *ᵥ z + c) := by
    rw [mulVec_add, mulVec_mulVec]
  rw [hy]
  have hMM : M *ᵥ x + M *ᵥ x = 0 := by ext i; exact CharTwo.add_self_eq_zero _
  constructor
  · intro hx
    have : (1 + M) *ᵥ x = N *ᵥ z + c := by
      rw [add_mulVec, one_mulVec]
      calc x + M *ᵥ x = (M *ᵥ x + N *ᵥ z + c) + M *ᵥ x := by rw [← hx]
        _ = (M *ᵥ x + M *ᵥ x) + (N *ᵥ z + c) := by abel
        _ = N *ᵥ z + c := by rw [hMM, zero_add]
    rw [← this, mulVec_mulVec, h2, one_mulVec]
  · intro hx
    have h : (1 + M) *ᵥ x = N *ᵥ z + c := by rw [hx, mulVec_mulVec, h1, one_mulVec]
    rw [add_mulVec, one_mulVec] at h
    rw [add_assoc, ← h, add_left_comm, hMM, add_zero]

/-! ## Non-affine depth (Lemma `lem:boundary`) -/

/-- The syntax relevant for the non-affine depth: gates `0, …, L-1` in topological order, each
with a list of references to earlier gates and an affine/barrier label (boundary inputs have depth
`0` and are omitted). -/
structure DepthCircuit (L : ℕ) where
  refs : Fin L → List (Fin L)
  refs_lt : ∀ v, ∀ w ∈ refs v, w < v
  barrier : Fin L → Bool

namespace DepthCircuit

variable {L : ℕ} (K : DepthCircuit L)

/-- The non-affine depth `d(v) = χ(v) + max_i d(p_v(i))`. -/
def depth (v : Fin L) : ℕ :=
  (if K.barrier v then 1 else 0) +
    ((K.refs v).attach.map fun (w : {w // w ∈ K.refs v}) =>
      have : (w.1 : ℕ) < v := K.refs_lt v w.1 w.2
      depth w.1).foldr max 0
termination_by (v : ℕ)

lemma depth_eq (v : Fin L) : K.depth v = (if K.barrier v then 1 else 0) +
    ((K.refs v).attach.map fun w => K.depth w.1).foldr max 0 := by
  rw [depth]

lemma le_foldr_max {l : List ℕ} {a : ℕ} (ha : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp ha with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

lemma depth_ref_le_max {v w : Fin L} (hw : w ∈ K.refs v) :
    K.depth w ≤ ((K.refs v).attach.map fun w => K.depth w.1).foldr max 0 :=
  le_foldr_max (List.mem_map.mpr ⟨⟨w, hw⟩, List.mem_attach _ _, rfl⟩)

/-- **Lemma `lem:boundary` (008e), first part.** The depth is monotone along references. -/
theorem depth_le_of_ref {v w : Fin L} (hw : w ∈ K.refs v) : K.depth w ≤ K.depth v := by
  rw [K.depth_eq v]
  exact le_trans (K.depth_ref_le_max hw) (Nat.le_add_left _ _)

/-- **Lemma `lem:boundary` (008e), second part.** Every reference of a barrier of depth `δ` has
depth at most `δ - 1`. -/
theorem depth_lt_of_barrier {v w : Fin L} (hv : K.barrier v = true) (hw : w ∈ K.refs v) :
    K.depth w + 1 ≤ K.depth v := by
  rw [K.depth_eq v]
  simp only [hv, ↓reduceIte]
  have := K.depth_ref_le_max hw
  omega

/-- The depth of an affine gate is the maximum depth of its references. -/
theorem depth_affine {v : Fin L} (hv : K.barrier v = false) :
    K.depth v = ((K.refs v).attach.map fun w => K.depth w.1).foldr max 0 := by
  rw [K.depth_eq v, hv]
  simp

end DepthCircuit

end GC.SCLadder
