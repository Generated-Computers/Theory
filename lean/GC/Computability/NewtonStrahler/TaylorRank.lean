import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Tactic.LinearCombination

/-!
# Gates of higher degree: the Taylor rank

Section 6 of "Newton's Method Evaluates Circuits in Strahler-Rank Rounds": a triangular Boolean
system over `GF(2)` with arbitrary gate functions, the exact multilinear Taylor identity, the
exact error identity `J(x) e⁺ = R(x, e)`, and the Taylor-rank Newton contraction.
-/

namespace GC.NewtonStrahler

open Matrix

variable {n : ℕ}

/-- A triangular Boolean system over `GF(2)` (Section 6): gate `i` has a set of parents
`P_i ⊆ [i-1]` and a gate function `f_i` that depends only on the coordinates in `P_i`. -/
structure BoolSystem (n : ℕ) where
  par : Fin n → Finset (Fin n)
  fn : Fin n → (Fin n → ZMod 2) → ZMod 2
  par_lt : ∀ i, ∀ j ∈ par i, j < i
  fn_dep : ∀ i (x y : Fin n → ZMod 2), (∀ j ∈ par i, x j = y j) → fn i x = fn i y

/-- The point obtained from `x` by setting the coordinates in `S` to the indicator of `T`. -/
def setOn (S T : Finset (Fin n)) (x : Fin n → ZMod 2) : Fin n → ZMod 2 :=
  fun j => if j ∈ S then (if j ∈ T then 1 else 0) else x j

/-- The multilinear derivative `∂_S g` over `GF(2)`, evaluated at `x`:
`∂_S g(x) = ∑_{T ⊆ S} g(x with x_S := 1_T)`. For the multilinear (algebraic normal form)
representation of `g` this is the formal derivative `∏_{j ∈ S} ∂/∂x_j` applied to it. -/
def mderiv (S : Finset (Fin n)) (g : (Fin n → ZMod 2) → ZMod 2) (x : Fin n → ZMod 2) :
    ZMod 2 :=
  ∑ T ∈ S.powerset, g (setOn S T x)

namespace BoolSystem

/-- `xs` is the value vector: `xs_i = f_i(xs)` for all `i`. -/
def IsValue (B : BoolSystem n) (xs : Fin n → ZMod 2) : Prop := ∀ i, xs i = B.fn i xs

/-- The residual `F_i(x) = x_i + f_i(x)`. -/
def residual (B : BoolSystem n) (x : Fin n → ZMod 2) : Fin n → ZMod 2 :=
  fun i => x i + B.fn i x

/-- The Jacobian `J(x)_{ij} = [i = j] + ∂_{j} f_i(x)`. -/
def jacobian (B : BoolSystem n) (x : Fin n → ZMod 2) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  fun i j => (if i = j then 1 else 0) + mderiv {j} (B.fn i) x

/-- The Newton map `N(x) = x + J(x)⁻¹ F(x)`. -/
noncomputable def newton (B : BoolSystem n) (x : Fin n → ZMod 2) : Fin n → ZMod 2 :=
  x + (jacobian B x)⁻¹ *ᵥ residual B x

/-- The Taylor remainder `R_i(x,e) = ∑_{S ⊆ P_i, |S| ≥ 2} (∂_S f_i)(x) e_S`. -/
def remainder (B : BoolSystem n) (x e : Fin n → ZMod 2) : Fin n → ZMod 2 :=
  fun i => ∑ S ∈ (B.par i).powerset.filter (fun S => 2 ≤ S.card),
    mderiv S (B.fn i) x * ∏ j ∈ S, e j

open Classical in
/-- `𝓗_i = {S ⊆ P_i : |S| ≥ 2, ∂_S f_i ≢ 0}`. -/
noncomputable def hset (B : BoolSystem n) (i : Fin n) : Finset (Finset (Fin n)) :=
  (B.par i).powerset.filter (fun S => 2 ≤ S.card ∧ mderiv S (B.fn i) ≠ 0)

lemma subset_of_mem_hset {B : BoolSystem n} {i : Fin n} {S : Finset (Fin n)}
    (h : S ∈ hset B i) : S ⊆ B.par i := by
  classical
  unfold hset at h
  exact Finset.mem_powerset.mp (Finset.mem_filter.mp h).1

lemma nonempty_of_mem_hset {B : BoolSystem n} {i : Fin n} {S : Finset (Fin n)}
    (h : S ∈ hset B i) : S.Nonempty := by
  classical
  unfold hset at h
  have := (Finset.mem_filter.mp h).2.1
  exact Finset.card_pos.mp (by omega)

/-- The Taylor rank (Definition 6.3, with the correction for gates without nonlinear terms):
`ρ_T(i) = max (max_{j ∈ P_i} ρ_T(j)) (max_{S ∈ 𝓗_i} (1 + min_{j ∈ S} ρ_T(j)))`, where an empty
maximum is `0`. -/
noncomputable def taylorRank (B : BoolSystem n) (i : Fin n) : ℕ :=
  max ((B.par i).attach.sup fun j => taylorRank B j.1)
    ((hset B i).attach.sup fun S =>
      1 + S.1.attach.inf' (Finset.attach_nonempty_iff.mpr (nonempty_of_mem_hset S.2))
        fun j => taylorRank B j.1)
termination_by i.val
decreasing_by
  · exact B.par_lt i _ j.2
  · exact B.par_lt i _ (subset_of_mem_hset S.2 j.2)

/-- `ρ_T(C) = max_i ρ_T(i)`. -/
noncomputable def systemTaylorRank (B : BoolSystem n) : ℕ := Finset.univ.sup (taylorRank B)

end BoolSystem

/-! ### The multilinear Taylor identity -/

/-- The derivative in direction `a`: `g(y with y_a := 1) + g(y with y_a := 0)`. -/
def dirDeriv (a : Fin n) (g : (Fin n → ZMod 2) → ZMod 2) : (Fin n → ZMod 2) → ZMod 2 :=
  fun y => g (Function.update y a 1) + g (Function.update y a 0)

lemma mderiv_empty (g : (Fin n → ZMod 2) → ZMod 2) (x : Fin n → ZMod 2) :
    mderiv ∅ g x = g x := by
  have : setOn ∅ ∅ x = x := by funext j; simp [setOn]
  simp [mderiv, this]

lemma mderiv_insert {a : Fin n} {S : Finset (Fin n)} (ha : a ∉ S)
    (g : (Fin n → ZMod 2) → ZMod 2) (x : Fin n → ZMod 2) :
    mderiv (insert a S) g x = mderiv S (dirDeriv a g) x := by
  unfold mderiv
  rw [Finset.sum_powerset_insert ha, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun T hT => ?_
  have haT : a ∉ T := fun h => ha (Finset.mem_powerset.mp hT h)
  have h1 : setOn (insert a S) T x = Function.update (setOn S T x) a 0 := by
    funext j
    by_cases hj : j = a
    · subst hj; simp [setOn, haT]
    · simp [setOn, hj]
  have h2 : setOn (insert a S) (insert a T) x = Function.update (setOn S T x) a 1 := by
    funext j
    by_cases hj : j = a
    · subst hj; simp [setOn]
    · simp [setOn, hj]
  rw [h1, h2, dirDeriv, add_comm]

lemma zmod2_cases (v : ZMod 2) : v = 0 ∨ v = 1 := by
  revert v; decide

/-- **Lemma 6.1 (exact multilinear Taylor identity)**, for increments supported on `W`:
`g(x + e) = ∑_{S ⊆ W} (∂_S g)(x) e_S`. -/
theorem taylor_identity (W : Finset (Fin n)) :
    ∀ (g : (Fin n → ZMod 2) → ZMod 2) (x e : Fin n → ZMod 2), (∀ j ∉ W, e j = 0) →
      g (x + e) = ∑ S ∈ W.powerset, mderiv S g x * ∏ j ∈ S, e j := by
  induction W using Finset.induction_on with
  | empty =>
    intro g x e he
    have : e = 0 := funext fun j => he j (Finset.notMem_empty j)
    simp [this, mderiv_empty]
  | insert a W ha ih =>
    intro g x e he
    rw [Finset.sum_powerset_insert ha]
    set e' := Function.update e a 0 with he'def
    have he' : ∀ j ∉ W, e' j = 0 := by
      intro j hj
      by_cases hja : j = a
      · subst hja; simp [e']
      · simp only [e', Function.update_of_ne hja]
        exact he j (by simp [hja, hj])
    have hprod : ∀ S ∈ W.powerset, ∏ j ∈ S, e' j = ∏ j ∈ S, e j := fun S hS =>
      Finset.prod_congr rfl fun j hj => by
        have : j ≠ a := fun h => ha (h ▸ Finset.mem_powerset.mp hS hj)
        simp [e', Function.update_of_ne this]
    have hs1 : ∑ S ∈ W.powerset, mderiv S g x * ∏ j ∈ S, e j = g (x + e') := by
      rw [ih g x e' he']
      exact Finset.sum_congr rfl fun S hS => by rw [hprod S hS]
    have hs2 : ∑ S ∈ W.powerset, mderiv (insert a S) g x * ∏ j ∈ insert a S, e j =
        e a * dirDeriv a g (x + e') := by
      rw [ih (dirDeriv a g) x e' he', Finset.mul_sum]
      refine Finset.sum_congr rfl fun S hS => ?_
      have haS : a ∉ S := fun h => ha (Finset.mem_powerset.mp hS h)
      rw [mderiv_insert haS, Finset.prod_insert haS, hprod S hS]
      ring
    rw [hs1, hs2]
    have hya : (x + e') a = x a := by simp [e']
    have hxe : x + e = Function.update (x + e') a (x a + e a) := by
      funext j
      by_cases hja : j = a
      · subst hja; simp
      · simp [Function.update_of_ne hja, e']
    have hy : g (x + e') = g (Function.update (x + e') a (x a)) := by
      rw [← hya, Function.update_eq_self]
    rw [hxe, hy, dirDeriv]
    generalize x a = u
    generalize e a = v
    have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    rcases zmod2_cases u with rfl | rfl <;> rcases zmod2_cases v with rfl | rfl <;>
      simp only [zero_add, add_zero, h11, one_mul, zero_mul] <;>
      generalize g (Function.update (x + e') a 1) = A <;>
      generalize g (Function.update (x + e') a 0) = A' <;>
      revert A A' <;> decide

namespace BoolSystem

/-- The Taylor identity at a gate, summed over subsets of its parents. -/
lemma fn_taylor (B : BoolSystem n) (i : Fin n) (x e : Fin n → ZMod 2) :
    B.fn i (x + e) = ∑ S ∈ (B.par i).powerset, mderiv S (B.fn i) x * ∏ j ∈ S, e j := by
  classical
  set e'' : Fin n → ZMod 2 := fun j => if j ∈ B.par i then e j else 0
  have h1 : B.fn i (x + e) = B.fn i (x + e'') :=
    B.fn_dep i _ _ fun j hj => by simp [e'', hj]
  rw [h1, taylor_identity (B.par i) (B.fn i) x e'' (fun j hj => by simp [e'', hj])]
  refine Finset.sum_congr rfl fun S hS => ?_
  congr 1
  exact Finset.prod_congr rfl fun j hj => by simp [e'', Finset.mem_powerset.mp hS hj]

lemma sum_powerset_split (P : Finset (Fin n)) (c : Finset (Fin n) → ZMod 2) :
    ∑ S ∈ P.powerset, c S =
      c ∅ + ∑ j ∈ P, c {j} + ∑ S ∈ P.powerset.filter (fun S => 2 ≤ S.card), c S := by
  rw [← Finset.sum_filter_add_sum_filter_not P.powerset (fun S => 2 ≤ S.card), add_comm]
  congr 1
  have hset : P.powerset.filter (fun S => ¬ 2 ≤ S.card) = insert ∅ (P.image fun j => {j}) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_insert, Finset.mem_image]
    constructor
    · rintro ⟨hSP, hcard⟩
      rcases Nat.lt_or_ge S.card 1 with h0 | h1
      · left; exact Finset.card_eq_zero.mp (show S.card = 0 by omega)
      · right
        obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp (show S.card = 1 by omega)
        exact ⟨j, hSP (Finset.mem_singleton_self j), rfl⟩
    · rintro (rfl | ⟨j, hj, rfl⟩)
      · simp
      · simp [hj]
  rw [hset, Finset.sum_insert, Finset.sum_image]
  · intro a _ b _ h; exact Finset.singleton_injective h
  · simp

lemma mderiv_single_eq (g : (Fin n → ZMod 2) → ZMod 2) (j : Fin n) (x : Fin n → ZMod 2) :
    mderiv {j} g x = g (Function.update x j 1) + g (Function.update x j 0) := by
  have h := Finset.sum_powerset_insert (Finset.notMem_empty j) (fun T => g (setOn {j} T x))
  simp only [Finset.insert_empty, Finset.powerset_empty, Finset.sum_singleton] at h
  unfold mderiv
  rw [h, add_comm]
  congr 2 <;> funext k <;> by_cases hk : k = j <;> simp [setOn, hk]

lemma mderiv_single_eq_zero (B : BoolSystem n) {i j : Fin n} (hj : j ∉ B.par i)
    (x : Fin n → ZMod 2) : mderiv {j} (B.fn i) x = 0 := by
  rw [mderiv_single_eq, B.fn_dep i (Function.update x j 1) (Function.update x j 0) fun k hk => by
    have : k ≠ j := fun h => hj (h ▸ hk)
    simp [Function.update_of_ne this]]
  exact CharTwo.add_self_eq_zero _

lemma jacobian_isLowerTriangular (B : BoolSystem n) (x : Fin n → ZMod 2) :
    (jacobian B x).IsLowerTriangular := by
  intro i j hij
  have hij' : i < j := hij
  have hne : i ≠ j := ne_of_lt hij'
  have : j ∉ B.par i := fun h => absurd (B.par_lt i j h) (not_lt.mpr hij'.le)
  simp [jacobian, hne, mderiv_single_eq_zero B this]

lemma jacobian_diag (B : BoolSystem n) (x : Fin n → ZMod 2) (i : Fin n) :
    jacobian B x i i = 1 := by
  have : i ∉ B.par i := fun h => lt_irrefl _ (B.par_lt i i h)
  simp [jacobian, mderiv_single_eq_zero B this]

/-- `J(x)` is unit lower triangular, so `det J(x) = 1`. -/
theorem det_jacobian (B : BoolSystem n) (x : Fin n → ZMod 2) : (jacobian B x).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ (jacobian_isLowerTriangular B x)]
  simp [jacobian_diag]

lemma jacobian_mulVec_inv (B : BoolSystem n) (x v : Fin n → ZMod 2) :
    jacobian B x *ᵥ ((jacobian B x)⁻¹ *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (by simp [det_jacobian]),
    Matrix.one_mulVec]

lemma jacobian_mulVec_apply (B : BoolSystem n) (x v : Fin n → ZMod 2) (i : Fin n) :
    (jacobian B x *ᵥ v) i = v i + ∑ j ∈ B.par i, mderiv {j} (B.fn i) x * v j := by
  simp only [Matrix.mulVec, dotProduct, jacobian, add_mul, Finset.sum_add_distrib]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  congr 1
  symm
  refine Finset.sum_subset (Finset.subset_univ _) fun j _ hj => ?_
  rw [mderiv_single_eq_zero B hj, zero_mul]

lemma two_eq_zero' : (2 : ZMod 2) = 0 := rfl

/-- **Theorem 6.2 (exact error identity for arbitrary gates).**
`J(x) e⁺ = R(x, e)` with `e = x + x*` and `e⁺ = N(x) + x*`. -/
theorem error_identity (B : BoolSystem n) {xs : Fin n → ZMod 2} (hxs : IsValue B xs)
    (x : Fin n → ZMod 2) :
    jacobian B x *ᵥ (newton B x + xs) = remainder B x (x + xs) := by
  have hsplit : newton B x + xs = (x + xs) + (jacobian B x)⁻¹ *ᵥ residual B x := by
    simp only [newton]; abel
  rw [hsplit, Matrix.mulVec_add, jacobian_mulVec_inv]
  funext i
  rw [Pi.add_apply, jacobian_mulVec_apply]
  have hT := fn_taylor B i x (x + xs)
  have hxx : x + (x + xs) = xs := by
    funext j
    simp only [Pi.add_apply]
    rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  rw [hxx, sum_powerset_split] at hT
  simp only [mderiv_empty, Finset.prod_empty, mul_one, Finset.prod_singleton] at hT
  have hv := hxs i
  simp only [Pi.add_apply] at hT
  simp only [residual, remainder, Pi.add_apply]
  linear_combination hT + hv +
    (x i + ∑ j ∈ B.par i, mderiv {j} (B.fn i) x * (x j + xs j) + B.fn i x) * two_eq_zero'

/-! ### The Taylor-rank Newton contraction -/

/-- A Taylor layering: parents never lie in a higher layer, and every `S ∈ 𝓗_i` contains a
gate of strictly lower layer than `i`. The Taylor rank is one (Lemma 6.4). -/
def IsTaylorLayering (B : BoolSystem n) (lam : Fin n → ℕ) : Prop :=
  (∀ i, ∀ j ∈ B.par i, lam j ≤ lam i) ∧ ∀ i, ∀ S ∈ hset B i, ∃ j ∈ S, lam j < lam i

lemma taylorRank_eq (B : BoolSystem n) (i : Fin n) :
    taylorRank B i = max ((B.par i).sup (taylorRank B))
      ((hset B i).attach.sup fun S =>
        1 + S.1.inf' (nonempty_of_mem_hset S.2) (taylorRank B)) := by
  rw [taylorRank, Finset.sup_attach]
  congr 1
  refine Finset.sup_congr rfl fun S _ => ?_
  congr 1
  exact le_antisymm
    (Finset.le_inf' _ _ fun j hj => Finset.inf'_le _ (Finset.mem_attach _ ⟨j, hj⟩))
    (Finset.le_inf' _ _ fun j _ => Finset.inf'_le _ j.2)

/-- **Lemma 6.4 (downward closure and vanishing remainder).** -/
theorem taylorRank_isTaylorLayering (B : BoolSystem n) :
    IsTaylorLayering B (taylorRank B) := by
  refine ⟨fun i j hj => ?_, fun i S hS => ?_⟩
  · rw [taylorRank_eq B i]
    exact le_max_of_le_left (Finset.le_sup (f := taylorRank B) hj)
  · have hle : 1 + S.inf' (nonempty_of_mem_hset hS) (taylorRank B) ≤ taylorRank B i := by
      rw [taylorRank_eq B i]
      refine le_max_of_le_right ?_
      exact Finset.le_sup (f := fun S : hset B i =>
        1 + S.1.inf' (nonempty_of_mem_hset S.2) (taylorRank B)) (Finset.mem_attach _ ⟨S, hS⟩)
    obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_inf' (nonempty_of_mem_hset hS) (taylorRank B)
    exact ⟨j, hj, by omega⟩

/-- Taylor-rank contraction for an arbitrary Taylor layering. -/
theorem newton_exact_of_isTaylorLayering {B : BoolSystem n} {lam : Fin n → ℕ}
    (hlam : IsTaylorLayering B lam) {xs : Fin n → ZMod 2} (hxs : IsValue B xs)
    (x0 : Fin n → ZMod 2) (t : ℕ) (i : Fin n) (hi : lam i < t) :
    (newton B)^[t] x0 i = xs i := by
  classical
  induction t generalizing i with
  | zero => exact absurd hi (Nat.not_lt_zero _)
  | succ t iht =>
    rw [Function.iterate_succ_apply']
    set x := (newton B)^[t] x0 with hx
    have hid := error_identity B hxs x
    have key : ∀ i : Fin n, lam i ≤ t → newton B x i + xs i = 0 := by
      intro i
      induction i using WellFoundedLT.induction with
      | ind i ih =>
        intro hit
        have hrow := congrFun hid i
        rw [jacobian_mulVec_apply] at hrow
        have hsum : ∑ j ∈ B.par i, mderiv {j} (B.fn i) x * (newton B x + xs) j = 0 :=
          Finset.sum_eq_zero fun j hj => by
            rw [Pi.add_apply, ih j (B.par_lt i j hj) ((hlam.1 i j hj).trans hit), mul_zero]
        have hR : remainder B x (x + xs) i = 0 := by
          refine Finset.sum_eq_zero fun S hS => ?_
          obtain ⟨hSP, hcard⟩ := Finset.mem_filter.mp hS
          by_cases hD : mderiv S (B.fn i) = 0
          · rw [hD, Pi.zero_apply, zero_mul]
          · have hSH : S ∈ hset B i := by
              unfold hset
              exact Finset.mem_filter.mpr ⟨hSP, hcard, hD⟩
            obtain ⟨j, hjS, hj⟩ := hlam.2 i S hSH
            refine mul_eq_zero_of_right _ (Finset.prod_eq_zero hjS ?_)
            rw [Pi.add_apply, iht j (by omega), CharTwo.add_self_eq_zero]
        rw [hsum, add_zero, hR] at hrow
        simpa using hrow
    exact CharTwo.add_eq_zero.mp (key i (by omega))

/-- **Theorem 6.5 (Taylor-rank Newton contraction).** From an arbitrary start, after `t`
Newton steps every gate with Taylor rank `ρ_T(i) < t` is exact. -/
theorem taylor_newton_strahler (B : BoolSystem n) {xs : Fin n → ZMod 2} (hxs : IsValue B xs)
    (x0 : Fin n → ZMod 2) (t : ℕ) (i : Fin n) (hi : taylorRank B i < t) :
    (newton B)^[t] x0 i = xs i :=
  newton_exact_of_isTaylorLayering (taylorRank_isTaylorLayering B) hxs x0 t i hi

/-- **Theorem 6.5, last claim.** `ρ_T(C) + 1` Newton steps evaluate the system. -/
theorem taylor_newton_evaluates (B : BoolSystem n) {xs : Fin n → ZMod 2} (hxs : IsValue B xs)
    (x0 : Fin n → ZMod 2) : (newton B)^[systemTaylorRank B + 1] x0 = xs := by
  funext i
  exact taylor_newton_strahler B hxs x0 _ i
    (Nat.lt_succ_of_le (Finset.le_sup (f := taylorRank B) (Finset.mem_univ i)))

/-- The value vector of a triangular Boolean system exists and is unique. -/
theorem existsUnique_isValue (B : BoolSystem n) : ∃! xs, IsValue B xs := by
  let step : (Fin n → ZMod 2) → Fin n → ZMod 2 := fun x i => B.fn i x
  have hstab : ∀ t : ℕ, ∀ i : Fin n, i.val < t →
      step^[t + 1] 0 i = step^[t] 0 i := by
    intro t
    induction t with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ t ih =>
      intro i hi
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      apply B.fn_dep
      intro j hj
      have := B.par_lt i j hj
      simpa only [Function.iterate_succ_apply'] using ih j (by omega)
  have hxs : IsValue B (step^[n] 0) := fun i => by
    have := hstab n i i.isLt
    rw [Function.iterate_succ_apply'] at this
    exact this.symm
  refine ⟨step^[n] 0, hxs, fun ys hys => ?_⟩
  funext i
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    rw [hys i, hxs i]
    exact B.fn_dep i _ _ fun j hj => ih j (B.par_lt i j hj)

end BoolSystem

end GC.NewtonStrahler
