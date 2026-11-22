import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.LinearCombination

namespace GC.NewtonStrahler

open Matrix

/-- A gate of an affine–product circuit with `n` gates over `GF(2) = ZMod 2`:
a constant gate `x_i = c`, an affine gate `x_i = c + ∑_{j ∈ A} x_j`, or a product gate
`x_i = x_p * x_q`. -/
inductive Gate (n : ℕ) where
  | const (c : ZMod 2)
  | affine (c : ZMod 2) (A : Finset (Fin n))
  | prod (p q : Fin n)

/-- Well-formedness of gate number `i`: parents precede `i`, and the two parents of a product
gate are distinct. -/
def Gate.WF {n : ℕ} (i : Fin n) : Gate n → Prop
  | .const _ => True
  | .affine _ A => ∀ j ∈ A, j < i
  | .prod p q => p < i ∧ q < i ∧ p ≠ q

/-- An affine–product circuit (Definition 2.1 of the paper). -/
structure Circuit (n : ℕ) where
  gate : Fin n → Gate n
  wf : ∀ i, (gate i).WF i

/-- The right-hand side `f_i(x)` of a gate. -/
def Gate.eval {n : ℕ} : Gate n → (Fin n → ZMod 2) → ZMod 2
  | .const c, _ => c
  | .affine c A, x => c + ∑ j ∈ A, x j
  | .prod p q, x => x p * x q

/-- The formal partial derivative `∂ f_i / ∂ x_j` of the right-hand side of a gate at `x`. -/
def Gate.deriv {n : ℕ} : Gate n → (Fin n → ZMod 2) → Fin n → ZMod 2
  | .const _, _, _ => 0
  | .affine _ A, _, j => if j ∈ A then 1 else 0
  | .prod p q, x, j => (if j = p then x q else 0) + (if j = q then x p else 0)

variable {n : ℕ}

/-- `xs` is the value vector of `C`: `xs_i = f_i(xs)` for every gate `i`. -/
def IsValue (C : Circuit n) (xs : Fin n → ZMod 2) : Prop :=
  ∀ i, xs i = (C.gate i).eval xs

/-- The residual `F_i(x) = x_i + f_i(x)`. -/
def residual (C : Circuit n) (x : Fin n → ZMod 2) : Fin n → ZMod 2 :=
  fun i => x i + (C.gate i).eval x

/-- The formal Jacobian `J(x) = (∂F_i/∂x_j)(x)` of the residual over `GF(2)`. -/
def jacobian (C : Circuit n) (x : Fin n → ZMod 2) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  fun i j => (if i = j then 1 else 0) + (C.gate i).deriv x j

/-- The Newton map `N(x) = x + J(x)⁻¹ F(x)` over `GF(2)`. -/
noncomputable def newton (C : Circuit n) (x : Fin n → ZMod 2) : Fin n → ZMod 2 :=
  x + (jacobian C x)⁻¹ *ᵥ residual C x

/-- The Horton–Strahler combination `hs(a,b)`: `max a b` if `a ≠ b`, and `a + 1` if `a = b`. -/
def hs (a b : ℕ) : ℕ := if a = b then a + 1 else max a b

/-- The Horton–Strahler rank `ρ(i)` of a gate (Definition 3.2). -/
def rank (C : Circuit n) (i : Fin n) : ℕ :=
  match _h : C.gate i with
  | .const _ => 0
  | .affine _ A => A.attach.sup fun j => rank C j.1
  | .prod p q => hs (rank C p) (rank C q)
termination_by i.val
decreasing_by
  all_goals
    have hw := C.wf i
    rw [_h] at hw
    simp only [Gate.WF] at hw
  · exact hw _ j.2
  · exact hw.1
  · exact hw.2.1

/-- The rank `ρ(C) = max_i ρ(i)` of a circuit. -/
def circuitRank (C : Circuit n) : ℕ := Finset.univ.sup (rank C)


/-! ### Basic facts about the circuit -/

/-- `j` is a parent of gate `i`. -/
def IsParent (C : Circuit n) (i j : Fin n) : Prop :=
  match C.gate i with
  | .const _ => False
  | .affine _ A => j ∈ A
  | .prod p q => j = p ∨ j = q

lemma two_eq_zero : (2 : ZMod 2) = 0 := rfl

lemma IsParent.lt {C : Circuit n} {i j : Fin n} (h : IsParent C i j) : j < i := by
  have hw := C.wf i
  unfold IsParent at h
  split at h <;> rename_i heq <;> simp only [heq, Gate.WF] at hw
  · exact h.elim
  · exact hw j h
  · exact h.elim (fun h => h ▸ hw.1) (fun h => h ▸ hw.2.1)

lemma deriv_eq_zero_of_not_parent {C : Circuit n} {i j : Fin n} (x : Fin n → ZMod 2)
    (h : ¬ IsParent C i j) : (C.gate i).deriv x j = 0 := by
  unfold IsParent at h
  revert h
  cases C.gate i with
  | const c => simp [Gate.deriv]
  | affine c A => intro h; simp [Gate.deriv, h]
  | prod p q =>
    intro h
    push Not at h
    simp [Gate.deriv, h.1, h.2]

lemma eval_congr {C : Circuit n} {i : Fin n} {x y : Fin n → ZMod 2}
    (h : ∀ j, IsParent C i j → x j = y j) : (C.gate i).eval x = (C.gate i).eval y := by
  unfold IsParent at h
  revert h
  cases C.gate i with
  | const c => simp [Gate.eval]
  | affine c A =>
    intro h
    simp only [Gate.eval]
    rw [Finset.sum_congr rfl fun j hj => h j hj]
  | prod p q =>
    intro h
    simp [Gate.eval, h p (Or.inl rfl), h q (Or.inr rfl)]

lemma jacobian_diag (C : Circuit n) (x : Fin n → ZMod 2) (i : Fin n) :
    jacobian C x i i = 1 := by
  have : ¬ IsParent C i i := fun h => lt_irrefl _ h.lt
  simp [jacobian, deriv_eq_zero_of_not_parent x this]

lemma jacobian_isLowerTriangular (C : Circuit n) (x : Fin n → ZMod 2) :
    (jacobian C x).IsLowerTriangular := by
  intro i j hij
  have hij' : i < j := hij
  have hne : i ≠ j := ne_of_lt hij'
  have : ¬ IsParent C i j := fun h => absurd h.lt (not_lt.mpr hij'.le)
  simp [jacobian, hne, deriv_eq_zero_of_not_parent x this]

/-- Lemma 2.3(a): `J(x)` is unit lower triangular, so `det J(x) = 1`. -/
theorem det_jacobian (C : Circuit n) (x : Fin n → ZMod 2) : (jacobian C x).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ (jacobian_isLowerTriangular C x)]
  simp [jacobian_diag]

lemma jacobian_mulVec_inv (C : Circuit n) (x v : Fin n → ZMod 2) :
    jacobian C x *ᵥ ((jacobian C x)⁻¹ *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (by simp [det_jacobian]),
    Matrix.one_mulVec]

lemma jacobian_mulVec_apply (C : Circuit n) (x v : Fin n → ZMod 2) (i : Fin n) :
    (jacobian C x *ᵥ v) i = v i + ∑ j, (C.gate i).deriv x j * v j := by
  simp only [Matrix.mulVec, dotProduct, jacobian, add_mul, Finset.sum_add_distrib]
  simp

lemma sum_deriv_mul (g : Gate n) (x v : Fin n → ZMod 2) :
    ∑ j, g.deriv x j * v j =
      match g with
      | .const _ => 0
      | .affine _ A => ∑ j ∈ A, v j
      | .prod p q => x q * v p + x p * v q := by
  cases g with
  | const c => simp [Gate.deriv]
  | affine c A => simp [Gate.deriv, ite_mul, Finset.sum_ite_mem]
  | prod p q => simp [Gate.deriv, add_mul, ite_mul, Finset.sum_add_distrib]

/-- Lemma 2.3(b), existence and uniqueness of the value vector. -/
theorem existsUnique_isValue (C : Circuit n) : ∃! xs, IsValue C xs := by
  let step : (Fin n → ZMod 2) → Fin n → ZMod 2 := fun x i => (C.gate i).eval x
  have hstab : ∀ t : ℕ, ∀ i : Fin n, i.val < t →
      step^[t + 1] 0 i = step^[t] 0 i := by
    intro t
    induction t with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ t ih =>
      intro i hi
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      apply eval_congr
      intro j hj
      have := hj.lt
      simpa only [Function.iterate_succ_apply'] using ih j (by omega)
  refine ⟨step^[n] 0, fun i => ?_, fun ys hys => ?_⟩
  · have := hstab n i i.isLt
    rw [Function.iterate_succ_apply'] at this
    exact this.symm
  · have hxs : IsValue C (step^[n] 0) := fun i => by
      have := hstab n i i.isLt
      rw [Function.iterate_succ_apply'] at this
      exact this.symm
    funext i
    induction i using WellFoundedLT.induction with
    | ind i ih =>
      rw [hys i, hxs i]
      exact eval_congr fun j hj => ih j hj.lt

lemma residual_eq_zero_iff (C : Circuit n) (x : Fin n → ZMod 2) :
    residual C x = 0 ↔ IsValue C x := by
  constructor
  · intro h i
    have := congrFun h i
    simpa [residual, CharTwo.add_eq_zero] using this
  · intro h
    funext i
    simp [residual, CharTwo.add_eq_zero, ← h i]

/-- Lemma 2.3(c): `N(x) = x` if and only if `x` is the value vector. -/
theorem newton_eq_self_iff (C : Circuit n) (x : Fin n → ZMod 2) :
    newton C x = x ↔ IsValue C x := by
  rw [← residual_eq_zero_iff]
  constructor
  · intro h
    have h0 : (jacobian C x)⁻¹ *ᵥ residual C x = 0 := by
      have := congrArg (fun y => y + x) h
      simpa [newton, add_comm x, add_assoc, CharTwo.add_self_eq_zero] using this
    rw [← jacobian_mulVec_inv C x (residual C x), h0, Matrix.mulVec_zero]
  · intro h
    simp [newton, h]

/-! ### The error identity -/

/-- The quadratic source `Q(e)`: `e_p e_q` at a product gate, `0` elsewhere. -/
def quadSource (C : Circuit n) (e : Fin n → ZMod 2) : Fin n → ZMod 2 :=
  fun i => match C.gate i with
    | .prod p q => e p * e q
    | _ => 0

/-- Lemma 3.1 (exact one-step error identity): `J(x) e⁺ = Q(e)` with `e = x + x*` and
`e⁺ = N(x) + x*`. -/
theorem error_identity (C : Circuit n) {xs : Fin n → ZMod 2} (hxs : IsValue C xs)
    (x : Fin n → ZMod 2) :
    jacobian C x *ᵥ (newton C x + xs) = quadSource C (x + xs) := by
  have hsplit : newton C x + xs = (x + xs) + (jacobian C x)⁻¹ *ᵥ residual C x := by
    simp only [newton]; abel
  rw [hsplit, Matrix.mulVec_add, jacobian_mulVec_inv]
  funext i
  rw [Pi.add_apply, jacobian_mulVec_apply, sum_deriv_mul]
  simp only [residual, quadSource, Pi.add_apply]
  rw [hxs i]
  cases C.gate i with
  | const c =>
    simp only [Gate.eval]
    linear_combination (x i + c) * two_eq_zero
  | affine c A =>
    simp only [Gate.eval, Finset.sum_add_distrib]
    linear_combination (x i + c + ∑ j ∈ A, x j + ∑ j ∈ A, xs j) * two_eq_zero
  | prod p q =>
    simp only [Gate.eval]
    linear_combination (x i + x p * x q) * two_eq_zero

/-! ### Rank, valid layerings and the Newton–Strahler theorem -/

lemma rank_const {C : Circuit n} {i : Fin n} {c : ZMod 2} (h : C.gate i = .const c) :
    rank C i = 0 := by
  rw [rank.eq_def]; split <;> simp_all

lemma rank_affine {C : Circuit n} {i : Fin n} {c : ZMod 2} {A : Finset (Fin n)}
    (h : C.gate i = .affine c A) : rank C i = A.sup (rank C) := by
  rw [rank.eq_def]; split <;> simp_all [Finset.sup_attach]

lemma rank_prod {C : Circuit n} {i p q : Fin n} (h : C.gate i = .prod p q) :
    rank C i = hs (rank C p) (rank C q) := by
  rw [rank.eq_def]; split <;> simp_all

lemma le_hs_left (a b : ℕ) : a ≤ hs a b := by unfold hs; split_ifs <;> omega
lemma le_hs_right (a b : ℕ) : b ≤ hs a b := by unfold hs; split_ifs <;> omega
lemma min_lt_hs (a b : ℕ) : min a b < hs a b := by unfold hs; split_ifs <;> omega

/-- A valid layering (Remark 3.5(ii)): parents never have a larger layer, and at every
product gate at least one parent lies in a strictly lower layer. -/
def IsValidLayering (C : Circuit n) (lam : Fin n → ℕ) : Prop :=
  (∀ i j, IsParent C i j → lam j ≤ lam i) ∧
    ∀ i p q, C.gate i = .prod p q → min (lam p) (lam q) < lam i

/-- Lemma 3.3: the rank is a valid layering (downward closure and balanced sources). -/
theorem rank_isValidLayering (C : Circuit n) : IsValidLayering C (rank C) := by
  refine ⟨fun i j hij => ?_, fun i p q h => ?_⟩
  · unfold IsParent at hij
    split at hij <;> rename_i heq
    · exact hij.elim
    · rw [rank_affine heq]; exact Finset.le_sup hij
    · rw [rank_prod heq]
      rcases hij with rfl | rfl
      · exact le_hs_left _ _
      · exact le_hs_right _ _
  · rw [rank_prod h]; exact min_lt_hs _ _

/-- Remark 3.5(ii): the rank is the smallest valid layering. -/
theorem rank_le_of_isValidLayering {C : Circuit n} {lam : Fin n → ℕ}
    (hlam : IsValidLayering C lam) (i : Fin n) : rank C i ≤ lam i := by
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    rcases hg : C.gate i with c | ⟨c, A⟩ | ⟨p, q⟩
    · simp [rank_const hg]
    · rw [rank_affine hg]
      refine Finset.sup_le fun j hj => ?_
      have hpar : IsParent C i j := by unfold IsParent; rw [hg]; exact hj
      exact (ih j hpar.lt).trans (hlam.1 i j hpar)
    · rw [rank_prod hg]
      have hp : IsParent C i p := by unfold IsParent; rw [hg]; exact Or.inl rfl
      have hq : IsParent C i q := by unfold IsParent; rw [hg]; exact Or.inr rfl
      have h1 := ih p hp.lt
      have h2 := ih q hq.lt
      have h3 := hlam.1 i p hp
      have h4 := hlam.1 i q hq
      have h5 := hlam.2 i p q hg
      unfold hs; split_ifs <;> omega

/-- Theorem 3.4 for a valid layering (Remark 3.5(ii)): from an arbitrary start, after `t`
Newton steps every gate of layer `< t` has its correct value. -/
theorem newton_exact_of_isValidLayering {C : Circuit n} {lam : Fin n → ℕ}
    (hlam : IsValidLayering C lam) {xs : Fin n → ZMod 2} (hxs : IsValue C xs)
    (x0 : Fin n → ZMod 2) (t : ℕ) (i : Fin n) (hi : lam i < t) :
    (newton C)^[t] x0 i = xs i := by
  induction t generalizing i with
  | zero => exact absurd hi (Nat.not_lt_zero _)
  | succ t iht =>
    rw [Function.iterate_succ_apply']
    set x := (newton C)^[t] x0 with hx
    have hid := error_identity C hxs x
    -- every gate of layer `≤ t` has zero error after the step
    have key : ∀ i : Fin n, lam i ≤ t → newton C x i + xs i = 0 := by
      intro i
      induction i using WellFoundedLT.induction with
      | ind i ih =>
        intro hit
        have hrow := congrFun hid i
        rw [jacobian_mulVec_apply] at hrow
        have hsum : ∑ j, (C.gate i).deriv x j * (newton C x + xs) j = 0 := by
          refine Finset.sum_eq_zero fun j _ => ?_
          by_cases hj : IsParent C i j
          · rw [Pi.add_apply, ih j hj.lt ((hlam.1 i j hj).trans hit), mul_zero]
          · rw [deriv_eq_zero_of_not_parent x hj, zero_mul]
        have hQ : quadSource C (x + xs) i = 0 := by
          simp only [quadSource]
          split
          · rename_i p q heq
            have hmin := hlam.2 i p q heq
            rcases Nat.lt_or_ge (lam p) t with hp | hp
            · rw [Pi.add_apply, Pi.add_apply (f := x), iht p hp,
                CharTwo.add_self_eq_zero, zero_mul]
            · have hq : lam q < t := by omega
              rw [Pi.add_apply (f := x), Pi.add_apply (f := x), iht q hq,
                CharTwo.add_self_eq_zero, mul_zero]
          · rfl
        rw [hsum, add_zero, hQ] at hrow
        simpa using hrow
    exact CharTwo.add_eq_zero.mp (key i (by omega))

/-- **Theorem 3.4 (Newton–Strahler contraction).** Let `x*` be the value vector of an
affine–product circuit over `GF(2)`. From an arbitrary starting vector, after `t` exact Newton
steps every gate of Horton–Strahler rank `ρ(i) < t` has its correct value. -/
theorem newton_strahler (C : Circuit n) {xs : Fin n → ZMod 2} (hxs : IsValue C xs)
    (x0 : Fin n → ZMod 2) (t : ℕ) (i : Fin n) (hi : rank C i < t) :
    (newton C)^[t] x0 i = xs i :=
  newton_exact_of_isValidLayering (rank_isValidLayering C) hxs x0 t i hi

/-- **Theorem 3.4, last claim.** `ρ(C) + 1` Newton steps from any start evaluate the circuit. -/
theorem newton_evaluates (C : Circuit n) {xs : Fin n → ZMod 2} (hxs : IsValue C xs)
    (x0 : Fin n → ZMod 2) : (newton C)^[circuitRank C + 1] x0 = xs := by
  funext i
  exact newton_strahler C hxs x0 _ i
    (Nat.lt_succ_of_le (Finset.le_sup (f := rank C) (Finset.mem_univ i)))

/-- Remark 3.5(ii): any valid layering with all layers `≤ K` certifies that `K + 1` Newton
steps evaluate the circuit. -/
theorem newton_evaluates_of_isValidLayering {C : Circuit n} {lam : Fin n → ℕ}
    (hlam : IsValidLayering C lam) {K : ℕ} (hK : ∀ i, lam i ≤ K) {xs : Fin n → ZMod 2}
    (hxs : IsValue C xs) (x0 : Fin n → ZMod 2) : (newton C)^[K + 1] x0 = xs := by
  funext i
  exact newton_exact_of_isValidLayering hlam hxs x0 _ i (Nat.lt_succ_of_le (hK i))

end GC.NewtonStrahler
