import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
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

/-- `j` is a parent of gate `i`. -/
def IsParent (C : Circuit n) (i j : Fin n) : Prop :=
  match C.gate i with
  | .const _ => False
  | .affine _ A => j ∈ A
  | .prod p q => j = p ∨ j = q

/-- Lemma 2.3(a): `J(x)` is unit lower triangular, so `det J(x) = 1`. -/
theorem det_jacobian (C : Circuit n) (x : Fin n → ZMod 2) : (jacobian C x).det = 1 := by
  sorry

/-- Lemma 2.3(b), existence and uniqueness of the value vector. -/
theorem existsUnique_isValue (C : Circuit n) : ∃! xs, IsValue C xs := by
  sorry

/-- Lemma 2.3(c): `N(x) = x` if and only if `x` is the value vector. -/
theorem newton_eq_self_iff (C : Circuit n) (x : Fin n → ZMod 2) :
    newton C x = x ↔ IsValue C x := by
  sorry

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
  sorry

/-- A valid layering (Remark 3.5(ii)): parents never have a larger layer, and at every
product gate at least one parent lies in a strictly lower layer. -/
def IsValidLayering (C : Circuit n) (lam : Fin n → ℕ) : Prop :=
  (∀ i j, IsParent C i j → lam j ≤ lam i) ∧
    ∀ i p q, C.gate i = .prod p q → min (lam p) (lam q) < lam i

/-- Lemma 3.3: the rank is a valid layering (downward closure and balanced sources). -/
theorem rank_isValidLayering (C : Circuit n) : IsValidLayering C (rank C) := by
  sorry

/-- Remark 3.5(ii): the rank is the smallest valid layering. -/
theorem rank_le_of_isValidLayering {C : Circuit n} {lam : Fin n → ℕ}
    (hlam : IsValidLayering C lam) (i : Fin n) : rank C i ≤ lam i := by
  sorry

/-- **Theorem 3.4 (Newton–Strahler contraction).** Let `x*` be the value vector of an
affine–product circuit over `GF(2)`. From an arbitrary starting vector, after `t` exact Newton
steps every gate of Horton–Strahler rank `ρ(i) < t` has its correct value. -/
theorem newton_strahler (C : Circuit n) {xs : Fin n → ZMod 2} (hxs : IsValue C xs)
    (x0 : Fin n → ZMod 2) (t : ℕ) (i : Fin n) (hi : rank C i < t) :
    (newton C)^[t] x0 i = xs i := by
  sorry

/-- **Theorem 3.4, last claim.** `ρ(C) + 1` Newton steps from any start evaluate the circuit. -/
theorem newton_evaluates (C : Circuit n) {xs : Fin n → ZMod 2} (hxs : IsValue C xs)
    (x0 : Fin n → ZMod 2) : (newton C)^[circuitRank C + 1] x0 = xs := by
  sorry

/-- Remark 3.5(ii): any valid layering with all layers `≤ K` certifies that `K + 1` Newton
steps evaluate the circuit. -/
theorem newton_evaluates_of_isValidLayering {C : Circuit n} {lam : Fin n → ℕ}
    (hlam : IsValidLayering C lam) {K : ℕ} (hK : ∀ i, lam i ≤ K) {xs : Fin n → ZMod 2}
    (hxs : IsValue C xs) (x0 : Fin n → ZMod 2) : (newton C)^[K + 1] x0 = xs := by
  sorry

end GC.NewtonStrahler

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

/-- **Lemma 6.1 (exact multilinear Taylor identity)**, for increments supported on `W`:
`g(x + e) = ∑_{S ⊆ W} (∂_S g)(x) e_S`. -/
theorem taylor_identity (W : Finset (Fin n)) :
    ∀ (g : (Fin n → ZMod 2) → ZMod 2) (x e : Fin n → ZMod 2), (∀ j ∉ W, e j = 0) →
      g (x + e) = ∑ S ∈ W.powerset, mderiv S g x * ∏ j ∈ S, e j := by
  sorry

namespace BoolSystem

/-- **Theorem 6.2 (exact error identity for arbitrary gates).**
`J(x) e⁺ = R(x, e)` with `e = x + x*` and `e⁺ = N(x) + x*`. -/
theorem error_identity (B : BoolSystem n) {xs : Fin n → ZMod 2} (hxs : IsValue B xs)
    (x : Fin n → ZMod 2) :
    jacobian B x *ᵥ (newton B x + xs) = remainder B x (x + xs) := by
  sorry

/-- **Theorem 6.5 (Taylor-rank Newton contraction).** From an arbitrary start, after `t`
Newton steps every gate with Taylor rank `ρ_T(i) < t` is exact. -/
theorem taylor_newton_strahler (B : BoolSystem n) {xs : Fin n → ZMod 2} (hxs : IsValue B xs)
    (x0 : Fin n → ZMod 2) (t : ℕ) (i : Fin n) (hi : taylorRank B i < t) :
    (newton B)^[t] x0 i = xs i := by
  sorry

/-- **Theorem 6.5, last claim.** `ρ_T(C) + 1` Newton steps evaluate the system. -/
theorem taylor_newton_evaluates (B : BoolSystem n) {xs : Fin n → ZMod 2} (hxs : IsValue B xs)
    (x0 : Fin n → ZMod 2) : (newton B)^[systemTaylorRank B + 1] x0 = xs := by
  sorry

/-- The value vector of a triangular Boolean system exists and is unique. -/
theorem existsUnique_isValue (B : BoolSystem n) : ∃! xs, IsValue B xs := by
  sorry

end BoolSystem

end GC.NewtonStrahler
