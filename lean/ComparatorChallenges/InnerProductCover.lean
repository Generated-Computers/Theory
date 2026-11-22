import Mathlib.Algebra.CharP.Two
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Logic.Equiv.Fin.Basic

/-! Comparator challenge: 008c, Inner product has affine-cover number 2^m -/

namespace GC.SCLadder

open Module Matrix

abbrev F := ZMod 2

abbrev Vec (m : ℕ) := Fin m → F

abbrev Pt (m : ℕ) := Vec m × Vec m × F

def H (m : ℕ) : Set (Pt m) := {p | p.2.2 = p.1 ⬝ᵥ p.2.1}

noncomputable def affineCoverNumber {k V : Type*} [Ring k] [AddCommGroup V] [Module k V]
    (S : Set V) : ℕ :=
  sInf {n | ∃ A : Fin n → AffineSubspace k V, (∀ i, (A i : Set V) ⊆ S) ∧ ⋃ i, (A i : Set V) = S}

noncomputable def fiberLin {m : ℕ} (a : Vec m) : Vec m →ₗ[F] Pt m :=
  LinearMap.prod 0 (LinearMap.prod LinearMap.id ((dotProductEquiv F (Fin m)) a))

noncomputable def fiber {m : ℕ} (a : Vec m) : AffineSubspace F (Pt m) :=
  AffineSubspace.mk' (a, 0, 0) (LinearMap.range (fiberLin a))

theorem inner_product_affine_cover_number (m : ℕ) :
    (∀ A : AffineSubspace F (Pt m), (A : Set (Pt m)) ⊆ H m → (A : Set (Pt m)).ncard ≤ 2 ^ m) ∧
    affineCoverNumber (k := F) (H m) = 2 ^ m ∧
    (∀ a : Vec m, (fiber a : Set (Pt m)) ⊆ H m) ∧
    ⋃ a : Vec m, (fiber a : Set (Pt m)) = H m ∧
    Pairwise (fun a a' : Vec m => Disjoint (fiber a : Set (Pt m)) (fiber a')) := by sorry

theorem exact_projection {p nx ny k : ℕ} (Ax : Matrix (Fin p) (Fin nx) F)
    (Ay : Matrix (Fin p) (Fin ny) F) (b : Fin p → F) (L : Matrix (Fin k) (Fin p) F)
    (hL0 : L * Ay = 0) (hLspan : ∀ ℓ : Fin p → F, ℓ ᵥ* Ay = 0 → ℓ ∈ Submodule.span F (Set.range L))
    (x : Fin nx → F) :
    (∃ y, Ax *ᵥ x + Ay *ᵥ y = b) ↔ L *ᵥ (Ax *ᵥ x) = L *ᵥ b := by sorry

theorem index_state_lower_bound {m : ℕ} {St : Type*} [Finite St] (σ : Vec m → St) (acc : St → Fin m → F → Prop)
    (h : ∀ y i z, acc (σ y) i z ↔ z = y i) : Function.Injective σ ∧ 2 ^ m ≤ Nat.card St := by sorry

end GC.SCLadder
