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

/-! Comparator challenge: 008b, Knowledge compilation gives NC fragments of SC -/

namespace GC.SCLadder

open Matrix Module

abbrev F := ZMod 2

section Atoms

variable {n k k' r : ℕ}

theorem leaf_pullback (B : Matrix (Fin k) (Fin n) F) (R : Set (Fin k → F))
    (M : Matrix (Fin n) (Fin n) F) (c : Fin n → F) (D : Matrix (Fin r) (Fin n) F)
    (rep : (Fin r → F) → Fin n → F) (hrep : ∀ σ, D *ᵥ rep σ = σ)
    (hrows : ∀ i, (B * M) i ∈ Submodule.span F (Set.range D)) :
    {x | B *ᵥ (M *ᵥ x + c) ∈ R} = {x | D *ᵥ x ∈ {σ | B *ᵥ (M *ᵥ rep σ + c) ∈ R}} := by sorry

theorem leaf_conj (B : Matrix (Fin k) (Fin n) F) (R : Set (Fin k → F))
    (C : Matrix (Fin k') (Fin n) F) (R'' : Set (Fin k' → F)) (D : Matrix (Fin r) (Fin n) F)
    (rep : (Fin r → F) → Fin n → F) (hrep : ∀ σ, D *ᵥ rep σ = σ)
    (hB : ∀ i, B i ∈ Submodule.span F (Set.range D))
    (hC : ∀ i, C i ∈ Submodule.span F (Set.range D)) :
    {x | B *ᵥ x ∈ R} ∩ {x | C *ᵥ x ∈ R''} =
      {x | D *ᵥ x ∈ {σ | B *ᵥ rep σ ∈ R ∧ C *ᵥ rep σ ∈ R''}} := by sorry

end Atoms

section Decomposable

variable {α β ι ι' : Type*}

theorem conj_iUnion_prod (P : ι → Set α) (Q : ι → Set β) (P' : ι' → Set α) (Q' : ι' → Set β) :
    (⋃ i, P i ×ˢ Q i) ∩ (⋃ j, P' j ×ˢ Q' j) =
      ⋃ p : ι × ι', (P p.1 ∩ P' p.2) ×ˢ (Q p.1 ∩ Q' p.2) := by sorry

theorem conj_pairwise_disjoint (P : ι → Set α) (Q : ι → Set β) (P' : ι' → Set α)
    (Q' : ι' → Set β) (h : Pairwise fun i i' => Disjoint (P i ×ˢ Q i) (P i' ×ˢ Q i'))
    (h' : Pairwise fun j j' => Disjoint (P' j ×ˢ Q' j) (P' j' ×ˢ Q' j')) :
    Pairwise fun p p' : ι × ι' => Disjoint ((P p.1 ∩ P' p.2) ×ˢ (Q p.1 ∩ Q' p.2))
      ((P p'.1 ∩ P' p'.2) ×ˢ (Q p'.1 ∩ Q' p'.2)) := by sorry

end Decomposable

section Transfer

variable {nL nR rL rR : ℕ} {ι : Type*}

theorem transfer_pullback (ALL : Matrix (Fin nL) (Fin nL) F) (ARR : Matrix (Fin nR) (Fin nR) F)
    (ULR : Matrix (Fin nL) (Fin rR) F) (VLR : Matrix (Fin rR) (Fin nR) F)
    (URL : Matrix (Fin nR) (Fin rL) F) (VRL : Matrix (Fin rL) (Fin nL) F)
    (bL : Fin nL → F) (bR : Fin nR → F) (P : ι → Set (Fin nL → F)) (Q : ι → Set (Fin nR → F)) :
    let T : (Fin nL → F) × (Fin nR → F) → (Fin nL → F) × (Fin nR → F) := fun x =>
      (ALL *ᵥ x.1 + (ULR * VLR) *ᵥ x.2 + bL, (URL * VRL) *ᵥ x.1 + ARR *ᵥ x.2 + bR)
    let term : ι × (Fin rL → F) × (Fin rR → F) → Set ((Fin nL → F) × (Fin nR → F)) := fun t =>
      {xL | VRL *ᵥ xL = t.2.1 ∧ ALL *ᵥ xL + ULR *ᵥ t.2.2 + bL ∈ P t.1} ×ˢ
        {xR | VLR *ᵥ xR = t.2.2 ∧ ARR *ᵥ xR + URL *ᵥ t.2.1 + bR ∈ Q t.1}
    (T ⁻¹' ⋃ i, P i ×ˢ Q i = ⋃ t, term t) ∧
      ((Pairwise fun i j => Disjoint (P i ×ˢ Q i) (P j ×ˢ Q j)) →
        Pairwise fun t t' => Disjoint (term t) (term t')) := by sorry

end Transfer

section Equality

variable {α : Type*}

theorem piece_injective {n r₁ r₂ : ℕ} (B₁ : Matrix (Fin r₁) (Fin n) F)
    (B₂ : Matrix (Fin r₂) (Fin n) F) (s₁ : Fin r₁ → F) (s₂ : Fin r₂ → F)
    (h : {x | B₁ *ᵥ x = s₁} ×ˢ {x | B₂ *ᵥ x = s₂} ⊆ {p | p.1 = p.2})
    (hne : ({x | B₁ *ᵥ x = s₁} ×ˢ {x | B₂ *ᵥ x = s₂}).Nonempty) :
    Function.Injective B₁.mulVec ∧ Function.Injective B₂.mulVec := by sorry

theorem diag_cover_card [Fintype α] {ι : Type*} [Fintype ι] (A B : ι → Set α)
    (hsub : ∀ i, A i ×ˢ B i ⊆ {p | p.1 = p.2})
    (hcov : {p : α × α | p.1 = p.2} ⊆ ⋃ i, A i ×ˢ B i) : Fintype.card α ≤ Fintype.card ι := by sorry

theorem ordered_equality_states {n : ℕ} {St : Type*} [Finite St] (σ : (Fin n → F) → St)
    (acc : St → (Fin n → F) → Prop) (h : ∀ a b, acc (σ a) b ↔ a = b) :
    Function.Injective σ ∧ 2 ^ n ≤ Nat.card St := by sorry

end Equality

section InnerProduct

variable {n : ℕ}

theorem rect_card_le (A B : Set (Fin n → F)) (h : ∀ a ∈ A, ∀ b ∈ B, a ⬝ᵥ b = 1) :
    A.ncard * B.ncard ≤ 2 ^ (n - 1) := by sorry

theorem card_ip_eq_one :
    (Finset.univ.filter fun p : (Fin n → F) × (Fin n → F) => p.1 ⬝ᵥ p.2 = 1).card =
      (2 ^ n - 1) * 2 ^ (n - 1) := by sorry

theorem ip_rect_cover_card {ι : Type*} [Fintype ι] (A B : ι → Set (Fin n → F))
    (hsub : ∀ i, A i ×ˢ B i ⊆ {p | p.1 ⬝ᵥ p.2 = 1})
    (hcov : {p : (Fin n → F) × (Fin n → F) | p.1 ⬝ᵥ p.2 = 1} ⊆ ⋃ i, A i ×ˢ B i) :
    2 ^ n - 1 ≤ Fintype.card ι := by sorry

end InnerProduct

end GC.SCLadder
