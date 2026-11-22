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

/-! Comparator challenge: 008e, Few nonlinear gates per path put circuits in NC -/

namespace GC.SCLadder

open Matrix

abbrev F := ZMod 2

variable {n : ℕ}

def StrictLower (M : Matrix (Fin n) (Fin n) F) : Prop := ∀ i j, i ≤ j → M i j = 0

def squaringProduct (M : Matrix (Fin n) (Fin n) F) (s : ℕ) : Matrix (Fin n) (Fin n) F :=
  ((List.range s).map fun k => 1 + M ^ (2 ^ k)).prod

theorem triangular_product_identity {M : Matrix (Fin n) (Fin n) F} (hM : StrictLower M) {s : ℕ}
    (hs : n ≤ 2 ^ s) :
    (1 + M) * squaringProduct M s = 1 ∧ squaringProduct M s * (1 + M) = 1 ∧
      (1 + M)⁻¹ = squaringProduct M s := by sorry

theorem region_solve {m : ℕ} {M : Matrix (Fin n) (Fin n) F} (hM : StrictLower M) {s : ℕ}
    (hs : n ≤ 2 ^ s) (N : Matrix (Fin n) (Fin m) F) (c : Fin n → F) (z : Fin m → F)
    (x : Fin n → F) :
    x = M *ᵥ x + N *ᵥ z + c ↔
      x = (squaringProduct M s * N) *ᵥ z + squaringProduct M s *ᵥ c := by sorry

structure DepthCircuit (L : ℕ) where
  refs : Fin L → List (Fin L)
  refs_lt : ∀ v, ∀ w ∈ refs v, w < v
  barrier : Fin L → Bool

namespace DepthCircuit

variable {L : ℕ} (K : DepthCircuit L)

def depth (v : Fin L) : ℕ :=
  (if K.barrier v then 1 else 0) +
    ((K.refs v).attach.map fun (w : {w // w ∈ K.refs v}) =>
      have : (w.1 : ℕ) < v := K.refs_lt v w.1 w.2
      depth w.1).foldr max 0
termination_by (v : ℕ)

theorem depth_le_of_ref {v w : Fin L} (hw : w ∈ K.refs v) : K.depth w ≤ K.depth v := by sorry

theorem depth_lt_of_barrier {v w : Fin L} (hv : K.barrier v = true) (hw : w ∈ K.refs v) :
    K.depth w + 1 ≤ K.depth v := by sorry

end DepthCircuit

end GC.SCLadder
