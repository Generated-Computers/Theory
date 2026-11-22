import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Group.Commutator
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.GroupTheory.Perm.ClosureSwap
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.Induction
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.GroupTheory.FreeGroup.Basic

namespace GC.A5Programs

open Equiv

section Descriptors

variable {G : Type*} [Group G]

/-- A Latin factor `z = x y` can be solved for each of its variables, which gives the six
oriented forms `y = x⁻¹ z`, `x = z y⁻¹`, `z = x y` (with the known third value as a coefficient)
of 004e, Lemma 5.1. -/
theorem latin_relations (x y z : G) :
    (z = x * y ↔ y = x⁻¹ * z) ∧ (z = x * y ↔ x = z * y⁻¹) := by
  sorry

/-- The descriptor `x ↦ a x^ε b`, with sign `ε = true` for `+1` and `false` for `-1`. -/
def descr (a b : G) : Bool → G → G
  | true, x => a * x * b
  | false, x => a * x⁻¹ * b

theorem descriptor_comp_pos (a b c d : G) (ε : Bool) (x : G) :
    descr c d true (descr a b ε x) = descr (c * a) (b * d) ε x := by
  sorry

theorem descriptor_comp_neg (a b c d : G) (ε : Bool) (x : G) :
    descr c d false (descr a b ε x) = descr (c * b⁻¹) (a⁻¹ * d) (!ε) x := by
  sorry

theorem descriptor_inv_pos (a b x : G) :
    descr a⁻¹ b⁻¹ true (descr a b true x) = x := by
  sorry

theorem descriptor_inv_neg (a b x : G) :
    descr b a false (descr a b false x) = x := by
  sorry

/-- Composition of descriptors is a descriptor (with explicit new coefficients). -/
theorem comp_descriptors (Φ : ℕ → G × G × Bool) (m : ℕ) :
    ∃ A B : G, ∃ ε : Bool, ∀ x,
      (List.range m).foldl (fun y i => descr (Φ i).1 (Φ i).2.1 (Φ i).2.2 y) x = descr A B ε x := by
  sorry

end Descriptors

section Monodromy

variable {X : Type*}

/-- The prefix compositions `Ψ_i = Φ_{i-1} ∘ ⋯ ∘ Φ_0`. -/
def prefixMap (Φ : ℕ → X → X) : ℕ → X → X
  | 0, x => x
  | i + 1, x => Φ i (prefixMap Φ i x)

/-- **Cycle monodromy** (004e, Theorem 5.2; 004f, Theorem 3.3). For relations
`q_{i+1} = Φ_i(q_i)` (`0 ≤ i < m - 1`) closed by `q_0 = Φ_{m-1}(q_{m-1})`, an assignment
`q_0, …, q_{m-1}` satisfies all `m` relations iff `q_i = Ψ_i(q_0)` for all `i < m` and `q_0` is a
root of the return map `Ψ_m`. Hence `r ↦ (Ψ_i r)_i` is a bijection from the roots of
`r = Ψ_m(r)` onto the solutions. -/
theorem cycle_monodromy (Φ : ℕ → X → X) (m : ℕ) (hm : 0 < m) (q : ℕ → X) :
    ((∀ i, i + 1 < m → q (i + 1) = Φ i (q i)) ∧ q 0 = Φ (m - 1) (q (m - 1))) ↔
    ((∀ i, i < m → q i = prefixMap Φ i (q 0)) ∧ q 0 = prefixMap Φ m (q 0)) := by
  sorry

end Monodromy

/-- A permutation of `Fin 5` from the vector of its values and the vector of its inverse. -/
def mk5 (f g : Fin 5 → Fin 5) (h1 : ∀ i, g (f i) = i := by decide)
    (h2 : ∀ i, f (g i) = i := by decide) : Perm (Fin 5) := ⟨f, g, h1, h2⟩

/-- `p = (1 2 3 4 5)` (paper notation), i.e. `0 ↦ 1 ↦ 2 ↦ 3 ↦ 4 ↦ 0`. -/
def pA : Perm (Fin 5) := mk5 ![1,2,3,4,0] ![4,0,1,2,3]
/-- `q = (1 2 3)`. -/
def qA : Perm (Fin 5) := mk5 ![1,2,0,3,4] ![2,0,1,3,4]

/-- The 60 elements of `A₅`, in breadth-first order from `p, q, p⁻¹, q⁻¹, e`. -/
def A5list : List (Perm (Fin 5)) :=
  [mk5 ![1,2,3,4,0] ![4,0,1,2,3],
   mk5 ![1,2,0,3,4] ![2,0,1,3,4],
   mk5 ![4,0,1,2,3] ![1,2,3,4,0],
   mk5 ![2,0,1,3,4] ![1,2,0,3,4],
   mk5 ![0,1,2,3,4] ![0,1,2,3,4],
   mk5 ![2,3,4,0,1] ![3,4,0,1,2],
   mk5 ![2,3,1,4,0] ![4,2,0,1,3],
   mk5 ![3,1,2,4,0] ![4,1,2,0,3],
   mk5 ![2,0,3,4,1] ![1,4,0,2,3],
   mk5 ![4,1,2,0,3] ![3,1,2,4,0],
   mk5 ![0,1,4,2,3] ![0,1,3,4,2],
   mk5 ![3,4,0,1,2] ![2,3,4,0,1],
   mk5 ![1,4,0,2,3] ![2,0,3,4,1],
   mk5 ![0,1,3,4,2] ![0,1,4,2,3],
   mk5 ![4,2,0,1,3] ![2,3,1,4,0],
   mk5 ![3,4,2,0,1] ![3,4,2,0,1],
   mk5 ![4,2,3,0,1] ![3,4,1,2,0],
   mk5 ![3,1,4,0,2] ![3,1,4,0,2],
   mk5 ![0,2,3,1,4] ![0,3,1,2,4],
   mk5 ![1,2,4,0,3] ![3,0,1,4,2],
   mk5 ![0,3,1,2,4] ![0,2,3,1,4],
   mk5 ![0,3,4,1,2] ![0,3,4,1,2],
   mk5 ![0,3,2,4,1] ![0,4,2,1,3],
   mk5 ![3,2,0,4,1] ![2,4,1,0,3],
   mk5 ![3,4,1,2,0] ![4,2,3,0,1],
   mk5 ![2,4,1,0,3] ![3,2,0,4,1],
   mk5 ![1,4,2,3,0] ![4,0,2,3,1],
   mk5 ![3,0,1,4,2] ![1,2,4,0,3],
   mk5 ![4,0,3,1,2] ![1,3,4,2,0],
   mk5 ![4,0,2,3,1] ![1,4,2,3,0],
   mk5 ![1,3,4,2,0] ![4,0,3,1,2],
   mk5 ![1,3,0,4,2] ![2,0,4,1,3],
   mk5 ![2,0,4,1,3] ![1,3,0,4,2],
   mk5 ![0,4,2,1,3] ![0,3,2,4,1],
   mk5 ![2,3,0,1,4] ![2,3,0,1,4],
   mk5 ![1,4,3,0,2] ![3,0,4,2,1],
   mk5 ![4,3,1,0,2] ![3,2,4,1,0],
   mk5 ![3,0,2,1,4] ![1,3,2,0,4],
   mk5 ![2,4,0,3,1] ![2,4,0,3,1],
   mk5 ![3,1,0,2,4] ![2,1,3,0,4],
   mk5 ![1,0,3,2,4] ![1,0,3,2,4],
   mk5 ![3,2,4,1,0] ![4,3,1,0,2],
   mk5 ![1,3,2,0,4] ![3,0,2,1,4],
   mk5 ![4,1,3,2,0] ![4,1,3,2,0],
   mk5 ![4,1,0,3,2] ![2,1,4,3,0],
   mk5 ![4,2,1,3,0] ![4,2,1,3,0],
   mk5 ![2,1,4,3,0] ![4,1,0,3,2],
   mk5 ![0,2,4,3,1] ![0,4,1,3,2],
   mk5 ![3,0,4,2,1] ![1,4,3,0,2],
   mk5 ![2,1,3,0,4] ![3,1,0,2,4],
   mk5 ![0,4,1,3,2] ![0,2,4,3,1],
   mk5 ![4,3,0,2,1] ![2,4,3,1,0],
   mk5 ![2,4,3,1,0] ![4,3,0,2,1],
   mk5 ![0,2,1,4,3] ![0,2,1,4,3],
   mk5 ![1,0,2,4,3] ![1,0,2,4,3],
   mk5 ![4,3,2,1,0] ![4,3,2,1,0],
   mk5 ![3,2,1,0,4] ![3,2,1,0,4],
   mk5 ![1,0,4,3,2] ![1,0,4,3,2],
   mk5 ![0,4,3,2,1] ![0,4,3,2,1],
   mk5 ![2,1,0,4,3] ![2,1,0,4,3]]

/-- The elements of `A₅` as a finset. -/
def A5set : Finset (Perm (Fin 5)) := A5list.toFinset

/-- `D₊(A, B) = {r ∈ A₅ : r = A r B}`. -/
def rootPos (A B : Perm (Fin 5)) : Finset (Perm (Fin 5)) := A5set.filter fun r => r = A * r * B
/-- `D₋(A, B) = {r ∈ A₅ : r = A r⁻¹ B}`. -/
def rootNeg (A B : Perm (Fin 5)) : Finset (Perm (Fin 5)) := A5set.filter fun r => r = A * r⁻¹ * B

/-- **Root domains for `ε = -1`** (004e, Theorem 5.3(ii)): `|D₋(A, B)| ∈ {0, 1, 16}`; it is `16`
exactly when `A = B`, and `0` exactly when `A⁻¹ B` is a double transposition (an element of
order 2). -/
theorem root_domain_neg {A B : Perm (Fin 5)} (hA : A ∈ alternatingGroup (Fin 5))
    (hB : B ∈ alternatingGroup (Fin 5)) :
    ((rootNeg A B).card = 0 ∨ (rootNeg A B).card = 1 ∨ (rootNeg A B).card = 16) ∧
    ((rootNeg A B).card = 16 ↔ A = B) ∧
    ((rootNeg A B).card = 0 ↔ (A⁻¹ * B) * (A⁻¹ * B) = 1 ∧ A⁻¹ * B ≠ 1) := by
  sorry

/-- **Root domains for `ε = 1`** (004e, Theorem 5.3(i)): `|D₊(A, B)| ∈ {0, 3, 4, 5, 60}`; it is
nonzero exactly when `A` is conjugate in `A₅` to `B⁻¹`, it then equals the order of the
centralizer of `B` in `A₅`, and `60` occurs only for `A = B = e`. -/
theorem root_domain_pos {A B : Perm (Fin 5)} (hA : A ∈ alternatingGroup (Fin 5))
    (hB : B ∈ alternatingGroup (Fin 5)) :
    ((rootPos A B).card = 0 ∨ (rootPos A B).card = 3 ∨ (rootPos A B).card = 4 ∨
      (rootPos A B).card = 5 ∨ (rootPos A B).card = 60) ∧
    ((rootPos A B).card ≠ 0 ↔ ∃ r ∈ alternatingGroup (Fin 5), r * B⁻¹ * r⁻¹ = A) ∧
    ((rootPos A B).card ≠ 0 →
      (rootPos A B).card = (A5set.filter fun r => r * B = B * r).card) ∧
    ((rootPos A B).card = 60 ↔ A = 1 ∧ B = 1) := by
  sorry

end GC.A5Programs
