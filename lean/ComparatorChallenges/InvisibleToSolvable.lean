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

open scoped commutatorElement

section

/-- One node of a straight-line program over a group with leaves labelled by `α`. -/
inductive Op (α : Type) where
  | leaf : α → Op α
  | mul : ℕ → ℕ → Op α
  | inv : ℕ → Op α
  deriving DecidableEq, Repr

variable {α β : Type} {G H : Type*} [Group G] [Group H]

/-- The value of one operation, given the values of the earlier nodes. -/
def Op.step (ν : α → G) (vals : List G) : Op α → G
  | .leaf a => ν a
  | .mul i j => vals.getD i 1 * vals.getD j 1
  | .inv i => (vals.getD i 1)⁻¹

/-- The values of all nodes of a program. -/
def evalProg (ν : α → G) (ops : List (Op α)) : List G :=
  ops.foldl (fun vals op => vals ++ [op.step ν vals]) []

/-- The value of node `k`. -/
def val (ν : α → G) (ops : List (Op α)) (k : ℕ) : G := (evalProg ν ops).getD k 1

/-- A program is well formed if every operand is an earlier node. -/
def Op.WF (k : ℕ) : Op α → Prop
  | .leaf _ => True
  | .mul i j => i < k ∧ j < k
  | .inv i => i < k

/-- Every operand of node `k` refers to an earlier node. -/
def WellFormed (ops : List (Op α)) : Prop :=
  ∀ k (h : k < ops.length), (ops[k]'h).WF k

end

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

/-- Terminal values: `P ↦ p`, `Q ↦ q`. -/
def pq : Fin 2 → Perm (Fin 5) := ![pA, qA]

/-- The library: `P, Q, P⁻¹, Q⁻¹, P P⁻¹`, then one product per remaining element along a
breadth-first tree of the Cayley graph. -/
def libOps : List (Op (Fin 2)) :=
  [Op.leaf 0, Op.leaf 1, Op.inv 0, Op.inv 1, Op.mul 0 2, Op.mul 0 0, Op.mul 0 1, Op.mul 0 3, Op.mul 1 0, Op.mul 1 2, Op.mul 2 1, Op.mul 2 2, Op.mul 2 3, Op.mul 3 0, Op.mul 3 2, Op.mul 5 1, Op.mul 5 3, Op.mul 6 0, Op.mul 6 2, Op.mul 7 0, Op.mul 7 2, Op.mul 8 0, Op.mul 8 1, Op.mul 8 3, Op.mul 9 2, Op.mul 9 3, Op.mul 10 0, Op.mul 10 2, Op.mul 11 1, Op.mul 12 0, Op.mul 13 0, Op.mul 13 1, Op.mul 14 1, Op.mul 14 3, Op.mul 16 0, Op.mul 17 1, Op.mul 17 3, Op.mul 18 3, Op.mul 19 0, Op.mul 20 1, Op.mul 20 3, Op.mul 22 0, Op.mul 23 2, Op.mul 24 1, Op.mul 25 0, Op.mul 26 1, Op.mul 26 3, Op.mul 29 1, Op.mul 31 0, Op.mul 31 2, Op.mul 32 0, Op.mul 35 0, Op.mul 36 2, Op.mul 37 0, Op.mul 39 0, Op.mul 41 3, Op.mul 42 1, Op.mul 44 1, Op.mul 48 1, Op.mul 53 1]

/-- Index of an element in the library (`4` is the identity node). -/
def libIdx (g : Perm (Fin 5)) : ℕ := A5list.idxOf g

/-- The constants of a circuit lie in `A₅`. -/
def ConstsInA5 (C : List (Op (Perm (Fin 5)))) : Prop :=
  ∀ g, Op.leaf g ∈ C → g ∈ alternatingGroup (Fin 5)

/-- The free group on the terminals `P, Q`. -/
abbrev F2 := FreeGroup (Fin 2)

/-- Evaluation `P ↦ p`, `Q ↦ q`. -/
def ev : F2 →* Perm (Fin 5) := FreeGroup.lift pq

/-- Every element of `A₅` is a commutator of two elements of `A₅` (Ore; 004b, Section 4). -/
theorem exists_commutator_A5 (g : Perm (Fin 5)) (hg : g ∈ alternatingGroup (Fin 5)) :
    ∃ x ∈ alternatingGroup (Fin 5), ∃ y ∈ alternatingGroup (Fin 5), ⁅x, y⁆ = g := by
  sorry

/-- Existential form of the shared tower (004b, Theorem 4.2 (i), (ii)): every element of `A₅`
has a representative in every term of the derived series of `F(P, Q)`. -/
theorem tower_exists (d : ℕ) : ∀ g ∈ alternatingGroup (Fin 5),
    ∃ w ∈ derivedSeries F2 d, ev w = g := by
  sorry

section Series

variable {G : Type*} [Group G]

/-- **004b, Lemma 2.1**: `G^(d) ≤ γ_{2^d}(G)`. -/
theorem derivedSeries_le_lowerCentralSeries_two_pow (d : ℕ) :
    derivedSeries G d ≤ (⊤ : Subgroup G).lowerCentralSeries (2 ^ d - 1) := by
  sorry

/-- **Shadow annihilation, solvable case** (004b, Theorem 6.1(i)). -/
theorem shadow_solvable {F H : Type*} [Group F] [Group H] (φ : F →* H) {d : ℕ}
    (hH : derivedSeries H d = ⊥) {w : F} (hw : w ∈ derivedSeries F d) : φ w = 1 := by
  sorry

/-- **Shadow annihilation, nilpotent case** (004b, Theorem 6.1(ii)): a nilpotent group of class
less than `2^d` (that is, `γ_{2^d}(H) = 1`) kills `F^(d)`. -/
theorem shadow_nilpotent {F H : Type*} [Group F] [Group H] (φ : F →* H) {d : ℕ}
    (hH : (⊤ : Subgroup H).lowerCentralSeries (2 ^ d - 1) = ⊥) {w : F}
    (hw : w ∈ derivedSeries F d) :
    φ w = 1 := by
  sorry

/-- In a finite solvable group each strict step of the derived series at least halves the
order; hence a finite solvable group of order `< 2^d` has `H^(d) = 1`
(004b, proof of Corollary 6.2 and Remark 6.3(1)). -/
theorem derivedSeries_eq_bot_of_card_lt {H : Type*} [Group H] [Finite H] [Group.IsSolvable H] {d : ℕ}
    (hcard : Nat.card H < 2 ^ d) : derivedSeries H d = ⊥ := by
  sorry

end Series

/-- **No small solvable or nilpotent image can decide** (004b, Theorems 5.1, 6.1, Corollary 6.2,
Remark 6.3(1), combined). For every `A₅` circuit `C` with constants in `A₅` and every `d` there is
a substitution `ν` of the constants by words of `F^(d)` with `ev ∘ ν = id` on `A₅` (the tower
representatives) such that every node `w` of the substituted circuit satisfies: `ev w` is the
value of that node in `C`, while `φ w = 1` for every homomorphism `φ` from `F(P, Q)` to a finite
solvable group of order `< 2^d` and to any group that is nilpotent of class `< 2^d`. -/
theorem deep_core_invisible (C : List (Op (Perm (Fin 5)))) (hC : ConstsInA5 C) (d : ℕ) :
    ∃ ν : Perm (Fin 5) → F2,
      (∀ g ∈ alternatingGroup (Fin 5), ν g ∈ derivedSeries F2 d ∧ ev (ν g) = g) ∧
      ∀ k, ev (val ν C k) = val id C k ∧
      (∀ (H : Type) [Group H] [Finite H] [Group.IsSolvable H], Nat.card H < 2 ^ d →
        ∀ φ : F2 →* H, φ (val ν C k) = 1) ∧
      (∀ (H : Type) [Group H], (⊤ : Subgroup H).lowerCentralSeries (2 ^ d - 1) = ⊥ →
        ∀ φ : F2 →* H, φ (val ν C k) = 1) := by
  sorry

end GC.A5Programs
