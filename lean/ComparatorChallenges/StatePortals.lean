import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Cases
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Order.Lattice.Nat
import Mathlib.Logic.Relation
import Mathlib.Data.Finset.Sort
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Analysis.Convex.SpecificFunctions.Basic


namespace GC.Portals

/-- Horton–Strahler combination of the ranks of the two premises of a binary rule. -/
def strahler (r₁ r₂ : ℕ) : ℕ := if r₁ = r₂ then r₁ + 1 else max r₁ r₂

/-- A Horn system with rules of arity at most two on the fact universe `α`. -/
structure HornSystem (α : Type*) where
  /-- rules without premises -/
  ax : α → Prop
  /-- `unary f g`: a rule deriving `g` from `f` -/
  unary : α → α → Prop
  /-- `binary f f' g`: a rule deriving `g` from `f` and `f'` -/
  binary : α → α → α → Prop

namespace HornSystem

variable {α : Type*} (S : HornSystem α)

/-- `S.Proves f r`: the fact `f` has a proof of Horton–Strahler rank `r`. -/
inductive Proves : α → ℕ → Prop
  | ax {f : α} : S.ax f → Proves f 0
  | unary {f g : α} {r : ℕ} : S.unary f g → Proves f r → Proves g r
  | binary {f f' g : α} {r r' : ℕ} :
      S.binary f f' g → Proves f r → Proves f' r' → Proves g (strahler r r')

/-- `𝓕_{≤k}`: facts with a proof of rank at most `k`. -/
def le (k : ℕ) : Set α := {f | ∃ r ≤ k, S.Proves f r}

/-- `𝓕_{<k}`: facts with a proof of rank less than `k`. -/
def lt (k : ℕ) : Set α := {f | ∃ r < k, S.Proves f r}

/-- The arcs of the graph `G(X)`: `f → g` if a rule derives `g` from `f` alone or from `f`
together with one side premise in `X`. -/
def arc (X : Set α) (f g : α) : Prop :=
  S.unary f g ∨ (∃ f' ∈ X, S.binary f f' g) ∨ (∃ f' ∈ X, S.binary f' f g)

/-- Facts reachable in `G(X)` from `A`. -/
def reach (X A : Set α) : Set α := {g | ∃ a ∈ A, Relation.ReflTransGen (S.arc X) a g}

/-- `Seed(X)`: conclusions of binary rules with both premises in `X`. -/
def seedsOf (X : Set α) : Set α := {g | ∃ f ∈ X, ∃ f' ∈ X, S.binary f f' g}

/-- The rank-layer map `Φ(X) = Reach_{G(X)}(X ∪ Seed(X))`. -/
def layerMap (X : Set α) : Set α := S.reach X (X ∪ S.seedsOf X)

/-- `Φ` is monotone (it is computed by a monotone circuit). -/
theorem layerMap_mono : Monotone S.layerMap := by
  sorry

/-- Theorem (rank-layer symbolic transfer): `Φ(𝓕_{<k}) = 𝓕_{≤k}` for every `k ≥ 1`. -/
theorem layerMap_lt (k : ℕ) (hk : 1 ≤ k) : S.layerMap (S.lt k) = S.le k := by
  sorry

/-- Corollary (a band of `B` ranks): `Φ^B(𝓕_{<k}) = 𝓕_{≤k+B-1}` for `k, B ≥ 1`. -/
theorem layerMap_iterate (k B : ℕ) (hk : 1 ≤ k) (hB : 1 ≤ B) :
    S.layerMap^[B] (S.lt k) = S.le (k + B - 1) := by
  sorry

end HornSystem

section Capacity

variable {G : Type*} [Group G] [DecidableEq G]

/-- The fixed function `M(x, y) = e` if `x = e`, and `y` otherwise. -/
def portalM (x y : G) : G := if x = 1 then 1 else y

/-- Theorem (full-capacity portal) (iv): every vector of `G^t` is an output vector. -/
theorem full_capacity_portal [Nontrivial G] (t : ℕ) (v : Fin t → G) :
    ∃ (x : G) (y : Fin t → G), (fun i => portalM x (y i)) = v := by
  sorry

/-- Proposition (hard-coefficient capacity switch). -/
theorem capacity_switch [Fintype G] (t : ℕ) (x : G) :
    (Finset.univ.image (fun y : Fin t → G => fun i => portalM x (y i))).card =
      if x = 1 then 1 else Fintype.card G ^ t := by
  sorry

/-- The capacity switch for `A₅`: one state if `x = e`, `60^t` states otherwise. -/
theorem a5_capacity_switch (t : ℕ) (x : alternatingGroup (Fin 5)) :
    (Finset.univ.image (fun y : Fin t → alternatingGroup (Fin 5) => fun i => portalM x (y i))).card
      = if x = 1 then 1 else 60 ^ t := by
  sorry

end Capacity

/-- The one-rule Horn system `0 ⇒ 1` on two facts. -/
def oneRule : HornSystem (Fin 2) where
  ax _ := False
  unary f g := f = 0 ∧ g = 1
  binary _ _ _ := False

/-- The source's map to the newly derivable facts, `X ↦ Φ(X) \ X`, is not monotone. -/
theorem newly_derivable_not_monotone :
    ¬ Monotone (fun X : Set (Fin 2) => oneRule.layerMap X \ X) := by
  sorry

/-- The search of Corollary "One-shot criterion" (005c) and Corollary "Searching for the best
rank" (005e): after rank `K` it knows `β_K = min_{K' ≤ K} (K' + c K')` and stops at the first `K`
with `β_K ≤ K`. The first stopping rank is at most `Φ = min_K (K + c K)`. -/
theorem search_first_stop_le (c : ℕ → ℕ) (K₀ : ℕ)
    (hfirst : ∀ K < K₀, ¬ ∃ K' ≤ K, K' + c K' ≤ K) :
    K₀ ≤ sInf (Set.range fun K => K + c K) := by
  sorry

end GC.Portals
