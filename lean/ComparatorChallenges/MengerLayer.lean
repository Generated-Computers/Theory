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

/-- `f` has minimum rank exactly `k`. -/
def ExactRank (f : α) (k : ℕ) : Prop := f ∈ S.le k ∧ f ∉ S.lt k

/-- The balanced seeds `S_k`: conclusions outside `𝓕_{<k}` of binary rules whose two premises
both have rank exactly `k - 1`. -/
def seeds (k : ℕ) : Set α :=
  {g | g ∉ S.lt k ∧ ∃ f f', S.binary f f' g ∧ S.ExactRank f (k - 1) ∧ S.ExactRank f' (k - 1)}

/-- The arcs of the graph `G(X)`: `f → g` if a rule derives `g` from `f` alone or from `f`
together with one side premise in `X`. -/
def arc (X : Set α) (f g : α) : Prop :=
  S.unary f g ∨ (∃ f' ∈ X, S.binary f f' g) ∨ (∃ f' ∈ X, S.binary f' f g)

/-- Facts reachable in `G(X)` from `A`. -/
def reach (X A : Set α) : Set α := {g | ∃ a ∈ A, Relation.ReflTransGen (S.arc X) a g}

/-- Lemma (rank-layer reachability, 005d): for every `k ≥ 1`,
`𝓕_{≤k} = 𝓕_{<k} ∪ Reach_{G_k}(S_k)`, where `G_k = G(𝓕_{<k})`. -/
theorem rank_layer (k : ℕ) (hk : 1 ≤ k) :
    S.le k = S.lt k ∪ S.reach (S.lt k) (S.seeds k) := by
  sorry

/-- The derivable facts `D`. -/
def derivable : Set α := {f | ∃ r, S.Proves f r}

/-- `H` is a closed boundary of the region `R`: every premise outside `R` of every rule with
conclusion in `R` lies in `H`. -/
def ClosedBoundary (H R : Set α) : Prop :=
  (∀ f g, S.unary f g → g ∈ R → f ∉ R → f ∈ H) ∧
    (∀ f f' g, S.binary f f' g → g ∈ R → (f ∉ R → f ∈ H) ∧ (f' ∉ R → f' ∈ H))

/-- `Y` is closed for the region `R` over `X`: `Y ⊆ R`, and every rule with conclusion in `R`
whose premises lie in `X ∪ Y` has its conclusion in `Y`. -/
def RegionClosed (R X Y : Set α) : Prop :=
  Y ⊆ R ∧ (∀ g ∈ R, S.ax g → g ∈ Y) ∧
    (∀ f g, g ∈ R → S.unary f g → f ∈ X ∪ Y → g ∈ Y) ∧
    (∀ f f' g, g ∈ R → S.binary f f' g → f ∈ X ∪ Y → f' ∈ X ∪ Y → g ∈ Y)

/-- `lfp_R(X)`: the least set closed for the region `R` over `X`. -/
def lfpRegion (R X : Set α) : Set α := ⋂₀ {Y | S.RegionClosed R X Y}

/-- `lfp_R(X)` is itself closed (so it is the least closed set). -/
theorem lfpRegion_closed (R X : Set α) : S.RegionClosed R X (S.lfpRegion R X) := by
  sorry

/-- Lemma (closure determines the region): if `H` is a closed boundary of `R`, then
`D ∩ R = lfp_R(D ∩ H)`. -/
theorem closure_determines_region {H R : Set α} (hH : S.ClosedBoundary H R) :
    S.derivable ∩ R = S.lfpRegion R (S.derivable ∩ H) := by
  sorry

end HornSystem

/-- Facts of the side-premise star: `A`, `B_i`, `C_i`. -/
inductive StarFact (t : ℕ) where
  | A : StarFact t
  | B : Fin t → StarFact t
  | C : Fin t → StarFact t

/-- The side-premise star: `A` is an axiom (it is derivable), `B_i` is an axiom exactly for
`i ∈ P` (its derivability is controlled from outside), and the only rules concluding `C_i` are
`A ∧ B_i ⇒ C_i`. -/
def starSystem (t : ℕ) (P : Set (Fin t)) : HornSystem (StarFact t) where
  ax f := f = StarFact.A ∨ ∃ i ∈ P, f = StarFact.B i
  unary _ _ := False
  binary f f' g := ∃ i, f = StarFact.A ∧ f' = StarFact.B i ∧ g = StarFact.C i

/-- Theorem (side-premise star): the conclusion `C_i` is derivable exactly when `B_i` is, so the
conclusion vector equals the pattern `P`, which ranges over all `2^t` subsets. -/
theorem side_premise_star (t : ℕ) (P : Set (Fin t)) :
    {i | StarFact.C i ∈ (starSystem t P).derivable} = P := by
  sorry

/-- The `2^t` derivability patterns are all realized: the pattern map is injective. -/
theorem side_premise_star_injective (t : ℕ) :
    Function.Injective (fun P : Set (Fin t) => {i | StarFact.C i ∈ (starSystem t P).derivable}) := by
  sorry

end GC.Portals
