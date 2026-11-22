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

/-- Orbit representatives `(x_k, y_k)` of the 19 orbits of generating pairs. -/
def repX : Fin 19 → Perm (Fin 5) := ![mk5 ![1,2,3,4,0] ![4,0,1,2,3],
  mk5 ![1,2,3,4,0] ![4,0,1,2,3],
  mk5 ![1,2,3,4,0] ![4,0,1,2,3],
  mk5 ![1,2,3,4,0] ![4,0,1,2,3],
  mk5 ![1,2,3,4,0] ![4,0,1,2,3],
  mk5 ![1,2,3,4,0] ![4,0,1,2,3],
  mk5 ![1,2,3,4,0] ![4,0,1,2,3],
  mk5 ![1,2,3,4,0] ![4,0,1,2,3],
  mk5 ![1,2,3,4,0] ![4,0,1,2,3],
  mk5 ![1,2,3,4,0] ![4,0,1,2,3],
  mk5 ![1,2,0,3,4] ![2,0,1,3,4],
  mk5 ![1,2,0,3,4] ![2,0,1,3,4],
  mk5 ![1,2,0,3,4] ![2,0,1,3,4],
  mk5 ![1,2,0,3,4] ![2,0,1,3,4],
  mk5 ![1,2,0,3,4] ![2,0,1,3,4],
  mk5 ![1,2,0,3,4] ![2,0,1,3,4],
  mk5 ![3,4,2,0,1] ![3,4,2,0,1],
  mk5 ![3,4,2,0,1] ![3,4,2,0,1],
  mk5 ![3,4,2,0,1] ![3,4,2,0,1]]

def repY : Fin 19 → Perm (Fin 5) := ![mk5 ![1,2,0,3,4] ![2,0,1,3,4],
  mk5 ![2,0,1,3,4] ![1,2,0,3,4],
  mk5 ![2,3,1,4,0] ![4,2,0,1,3],
  mk5 ![1,4,0,2,3] ![2,0,3,4,1],
  mk5 ![3,4,2,0,1] ![3,4,2,0,1],
  mk5 ![0,3,2,4,1] ![0,4,2,1,3],
  mk5 ![3,2,0,4,1] ![2,4,1,0,3],
  mk5 ![2,4,1,0,3] ![3,2,0,4,1],
  mk5 ![0,4,2,1,3] ![0,3,2,4,1],
  mk5 ![1,0,3,2,4] ![1,0,3,2,4],
  mk5 ![1,2,3,4,0] ![4,0,1,2,3],
  mk5 ![4,0,1,2,3] ![1,2,3,4,0],
  mk5 ![2,3,4,0,1] ![3,4,0,1,2],
  mk5 ![3,1,2,4,0] ![4,1,2,0,3],
  mk5 ![3,4,0,1,2] ![2,3,4,0,1],
  mk5 ![3,4,2,0,1] ![3,4,2,0,1],
  mk5 ![1,2,3,4,0] ![4,0,1,2,3],
  mk5 ![1,2,0,3,4] ![2,0,1,3,4],
  mk5 ![2,3,4,0,1] ![3,4,0,1,2]]

/-- `A₅` as a group: the alternating group on five points. -/
abbrev A5 := alternatingGroup (Fin 5)

/-- The free group on the terminals `P, Q`. -/
abbrev F2 := FreeGroup (Fin 2)

section Hall

variable {T : Type*} [Group T] [IsSimpleGroup T]

/-- **P. Hall's theorem** (004c, Theorem 5.2, in general form). If `T` is simple nonabelian and
`(x i, y i)` are generating pairs of `T`, no two related by an automorphism, then `x, y`
generate `T^ι`. -/
theorem hall_generation {ι : Type*} [Finite ι] [DecidableEq ι] (hT : ∃ a b : T, a * b ≠ b * a)
    (x y : ι → T) (hgen : ∀ i, Subgroup.closure {x i, y i} = ⊤)
    (hdist : ∀ i j, i ≠ j → ¬ ∃ φ : T ≃* T, φ (x i) = x j ∧ φ (y i) = y j) :
    Subgroup.closure {x, y} = ⊤ := by
  sorry

end Hall

/-- The pair `(x, y)` generates `A₅`. -/
def IsHot (x y : Perm (Fin 5)) : Prop := Subgroup.closure {x, y} = alternatingGroup (Fin 5)

/-- `(x, y)` is conjugate by an element of `S₅` to the `k`-th representative. -/
def InOrbit (k : Fin 19) (x y : Perm (Fin 5)) : Prop :=
  ∃ σ : Perm (Fin 5), σ * x * σ⁻¹ = repX k ∧ σ * y * σ⁻¹ = repY k

/-- Evaluation of the free group `F(X, Y)` at a pair. -/
def evalPair (x y : Perm (Fin 5)) : F2 →* Perm (Fin 5) := FreeGroup.lift ![x, y]

/-- The elements of `A₅` as a finset. -/
def A5set : Finset (Perm (Fin 5)) := A5list.toFinset

/-- The parametrization of generating pairs by orbit index and conjugating permutation. -/
def orbitParam (p : Fin 19 × Perm (Fin 5)) : Perm (Fin 5) × Perm (Fin 5) :=
  (p.2⁻¹ * repX p.1 * p.2, p.2⁻¹ * repY p.1 * p.2)

open Classical in
/-- **Census of generating pairs** (004c, Table 1 and Section 5): exactly `2280 = 19 · 120`
ordered pairs of elements of `A₅` generate `A₅`; they are the images of the 19 representatives
under conjugation by the 120 elements of `S₅`, each pair exactly once. -/
theorem census_hot :
    ((A5set ×ˢ A5set).filter fun pr => IsHot pr.1 pr.2) = Finset.univ.image orbitParam ∧
    ((A5set ×ˢ A5set).filter fun pr => IsHot pr.1 pr.2).card = 2280 := by
  sorry

open Classical in
/-- Exactly `1320` ordered pairs of elements of `A₅` do not generate `A₅` (004c, Table 1). -/
theorem census_cold :
    ((A5set ×ˢ A5set).filter fun pr => ¬ IsHot pr.1 pr.2).card = 1320 := by
  sorry

/-- **Cold mirrors are blind** (004c, Theorem 6.1). For every target tuple `g ∈ A₅^19` there is a
word `w ∈ F₂''` with `w(x_k, y_k) = g_k` for all 19 representatives and `w(x, y) = e` for every
pair `(x, y) ∈ A₅²` that does not generate `A₅`. -/
theorem mirror_word (g : Fin 19 → Perm (Fin 5)) (hg : ∀ k, g k ∈ alternatingGroup (Fin 5)) :
    ∃ w ∈ derivedSeries F2 2, (∀ k, evalPair (repX k) (repY k) w = g k) ∧
      ∀ x y, x ∈ alternatingGroup (Fin 5) → y ∈ alternatingGroup (Fin 5) → ¬ IsHot x y →
        evalPair x y w = 1 := by
  sorry

/-- **Nineteen mirror selectors** (004c, Corollary 6.2): for each orbit `i` there is a word
`w_i ∈ F₂''` that is not the identity exactly on the pairs of orbit `i`. -/
theorem mirror_selectors (i : Fin 19) : ∃ w ∈ derivedSeries F2 2,
    ∀ x y, x ∈ alternatingGroup (Fin 5) → y ∈ alternatingGroup (Fin 5) →
      (evalPair x y w ≠ 1 ↔ InOrbit i x y) := by
  sorry

/-- **No interpolation from easy rows** (004c, Corollary 6.3). For every word `u`, orbit `i` and
target `h ∈ A₅` there is a word `u'` that agrees with `u` on every pair of `A₅²` outside orbit
`i` (all non-generating pairs and the other 18 orbits) and takes the value `h` on the `i`-th
representative. -/
theorem no_interpolation (u : F2) (i : Fin 19) (h : Perm (Fin 5))
    (hh : h ∈ alternatingGroup (Fin 5)) : ∃ u' : F2,
    evalPair (repX i) (repY i) u' = h ∧
    ∀ x y, x ∈ alternatingGroup (Fin 5) → y ∈ alternatingGroup (Fin 5) → ¬ InOrbit i x y →
      evalPair x y u' = evalPair x y u := by
  sorry

/-- **Power permutations** (004c, Lemma 3.5): `x ↦ x^a` is a permutation of `A₅` exactly when
`a` is prime to 30. -/
theorem pow_bijective_iff (a : ℕ) : Function.Bijective (fun x : A5 => x ^ a) ↔ Nat.Coprime a 30 := by
  sorry

/-- **Unit-power reversibility** (004c, Theorem 3.6), right form. -/
theorem unitPower_R_bijective_iff (a b : ℕ) :
    Function.Bijective (fun p : A5 × A5 => (p.1, p.1 ^ a * p.2 ^ b)) ↔ Nat.Coprime b 30 := by
  sorry

/-- **Unit-power reversibility** (004c, Theorem 3.6), left form. -/
theorem unitPower_L_bijective_iff (a b : ℕ) :
    Function.Bijective (fun p : A5 × A5 => (p.1 ^ a * p.2 ^ b, p.2)) ↔ Nat.Coprime a 30 := by
  sorry

/-- **Noncommutative Fibonacci update** (004c, Corollary 3.3): `T(x, y) = (x y, x)` is a
bijection of `G²` with inverse `(u, v) ↦ (v, v⁻¹ u)`, for every group `G`. -/
theorem fib_update_inverse {G : Type*} [Group G] :
    Function.LeftInverse (fun p : G × G => (p.2, p.2⁻¹ * p.1)) (fun p : G × G => (p.1 * p.2, p.1)) ∧
    Function.RightInverse (fun p : G × G => (p.2, p.2⁻¹ * p.1))
      (fun p : G × G => (p.1 * p.2, p.1)) := by
  sorry

end GC.A5Programs
