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

/-- Chord offsets of the LCF code `[-5,-2,-4,2,5,-2,2,5,-2,-5,4,2]`, modulo 12. -/
def fruchtOff : Fin 12 → Fin 12 := ![7, 10, 8, 2, 5, 10, 2, 5, 10, 7, 4, 2]

/-- Neighbors: the two cycle neighbors and the chord. -/
def fruchtNbrs (v : Fin 12) : List (Fin 12) := [v + 1, v + 11, v + fruchtOff v]

/-- Adjacency of the Frucht graph. -/
def fruchtAdj (u v : Fin 12) : Prop := v ∈ fruchtNbrs u

instance : DecidableRel fruchtAdj := fun u v => inferInstanceAs (Decidable (v ∈ fruchtNbrs u))

theorem fruchtAdj_symm : ∀ u v, fruchtAdj u v → fruchtAdj v u := by decide
theorem fruchtAdj_irrefl : ∀ v, ¬ fruchtAdj v v := by decide
theorem fruchtNbrs_nodup : ∀ v, (fruchtNbrs v).Nodup := by decide

/-- The Frucht graph. -/
def fruchtGraph : SimpleGraph (Fin 12) where
  Adj := fruchtAdj
  symm := ⟨fun u v h => fruchtAdj_symm u v h⟩
  loopless := ⟨fun v h => fruchtAdj_irrefl v h⟩

instance : DecidableRel fruchtGraph.Adj := inferInstanceAs (DecidableRel fruchtAdj)

/-- The Frucht graph is cubic. -/
theorem frucht_cubic : ∀ v, fruchtGraph.degree v = 3 := by
  sorry

/-- **The Frucht graph is asymmetric**: its only automorphism is the identity. -/
theorem frucht_asymmetric (φ : fruchtGraph ≃g fruchtGraph) : ∀ v, φ v = v := by
  sorry

/-- The 18 edges of the Frucht graph. -/
def fruchtEdge : Fin 18 → Fin 12 × Fin 12 :=
  ![(0, 1), (0, 7), (0, 11), (1, 2), (1, 11), (2, 3), (2, 10), (3, 4), (3, 5), (4, 5), (4, 9),
    (5, 6), (6, 7), (6, 8), (7, 8), (8, 9), (9, 10), (10, 11)]

/-- Incidence of a vertex and an edge. -/
def inc (v : Fin 12) (e : Fin 18) : Prop := v = (fruchtEdge e).1 ∨ v = (fruchtEdge e).2

instance (v : Fin 12) (e : Fin 18) : Decidable (inc v e) := by unfold inc; infer_instance

/-- Adjacency of the incidence graph `I(Φ)`: vertex-nodes `inl v`, edge-nodes `inr e`. -/
def incAdj : Fin 12 ⊕ Fin 18 → Fin 12 ⊕ Fin 18 → Prop
  | .inl v, .inr e => inc v e
  | .inr e, .inl v => inc v e
  | _, _ => False

instance : DecidableRel incAdj := fun x y => by
  cases x <;> cases y <;> unfold incAdj <;> infer_instance

/-- The incidence graph of the Frucht graph. -/
def incGraph : SimpleGraph (Fin 12 ⊕ Fin 18) where
  Adj := incAdj
  symm := ⟨by intro x y h; cases x <;> cases y <;> simp_all [incAdj]⟩
  loopless := ⟨by intro x h; cases x <;> simp_all [incAdj]⟩

instance : DecidableRel incGraph.Adj := inferInstanceAs (DecidableRel incAdj)

/-- The initial coloring: vertex-nodes and edge-nodes. -/
def incColor (x : Fin 12 ⊕ Fin 18) : Bool := x.isLeft

/-- One round of color refinement: own color and the multiset of neighbor colors. -/
def refineRound {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → Bool)
    (x : V) : Bool × Multiset Bool :=
  (c x, (Finset.univ.filter (G.Adj x)).val.map c)

/-- **Stable colors** (004h, Theorem 3.1, first part): one round of color refinement on the
colored incidence graph induces the same partition as the initial coloring (12 vertex-nodes,
18 edge-nodes); the refinement is stable immediately. -/
theorem incidence_refinement_stable (x y : Fin 12 ⊕ Fin 18) :
    refineRound incGraph incColor x = refineRound incGraph incColor y ↔
      incColor x = incColor y := by
  sorry

/-- **No nontrivial color-preserving automorphism** (004h, Theorem 3.1, second part). -/
theorem incidence_rigid (τ : incGraph ≃g incGraph) (hτ : ∀ x, incColor (τ x) = incColor x) :
    ∀ x, τ x = x := by
  sorry

/-- Tuples of `q = n + 1` records, rotated by `Fin (n + 1)`. -/
def Necklace (n : ℕ) (D : Type*) := Fin (n + 1) → D

instance (n : ℕ) (D : Type*) : AddAction (Fin (n + 1)) (Necklace n D) where
  vadd j x := fun i => x (i + j)
  zero_vadd x := by funext i; show x (i + 0) = x i; rw [add_zero]
  add_vadd j k x := by funext i; show x (i + (j + k)) = x (i + j + k); rw [add_assoc]

instance (n : ℕ) (D : Type*) [Fintype D] : Fintype (Necklace n D) :=
  inferInstanceAs (Fintype (Fin (n + 1) → D))

open Classical in
/-- **Transitive action with many orbits** (004h, Theorem 4.1). Rotations act transitively on
the `q = n + 1` positions, yet the number of orbits on `D^q` is at least `|D|^q / q`:
`|D|^q ≤ q · #orbits`. -/
theorem rotation_orbits_ge (n : ℕ) (D : Type*) [Fintype D] :
    (∀ i i' : Fin (n + 1), ∃ j : Fin (n + 1), i + j = i') ∧
    Fintype.card D ^ (n + 1) ≤
      (n + 1) * Fintype.card (AddAction.orbitRel.Quotient (Fin (n + 1)) (Necklace n D)) := by
  sorry

/-- Group terms in `k` variables with constants from `G`. -/
inductive GTerm (G : Type*) (k : ℕ) where
  | var : Fin k → GTerm G k
  | const : G → GTerm G k
  | mul : GTerm G k → GTerm G k → GTerm G k
  | inv : GTerm G k → GTerm G k

section MaurerRhodesTerms

variable {G : Type*} [Group G] {k : ℕ}

/-- Evaluation of a group term. -/
def GTerm.eval : GTerm G k → (Fin k → G) → G
  | .var i, x => x i
  | .const g, _ => g
  | .mul s t, x => s.eval x * t.eval x
  | .inv t, x => (t.eval x)⁻¹

/-- A function `G^k → G` is polynomial if some group term with constants computes it. -/
def IsPolynomial (f : (Fin k → G) → G) : Prop := ∃ t : GTerm G k, ∀ x, t.eval x = f x

end MaurerRhodesTerms

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

/-- `A₅` as a group: the alternating group on five points. -/
abbrev A5 := alternatingGroup (Fin 5)

/-- The shell `F_g(x)_i = M(g, x_i)`. -/
def shell (M : GTerm A5 2) (g : A5) {q : ℕ} (x : Fin q → A5) : Fin q → A5 :=
  fun i => M.eval ![g, x i]

/-- **Symmetric shell with a hard coefficient** (004h, Theorem 5.1). With the selector `M`,
the block `F_g` is equivariant under every permutation of the records, its response is the
constant `e` when `g = e` and the identity when `g ≠ e`. -/
theorem symmetric_shell : ∃ M : GTerm A5 2,
    (∀ (g : A5) (q : ℕ) (τ : Perm (Fin q)) (x : Fin q → A5),
      shell M g (x ∘ τ) = shell M g x ∘ τ) ∧
    (∀ (q : ℕ) (x : Fin q → A5), shell M 1 x = 1) ∧
    (∀ g : A5, g ≠ 1 → ∀ (q : ℕ) (x : Fin q → A5), shell M g x = x) := by
  sorry

/-- **Swap-forest generation** (004h, Theorem 6.4, connected case; Lemma 6.3 supplies the
hypothesis from certified transpositions). If a record block `B` is equivariant under the
transpositions along the edges of a connected graph on the `q` records, it is equivariant under
every permutation of the records. -/
theorem swap_forest {q : ℕ} {E Cf : Type*} (B : Cf → (Fin q → E) → (Fin q → E))
    (G : SimpleGraph (Fin q)) (hconn : G.Connected)
    (hswap : ∀ i j, G.Adj i j → ∀ c x, B c (x ∘ Equiv.swap i j) = B c x ∘ Equiv.swap i j) :
    ∀ τ : Perm (Fin q), ∀ c x, B c (x ∘ τ) = B c x ∘ τ := by
  sorry

end GC.A5Programs
