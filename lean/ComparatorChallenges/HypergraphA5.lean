import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Cases
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Finset.Sort
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Analysis.Convex.SpecificFunctions.Basic


namespace GC.Portals

section Hypergraph

variable {G : Type*} [Group G] [DecidableEq G]

set_option linter.unusedSectionVars false

/-- The colliding pairs `i < j` with `z i = z j` of a block of `k` values. -/
def collisions {k : ℕ} (z : Fin k → G) : Finset (Fin k × Fin k) :=
  Finset.univ.filter (fun p => p.1 < p.2 ∧ z p.1 = z p.2)

/-- A collision selector: for every `g` the block `(T i g)_i` has exactly one colliding pair,
and the set of colliding pairs determines `g`. -/
def IsSelector {k : ℕ} (T : Fin k → G → G) : Prop :=
  (∀ g, (collisions (fun i => T i g)).card = 1) ∧
    Function.Injective (fun g => collisions (fun i => T i g))

/-- The product `a_e = h_{i₁} ⋯ h_{i_r}` of the anchors of the edge `e = {i₁ < ⋯ < i_r}`. -/
def edgeProduct {t : ℕ} (e : Finset (Fin t)) (h : Fin t → G) : G :=
  ((e.sort (· ≤ ·)).map h).prod

/-- The colliding pairs of the selector block of the edge `e`: the function `F_e`. -/
def blockCollisions {k t : ℕ} (T : Fin k → G → G) (e : Finset (Fin t)) (h : Fin t → G) :
    Finset (Fin k × Fin k) :=
  collisions (fun i => T i (edgeProduct e h))

/-- Anchor `i` is essential for `F` if two assignments that differ only at `i` give different
values of `F`. -/
def Essential {t : ℕ} {β : Type*} (F : (Fin t → G) → β) (i : Fin t) : Prop :=
  ∃ h h' : Fin t → G, (∀ j, j ≠ i → h j = h' j) ∧ F h ≠ F h'

/-- The probes of the explicit selector: `T₀ = id` and `T_{j+1}` is the constant `σ⁻¹ j`. -/
def probe {n : ℕ} (σ : G ≃ Fin n) (i : Fin (n + 1)) (g : G) : G :=
  Fin.cases g (fun j => σ.symm j) i

/-- Lemma (collision selector) for an arbitrary finite group with `n` elements: `n + 1` probes,
each the identity or a constant. -/
theorem selector_exists {n : ℕ} (σ : G ≃ Fin n) :
    IsSelector (probe σ) ∧ ∀ i, probe σ i = id ∨ ∃ c, probe σ i = fun _ => c := by
  sorry

/-- Lemma (61-probe collision selector) for `A₅`. -/
theorem a5_selector :
    ∃ T : Fin 61 → alternatingGroup (Fin 5) → alternatingGroup (Fin 5),
      IsSelector T ∧ ∀ i, T i = id ∨ ∃ c, T i = fun _ => c := by
  sorry

/-- Theorem (arbitrary support-hypergraph realization). -/
theorem realization {k t : ℕ} [Nontrivial G] (T : Fin k → G → G) (hT : IsSelector T)
    (e : Finset (Fin t)) :
    (∀ h, (blockCollisions T e h).card = 1) ∧
    (∀ h h', blockCollisions T e h = blockCollisions T e h' →
      edgeProduct e h = edgeProduct e h') ∧
    (∀ i, Essential (blockCollisions T e) i ↔ i ∈ e) := by
  sorry

/-- Theorem (star-transversal barrier) (i): in the star `e = {0, i}`, for every fixed context,
the colliding pair of the block takes `|G|` distinct values as `h_i` varies. -/
theorem star_block_values [Fintype G] {k t : ℕ} {T : Fin k → G → G} (hT : IsSelector T)
    (i₀ i : Fin t) (h : Fin t → G) :
    (Finset.univ.image (fun x => blockCollisions T {i₀, i} (Function.update h i x))).card =
      Fintype.card G := by
  sorry

end Hypergraph

/-- Lemma (charging). Phases on integer sizes `n = x₀ > x₁ > ⋯ > x_k ≥ 1`: phase `i + 1` has depth
`D (i+1) > 0` and reduces the size from `x i` to at most `x i - D (i+1) · (x i)^ε / λ`. Then there
are fewer than `n` reducing phases and their total depth is at most `λ n^{1-ε} / (1 - ε)`; adding
the final phase of depth `D₀` gives the paper's bound. -/
theorem charging (ε lam D₀ : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hlam : 0 < lam) (n k : ℕ)
    (x : ℕ → ℕ) (D : ℕ → ℝ) (hx0 : x 0 = n) (hpos : ∀ i ≤ k, 1 ≤ x i)
    (hD : ∀ i < k, 0 < D (i + 1))
    (hstep : ∀ i < k, (x (i + 1) : ℝ) ≤ x i - D (i + 1) * (x i : ℝ) ^ ε / lam) :
    k < n ∧ ∑ i ∈ Finset.range k, D (i + 1) + D₀ ≤ lam * (n : ℝ) ^ (1 - ε) / (1 - ε) + D₀ := by
  sorry

end GC.Portals
