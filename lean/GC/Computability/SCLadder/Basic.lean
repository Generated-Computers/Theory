import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Shared definitions for the SC-ladder family (manuscripts 008a–008e)

* `F` is the two-element field `ZMod 2` (written `𝔽₂` in the papers).
* `dotOrth W` is the orthogonal complement of a subspace `W ⊆ F^n` for the standard dot product.
* `finrank_add_finrank_dotOrth`: `dim W + dim W^⊥ = n`.
-/

namespace GC.SCLadder

/-- The field with two elements. -/
abbrev F := ZMod 2

open Module Matrix

section DotOrth

variable {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]

/-- The dot product as a bilinear form on `n → K`. -/
noncomputable def dotForm (K n : Type*) [Field K] [Fintype n] [DecidableEq n] :
    LinearMap.BilinForm K (n → K) :=
  (dotProductEquiv K n).toLinearMap

@[simp] lemma dotForm_apply (x y : n → K) : dotForm K n x y = x ⬝ᵥ y := rfl

/-- The orthogonal complement for the standard dot product. -/
noncomputable def dotOrth (W : Submodule K (n → K)) : Submodule K (n → K) :=
  (dotForm K n).orthogonal W

lemma mem_dotOrth {W : Submodule K (n → K)} {y : n → K} :
    y ∈ dotOrth W ↔ ∀ x ∈ W, x ⬝ᵥ y = 0 := by
  simp [dotOrth, LinearMap.BilinForm.mem_orthogonal_iff]

lemma finrank_add_finrank_dotOrth (W : Submodule K (n → K)) :
    finrank K W + finrank K (dotOrth W) = Fintype.card n := by
  have h := LinearMap.BilinForm.finrank_add_finrank_orthogonal' (B := dotForm K n) W
  have hker : LinearMap.ker (dotForm K n) = ⊥ := by
    rw [dotForm, LinearEquiv.ker]
  rw [hker, inf_bot_eq, finrank_bot, add_zero, Module.finrank_fintype_fun_eq_card] at h
  exact h

end DotOrth

/-! ## Syndromes -/

/-- A linear form in the row space of `B` depends only on the syndrome `B x`. -/
lemma dotProduct_eq_of_mem_span {ρ d : ℕ} (B : Matrix (Fin ρ) (Fin d) F) {a : Fin d → F}
    (ha : a ∈ Submodule.span F (Set.range B)) {x y : Fin d → F} (h : B *ᵥ x = B *ᵥ y) :
    a ⬝ᵥ x = a ⬝ᵥ y := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨k, rfl⟩ := ha
    exact congrFun h k
  | zero => simp
  | add a a' _ _ h₁ h₂ => rw [add_dotProduct, add_dotProduct, h₁, h₂]
  | smul t a _ h₁ => rw [smul_dotProduct, smul_dotProduct, h₁]

/-- A matrix whose rows lie in the row space of `D` takes equal values on vectors with equal
`D`-syndrome. -/
lemma mulVec_eq_of_rows_mem_span {ρ k d : ℕ} (D : Matrix (Fin ρ) (Fin d) F)
    (E : Matrix (Fin k) (Fin d) F) (hE : ∀ i, E i ∈ Submodule.span F (Set.range D))
    {x y : Fin d → F} (h : D *ᵥ x = D *ᵥ y) : E *ᵥ x = E *ᵥ y :=
  funext fun i => dotProduct_eq_of_mem_span D (hE i) h

/-! ## Single-Probe Affine Iteration (SPAI)

An instance has controller states `Q`, a data vector `v ∈ 𝔽₂^d` and stages `t = 0, …, T-1`:
`z_t = (v_t)_{a_t(u_t)}`, `u_{t+1} = g_t(u_t, z_t)`, `v_{t+1} = A_{t,u_t} v_t + b_{t,u_t}`. -/

/-- Data vectors `𝔽₂^d`. -/
abbrev Data (d : ℕ) := Fin d → F

/-- One stage of a (stage-dependent) SPAI instance. -/
structure Stage (Q : Type*) (d : ℕ) where
  /-- probe address `a_t(u)` -/
  addr : Q → Fin d
  /-- controller update `g_t(u, ·)` -/
  g : Q → F → Q
  /-- data matrix `A_{t,u}` -/
  A : Q → Matrix (Fin d) (Fin d) F
  /-- data offset `b_{t,u}` -/
  b : Q → Data d

variable {Q : Type*} {d : ℕ}

/-- One step `(u, v) ↦ (g(u, v_{a(u)}), A_u v + b_u)`. -/
def Stage.step (s : Stage Q d) (c : Q × Data d) : Q × Data d :=
  (s.g c.1 (c.2 (s.addr c.1)), s.A c.1 *ᵥ c.2 + s.b c.1)

/-- The run of a list of stages: `Φ_I(u, x)` in the papers. -/
def run : List (Stage Q d) → Q × Data d → Q × Data d
  | [], c => c
  | s :: S, c => run S (s.step c)

@[simp] lemma run_nil (c : Q × Data d) : run [] c = c := rfl
@[simp] lemma run_cons (s : Stage Q d) (S : List (Stage Q d)) (c : Q × Data d) :
    run (s :: S) c = run S (s.step c) := rfl

lemma run_append (S₁ S₂ : List (Stage Q d)) (c : Q × Data d) :
    run (S₁ ++ S₂) c = run S₂ (run S₁ c) := by
  induction S₁ generalizing c with
  | nil => rfl
  | cons s S ih => exact ih _

/-- A stage is feedback-sensitive if `g_t(u,0) ≠ g_t(u,1)` for some `u`. -/
def Stage.Sensitive (s : Stage Q d) : Prop := ∃ u, s.g u 0 ≠ s.g u 1

lemma F_cases (z : F) : z = 0 ∨ z = 1 := by
  fin_cases z
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma Stage.g_eq_of_not_sensitive {s : Stage Q d} (h : ¬ s.Sensitive) (u : Q) (z : F) :
    s.g u z = s.g u 0 := by
  rcases F_cases z with rfl | rfl
  · rfl
  · by_contra h'
    exact h ⟨u, Ne.symm h'⟩

/-! ## Affine guards, leaves and exact summaries -/

/-- An affine guard: a list of equations `ℓ ⬝ x = r`. -/
abbrev Guard (d : ℕ) := List (Data d × F)

/-- The guard holds at `x`. -/
def Guard.Holds (G : Guard d) (x : Data d) : Prop := ∀ p ∈ G, p.1 ⬝ᵥ x = p.2

lemma Guard.holds_append {G G' : Guard d} {x : Data d} :
    (G ++ G').Holds x ↔ G.Holds x ∧ G'.Holds x := by
  simp only [Guard.Holds, List.mem_append]
  constructor
  · intro h; exact ⟨fun p hp => h p (Or.inl hp), fun p hp => h p (Or.inr hp)⟩
  · rintro ⟨h1, h2⟩ p (hp | hp)
    · exact h1 p hp
    · exact h2 p hp

/-- A leaf of an affine decision summary: a guard, an exit state and an exit map
`x ↦ M x + c`. -/
structure Leaf (Q : Type*) (d : ℕ) where
  guard : Guard d
  q : Q
  M : Matrix (Fin d) (Fin d) F
  c : Data d

/-- The exit of a leaf at `x`. -/
def Leaf.exit (l : Leaf Q d) (x : Data d) : Q × Data d := (l.q, l.M *ᵥ x + l.c)

/-- Exactness at one entering state `u`: exactly one leaf `i ∈ Λu` has its guard satisfied by `x`,
and for every leaf whose guard is satisfied, `Φ u x` is the exit of that leaf at `x`. -/
def IsExactAt {ι : Type*} (Φ : Q → Data d → Q × Data d) (u : Q) (Λu : Set ι)
    (leaf : ι → Leaf Q d) : Prop :=
  ∀ x, (∃! i, i ∈ Λu ∧ (leaf i).guard.Holds x) ∧
    ∀ i ∈ Λu, (leaf i).guard.Holds x → Φ u x = (leaf i).exit x

/-- Definition `def:summary` (008a): a summary with leaves `leaf i`, `i ∈ Λ u`, is *exact* for
`Φ` if for every `u` and `x` exactly one leaf of `Λ u` has its guard satisfied by `x`, and for that
leaf `Φ u x` is the exit of the leaf at `x`. -/
def IsExactSummary {ι : Type*} (Φ : Q → Data d → Q × Data d) (Λ : Q → Set ι)
    (leaf : ι → Leaf Q d) : Prop :=
  ∀ u, IsExactAt Φ u (Λ u) leaf

end GC.SCLadder
