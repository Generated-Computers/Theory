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

/-! Comparator challenge: 008a, An SC^k-complete problem with an NC^3 fragment -/

namespace GC.SCLadder

open Module Matrix

abbrev F := ZMod 2

abbrev Data (d : ℕ) := Fin d → F

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

def Stage.step (s : Stage Q d) (c : Q × Data d) : Q × Data d :=
  (s.g c.1 (c.2 (s.addr c.1)), s.A c.1 *ᵥ c.2 + s.b c.1)

def run : List (Stage Q d) → Q × Data d → Q × Data d
  | [], c => c
  | s :: S, c => run S (s.step c)

def Stage.Sensitive (s : Stage Q d) : Prop := ∃ u, s.g u 0 ≠ s.g u 1

abbrev Guard (d : ℕ) := List (Data d × F)

def Guard.Holds (G : Guard d) (x : Data d) : Prop := ∀ p ∈ G, p.1 ⬝ᵥ x = p.2

structure Leaf (Q : Type*) (d : ℕ) where
  guard : Guard d
  q : Q
  M : Matrix (Fin d) (Fin d) F
  c : Data d

def Leaf.exit (l : Leaf Q d) (x : Data d) : Q × Data d := (l.q, l.M *ᵥ x + l.c)

def IsExactAt {ι : Type*} (Φ : Q → Data d → Q × Data d) (u : Q) (Λu : Set ι)
    (leaf : ι → Leaf Q d) : Prop :=
  ∀ x, (∃! i, i ∈ Λu ∧ (leaf i).guard.Holds x) ∧
    ∀ i ∈ Λu, (leaf i).guard.Holds x → Φ u x = (leaf i).exit x

def IsExactSummary {ι : Type*} (Φ : Q → Data d → Q × Data d) (Λ : Q → Set ι)
    (leaf : ι → Leaf Q d) : Prop :=
  ∀ u, IsExactAt Φ u (Λ u) leaf

structure BitMachine (C : Type*) (d : ℕ) where
  head : C → Fin d
  next : C → F → C
  write : C → F → F

variable {C : Type*}

def BitMachine.step (M : BitMachine C d) (c : C × Data d) : C × Data d :=
  (M.next c.1 (c.2 (M.head c.1)),
    Function.update c.2 (M.head c.1) (M.write c.1 (c.2 (M.head c.1))))

def BitMachine.toStage [DecidableEq C] (M : BitMachine C d) : Stage C d where
  addr := M.head
  g := M.next
  A c := diagonal (Function.update (fun _ => (1 : F)) (M.head c) (M.write c 1 - M.write c 0))
  b c := Pi.single (M.head c) (M.write c 0)

lemma BitMachine.toStage_A [DecidableEq C] (M : BitMachine C d) (c : C) :
    (∀ i j, i ≠ j → M.toStage.A c i j = 0) ∧ (∀ i, i ≠ M.head c → M.toStage.A c i i = 1) := by sorry

theorem bitMachine_run [DecidableEq C] (M : BitMachine C d) (T : ℕ) (c : C × Data d) :
    run (List.replicate T M.toStage) c = M.step^[T] c := by sorry

def pairLeaf (l₁ l₂ : Leaf Q d) : Leaf Q d :=
  ⟨l₁.guard ++ l₂.guard.map (fun p => (p.1 ᵥ* l₁.M, p.2 - p.1 ⬝ᵥ l₁.c)), l₂.q, l₂.M * l₁.M,
    l₂.M *ᵥ l₁.c + l₂.c⟩

def pairSet {ι₁ ι₂ : Type*} (Λ₁ : Q → Set ι₁) (Λ₂ : Q → Set ι₂) (leaf₁ : ι₁ → Leaf Q d) (u : Q) :
    Set (ι₁ × ι₂) :=
  {p | p.1 ∈ Λ₁ u ∧ p.2 ∈ Λ₂ (leaf₁ p.1).q}

theorem pair_exact {ι₁ ι₂ : Type*} {Φ₁ Φ₂ : Q → Data d → Q × Data d}
    {Λ₁ : Q → Set ι₁} {Λ₂ : Q → Set ι₂} {leaf₁ : ι₁ → Leaf Q d} {leaf₂ : ι₂ → Leaf Q d}
    (h₁ : IsExactSummary Φ₁ Λ₁ leaf₁) (h₂ : IsExactSummary Φ₂ Λ₂ leaf₂) :
    IsExactSummary (fun u x => Φ₂ (Φ₁ u x).1 (Φ₁ u x).2) (pairSet Λ₁ Λ₂ leaf₁)
      (fun p => pairLeaf (leaf₁ p.1) (leaf₂ p.2)) := by sorry

def syndromeGuard {ρ : ℕ} (B : Matrix (Fin ρ) (Fin d) F) (σ : Fin ρ → F) : Guard d :=
  List.ofFn fun k => (B k, σ k)

noncomputable def syndromeLeaf {ι : Type*} {ρ : ℕ} (Λu : Set ι) (leaf : ι → Leaf Q d)
    (B : Matrix (Fin ρ) (Fin d) F) (hB : Function.Surjective B.mulVec)
    (hex : ∀ x, ∃ i, i ∈ Λu ∧ (leaf i).guard.Holds x) (σ : Fin ρ → F) : Leaf Q d :=
  let i := Classical.choose (hex (Classical.choose (hB σ)))
  ⟨syndromeGuard B σ, (leaf i).q, (leaf i).M, (leaf i).c⟩

theorem recompress_exact {ι : Type*} {ρ : ℕ} {Φ : Q → Data d → Q × Data d} {u : Q} {Λu : Set ι}
    {leaf : ι → Leaf Q d} (h : IsExactAt Φ u Λu leaf) (B : Matrix (Fin ρ) (Fin d) F)
    (hB : Function.Surjective B.mulVec)
    (hrows : ∀ i ∈ Λu, ∀ p ∈ (leaf i).guard, p.1 ∈ Submodule.span F (Set.range B)) :
    IsExactAt Φ u Set.univ (syndromeLeaf Λu leaf B hB (fun x => (h x).1.exists)) ∧
      Fintype.card (Fin ρ → F) = 2 ^ ρ := by sorry

def obsStep {r : ℕ} (B : Matrix (Fin r) (Fin d) F) (η : Q → Fin r → F)
    (Cm : Q → Matrix (Fin r) (Fin r) F) (s : Stage Q d) (c : Q × (Fin r → F)) : Q × (Fin r → F) :=
  (s.g c.1 (η c.1 ⬝ᵥ c.2), Cm c.1 *ᵥ c.2 + B *ᵥ s.b c.1)

def obsRun {r : ℕ} (B : Matrix (Fin r) (Fin d) F) (η : Stage Q d → Q → Fin r → F)
    (Cm : Stage Q d → Q → Matrix (Fin r) (Fin r) F) :
    List (Stage Q d) → Q × (Fin r → F) → Q × (Fin r → F)
  | [], c => c
  | s :: S, c => obsRun B η Cm S (obsStep B (η s) (Cm s) s c)

theorem invariant_observation_run {r : ℕ} (B : Matrix (Fin r) (Fin d) F)
    (η : Stage Q d → Q → Fin r → F) (Cm : Stage Q d → Q → Matrix (Fin r) (Fin r) F)
    (S : List (Stage Q d)) (hη : ∀ s ∈ S, ∀ u, η s u ᵥ* B = Pi.single (s.addr u) 1)
    (hC : ∀ s ∈ S, ∀ u, B * s.A u = Cm s u * B) (c : Q × Data d) :
    obsRun B η Cm S (c.1, B *ᵥ c.2) = ((run S c).1, B *ᵥ (run S c).2) := by sorry

end GC.SCLadder
