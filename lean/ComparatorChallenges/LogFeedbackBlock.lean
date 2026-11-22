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

/-! Comparator challenge: 008d, Logarithmic feedback in SC^2 lies in NC^2 -/

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

open Classical

structure Rec (Q : Type*) (d : ℕ) where
  q : Q
  M : Matrix (Fin d) (Fin d) F
  c : Data d
  guard : Guard d

def Rec.init (u : Q) : Rec Q d := ⟨u, 1, 0, []⟩

def Rec.next (s : Stage Q d) (r : Rec Q d) (z : F) (G : Guard d) : Rec Q d :=
  ⟨s.g r.q z, s.A r.q * r.M, s.A r.q *ᵥ r.c + s.b r.q, G⟩

noncomputable def forced : List (Stage Q d) → Rec Q d → List F → Option (Rec Q d)
  | [], r, [] => some r
  | [], _, _ :: _ => none
  | s :: S, r, τ =>
    if s.Sensitive then
      match τ with
      | [] => none
      | z :: τ' => forced S
          (r.next s z (r.guard ++ [(r.M (s.addr r.q), z - r.c (s.addr r.q))])) τ'
    else forced S (r.next s 0 r.guard) τ

noncomputable def numSensitive : List (Stage Q d) → ℕ
  | [] => 0
  | s :: S => (if s.Sensitive then 1 else 0) + numSensitive S

theorem unique_transcript (S : List (Stage Q d)) (u : Q) (x : Data d) :
    (∃! τ : List F, ∃ r, forced S (Rec.init u) τ = some r ∧ r.guard.Holds x) ∧
    ∀ τ r, forced S (Rec.init u) τ = some r → r.guard.Holds x →
      run S (u, x) = (r.q, r.M *ᵥ x + r.c) := by sorry

theorem card_transcripts (S : List (Stage Q d)) (u : Q) :
    {τ : List F | ∃ r, forced S (Rec.init u) τ = some r}.ncard ≤ 2 ^ numSensitive S ∧
    ∀ τ r, forced S (Rec.init u) τ = some r → r.guard.length = numSensitive S := by sorry

noncomputable def transcriptLeaf (S : List (Stage Q d)) (i : Q × List F) : Leaf Q d :=
  let r := (forced S (Rec.init i.1) i.2).getD (Rec.init i.1)
  ⟨r.guard, r.q, r.M, r.c⟩

def transcriptLeaves (S : List (Stage Q d)) (u : Q) : Set (Q × List F) :=
  {i | i.1 = u ∧ ∃ r, forced S (Rec.init u) i.2 = some r}

theorem transcript_summary_exact (S : List (Stage Q d)) :
    IsExactSummary (fun u x => run S (u, x)) (transcriptLeaves S) (transcriptLeaf S) := by sorry

theorem feedback_free_run (S : List (Stage Q d)) (hS : ∀ s ∈ S, ¬ s.Sensitive) (u : Q) :
    ∃ r : Rec Q d, forced S (Rec.init u) [] = some r ∧
      ∀ x, run S (u, x) = (r.q, r.M *ᵥ x + r.c) := by sorry

end GC.SCLadder
