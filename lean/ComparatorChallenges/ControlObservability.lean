import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Cases
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Data.ZMod.Basic


namespace GC.Portals

open Matrix

/-- Horton–Strahler combination of the ranks of the two premises of a binary rule. -/
def strahler (r₁ r₂ : ℕ) : ℕ := if r₁ = r₂ then r₁ + 1 else max r₁ r₂

/-- An affine history machine with `d` rational registers and control set `Q`. -/
structure AffineMachine (d : ℕ) (Q : Type*) where
  cp : Fin d → ℚ
  cz : Fin d → ℚ
  cw : Fin d → ℚ
  u : Fin d → ℚ
  A : Q → Bool → Matrix (Fin d) (Fin d) ℚ
  a : Q → Bool → Fin d → ℚ
  δ : Q → Bool → Q

/-- A configuration: control state, register vector and history (cells beyond the current
length are irrelevant). -/
structure Cfg (d : ℕ) (Q : Type*) where
  q : Q
  x : Fin d → ℚ
  H : ℕ → ℚ

/-- `r` is a valid address of a history of length `len`: a natural number below `len`. -/
def ValidAddr (len : ℕ) (r : ℚ) : Prop := ((⌊r⌋₊ : ℕ) : ℚ) = r ∧ ⌊r⌋₊ < len

instance (len : ℕ) (r : ℚ) : Decidable (ValidAddr len r) := by
  unfold ValidAddr; infer_instance

/-- Reading the history at a rational address (`0` for an invalid address). -/
def readAt (H : ℕ → ℚ) (len : ℕ) (r : ℚ) : ℚ := if ValidAddr len r then H ⌊r⌋₊ else 0

namespace AffineMachine

variable {d : ℕ} {Q : Type*} (M : AffineMachine d Q) (m : ℕ)

/-- The address computed from a configuration. -/
def addr (c : Cfg d Q) : ℚ := M.cp ⬝ᵥ c.x

/-- The branch bit computed from a configuration. -/
def branch (c : Cfg d Q) : Bool := decide (0 < M.cz ⬝ᵥ c.x)

/-- Step `t` of the machine (with initial history `H[0..m]`), applied to the configuration
after step `t - 1`. -/
def step (t : ℕ) (c : Cfg d Q) : Cfg d Q where
  q := M.δ c.q (M.branch c)
  x := M.A c.q (M.branch c) *ᵥ c.x + readAt c.H (m + t) (M.addr c) • M.u + M.a c.q (M.branch c)
  H := Function.update c.H (m + t) (M.cw ⬝ᵥ c.x)

/-- The address read at step `t + 1` of the execution `X`, as a natural number. -/
def readAddr (X : ℕ → Cfg d Q) (t : ℕ) : ℕ := ⌊M.addr (X t)⌋₊

/-- A closure for the (exact) trace of `X` on the interval `I = {a + 1, …, b}`
(conditions (C1)–(C3); the condition for step `t + 1 ∈ I` is stated for `a ≤ t < b`). -/
structure IsClosure (X : ℕ → Cfg d Q) (a b : ℕ) (L : ℕ → Submodule ℚ (Fin d → ℚ)) : Prop where
  c1p : ∀ t, a ≤ t → t < b → M.cp ∈ L t
  c1z : ∀ t, a ≤ t → t < b → M.cz ∈ L t
  c2 : ∀ t, a ≤ t → t < b → ∀ ℓ ∈ L (t + 1), ℓ ᵥ* M.A (X t).q (M.branch (X t)) ∈ L t
  c3 : ∀ t, a ≤ t → t < b → m + a < M.readAddr X t → (∃ ℓ ∈ L (t + 1), ℓ ⬝ᵥ M.u ≠ 0) →
    M.cw ∈ L (M.readAddr X t - m - 1)

/-- The read at step `t + 1` is demanded: it lies in `I`, it is internal to `I`, and some
`ℓ ∈ L_{t+1}` has `ℓ u ≠ 0`. -/
def Demanded (X : ℕ → Cfg d Q) (a b : ℕ) (L : ℕ → Submodule ℚ (Fin d → ℚ)) (t : ℕ) : Prop :=
  a ≤ t ∧ t < b ∧ m + a < M.readAddr X t ∧ ∃ ℓ ∈ L (t + 1), ℓ ⬝ᵥ M.u ≠ 0

/-- The cell written at step `s ∈ I` is control-live at the cut `τ`: `s ≤ τ` and some demanded
read at a step after `τ` reads it. -/
def Live (X : ℕ → Cfg d Q) (a b : ℕ) (L : ℕ → Submodule ℚ (Fin d → ℚ)) (s τ : ℕ) : Prop :=
  a < s ∧ s ≤ τ ∧ ∃ t, τ ≤ t ∧ M.Demanded m X a b L t ∧ M.readAddr X t = m + s

/-- Theorem (control-observable state suffices). Let `X` be an execution, normalized on
`I = {a+1, …, b}`, let `L` be a closure for its trace on `I`, and let `a ≤ τ ≤ b`. Let `X'` be an
execution started at time `τ` such that (a) its control state, (b) the values of all
functionals of `L_τ` on its registers, (c) its history cells `H[j]`, `j ≤ m + a`, and (d) its
history cells written at control-live steps agree with those of `X` at time `τ`. Then at every
step of `{τ+1, …, b}` the two executions have the same addresses, branch bits and control
states (in particular `X'` is normalized there). -/
theorem control_observable_sufficiency (X X' : ℕ → Cfg d Q) (a b τ : ℕ)
    (hX : ∀ t, X (t + 1) = M.step m (t + 1) (X t))
    (hnorm : ∀ t, a ≤ t → t < b → ValidAddr (m + (t + 1)) (M.addr (X t)))
    (L : ℕ → Submodule ℚ (Fin d → ℚ)) (hL : M.IsClosure m X a b L)
    (haτ : a ≤ τ) (hτb : τ ≤ b)
    (hX' : ∀ t, τ ≤ t → X' (t + 1) = M.step m (t + 1) (X' t))
    (hqa : (X' τ).q = (X τ).q)
    (hxb : ∀ ℓ ∈ L τ, ℓ ⬝ᵥ (X' τ).x = ℓ ⬝ᵥ (X τ).x)
    (hHc : ∀ j ≤ m + a, (X' τ).H j = (X τ).H j)
    (hHd : ∀ s, M.Live m X a b L s τ → (X' τ).H (m + s) = (X τ).H (m + s)) :
    ∀ t, τ ≤ t → t < b →
      M.addr (X' t) = M.addr (X t) ∧ M.branch (X' t) = M.branch (X t) ∧
        (X' (t + 1)).q = (X (t + 1)).q := by
  sorry

end AffineMachine

/-- The Strahler rank of the ladder vertex `v_{k,j}`: sources have rank `0`, and `v_{k+1,j}` has
the predecessors `v_{k,j}` and `v_{k,j+1}`. -/
def ladderRank (w : ℕ) : ℕ → ZMod w → ℕ
  | 0, _ => 0
  | k + 1, j => strahler (ladderRank w k j) (ladderRank w k (j + 1))

/-- Theorem (balanced ladders) (iii): every vertex of layer `k` has rank exactly `k`. -/
theorem ladder_rank (w k : ℕ) (j : ZMod w) : ladderRank w k j = k := by
  sorry

/-- Theorem (balanced ladders) (ii): for `w ≥ 2` the two predecessors are distinct. -/
theorem ladder_pred_ne (w : ℕ) (hw : 2 ≤ w) (j : ZMod w) : j ≠ j + 1 := by
  sorry

/-- The edges of the ladder `D_{r,w}`: from `v_{k,j+e}` to `v_{k+1,j}` for `k < r`, `e ∈ {0,1}`. -/
def ladderEdges (r w : ℕ) [NeZero w] : Finset ((ℕ × ZMod w) × (ℕ × ZMod w)) :=
  ((Finset.range r) ×ˢ (Finset.univ : Finset (ZMod w)) ×ˢ (Finset.univ : Finset Bool)).image
    (fun p => ((p.1, p.2.1 + if p.2.2 then 1 else 0), (p.1 + 1, p.2.1)))

/-- Theorem (balanced ladders) (i): the ladder has exactly `2 r w` edges. -/
theorem card_ladderEdges (r w : ℕ) [NeZero w] (hw : 2 ≤ w) :
    (ladderEdges r w).card = 2 * r * w := by
  sorry

end GC.Portals
