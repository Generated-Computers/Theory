import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Barrier: identity padding (manuscript 010e, Section 3)

Affine–product circuits over `𝔽₂`, the multiplicative Strahler rank, exact Newton iteration, the
balanced identity `z' = z·z` (Lemma 3.1) and the exact Newton delay on the ladder (Theorem 3.2).
The padding construction `C ↦ C↑` of Theorem 3.3 is not formalized.
-/

namespace GC.Tabulation

/-- A gate of an affine–product circuit over `𝔽₂`: a constant `x_i = c`, an affine gate
`x_i = c + ∑_{j ∈ S} x_j` (the list `S` records the coefficients `a_{ij}` with multiplicity), or a
product gate `x_i = x_p x_q`. Parents have smaller indices (only parents `< i` are used). -/
inductive APGate
  | const (c : ZMod 2)
  | affine (c : ZMod 2) (S : List ℕ)
  | prod (p q : ℕ)

/-- An affine–product circuit: gate `i` for every `i : ℕ` (a finite circuit is a prefix). -/
abbrev APCircuit := ℕ → APGate

/-- The right-hand side `f_i(x)` of a gate. -/
def gateRHS (g : APGate) (x : ℕ → ZMod 2) : ZMod 2 :=
  match g with
  | .const c => c
  | .affine c S => c + (S.map x).sum
  | .prod p q => x p * x q

/-- The exact values of the circuit. -/
def evalC (C : APCircuit) : ℕ → ZMod 2
  | i =>
    match C i with
    | .const c => c
    | .affine c S => c + (S.map (fun j => if _h : j < i then evalC C j else 0)).sum
    | .prod p q => (if _h : p < i then evalC C p else 0) * (if _h : q < i then evalC C q else 0)
termination_by i => i

/-- The Newton correction `δ`, the solution of `J(x) δ = F(x)` by forward substitution, where
`F_i(x) = x_i + f_i(x)` and `J(x)` is the formal Jacobian of `F` (unit lower triangular):
`δ_i = F_i(x) - ∑_{j < i} ∂f_i/∂x_j · δ_j`. -/
def newtonDelta (C : APCircuit) (x : ℕ → ZMod 2) : ℕ → ZMod 2
  | i =>
    match C i with
    | .const c => x i + c
    | .affine c S =>
      (x i + (c + (S.map x).sum)) -
        (S.map (fun j => if _h : j < i then newtonDelta C x j else 0)).sum
    | .prod p q =>
      (x i + x p * x q) -
        ((if _h : p < i then x q * newtonDelta C x p else 0) +
          (if _h : q < i then x p * newtonDelta C x q else 0))
termination_by i => i

/-- The Newton step `N(x) = x + δ`. -/
def newtonStep (C : APCircuit) (x : ℕ → ZMod 2) : ℕ → ZMod 2 := fun i => x i + newtonDelta C x i

/-- The multiplicative Strahler rank: `0` for constants, the maximum over parents for affine
gates, and `max(r₁, r₂ + 1)` (`r₁ ≥ r₂` the parent ranks) for products. -/
def srank (C : APCircuit) : ℕ → ℕ
  | i =>
    match C i with
    | .const _ => 0
    | .affine _ S => (S.map (fun j => if _h : j < i then srank C j else 0)).foldr max 0
    | .prod p q =>
      if (if _h : p < i then srank C p else 0) = (if _h : q < i then srank C q else 0) then
        (if _h : p < i then srank C p else 0) + 1
      else max (if _h : p < i then srank C p else 0) (if _h : q < i then srank C q else 0)
termination_by i => i

/-- **Lemma 3.1 (a balanced identity), value part.** Over `𝔽₂`, `z · z = z`. -/
theorem zmod2_mul_self (z : ZMod 2) : z * z = z := by
  revert z; decide

/-- The ladder: `z_0 = 1` (gate `0`) and, for `ℓ ≥ 0`, the copies `s_{ℓ+1} = z_ℓ` (gate `3ℓ+1`),
`d_{ℓ+1} = z_ℓ` (gate `3ℓ+2`) and the product `z_{ℓ+1} = s_{ℓ+1} d_{ℓ+1}` (gate `3ℓ+3`). The
ladder of length `k` is the prefix of gates `0, …, 3k`. -/
def ladder : APCircuit := fun i =>
  if i = 0 then .const 1
  else if i % 3 = 1 then .affine 0 [i - 1]
  else if i % 3 = 2 then .affine 0 [i - 2]
  else .prod (i - 2) (i - 1)

lemma ladder_zero : ladder 0 = .const 1 := rfl
lemma ladder_s (l : ℕ) : ladder (3 * l + 1) = .affine 0 [3 * l] := by
  simp only [ladder]
  rw [if_neg (by omega), if_pos (by omega), show 3 * l + 1 - 1 = 3 * l by omega]
lemma ladder_d (l : ℕ) : ladder (3 * l + 2) = .affine 0 [3 * l] := by
  simp only [ladder]
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), show 3 * l + 2 - 2 = 3 * l by omega]
lemma ladder_z (l : ℕ) : ladder (3 * l + 3) = .prod (3 * l + 1) (3 * l + 2) := by
  simp only [ladder]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    show 3 * l + 3 - 2 = 3 * l + 1 by omega, show 3 * l + 3 - 1 = 3 * l + 2 by omega]

/-- The exact values of the ladder are all `1`. -/
theorem ladder_eval (l : ℕ) :
    evalC ladder (3 * l) = 1 ∧ evalC ladder (3 * l + 1) = 1 ∧ evalC ladder (3 * l + 2) = 1 := by
  induction l with
  | zero =>
    have h0 : evalC ladder 0 = 1 := by rw [evalC, ladder_zero]
    refine ⟨h0, ?_, ?_⟩
    · rw [evalC, ladder_s 0]; simp [h0]
    · rw [evalC, ladder_d 0]; simp [h0]
  | succ l ih =>
    have hz : evalC ladder (3 * (l + 1)) = 1 := by
      rw [show 3 * (l + 1) = 3 * l + 3 by omega, evalC, ladder_z l]
      simp only [show 3 * l + 1 < 3 * l + 3 by omega, show 3 * l + 2 < 3 * l + 3 by omega,
        dite_true, ih.2.1, ih.2.2, mul_one]
    refine ⟨hz, ?_, ?_⟩
    · rw [evalC, ladder_s]; simp [hz]
    · rw [evalC, ladder_d]; simp [hz]

/-- The ranks along the ladder: `ρ(z_ℓ) = ℓ` and `ρ(s_{ℓ+1}) = ρ(d_{ℓ+1}) = ℓ`. -/
theorem ladder_rank (l : ℕ) :
    srank ladder (3 * l) = l ∧ srank ladder (3 * l + 1) = l ∧ srank ladder (3 * l + 2) = l := by
  induction l with
  | zero =>
    have h0 : srank ladder 0 = 0 := by rw [srank, ladder_zero]
    refine ⟨h0, ?_, ?_⟩
    · rw [srank, ladder_s 0]; simp [h0]
    · rw [srank, ladder_d 0]; simp [h0]
  | succ l ih =>
    have hz : srank ladder (3 * (l + 1)) = l + 1 := by
      rw [show 3 * (l + 1) = 3 * l + 3 by omega, srank, ladder_z l]
      simp only [show 3 * l + 1 < 3 * l + 3 by omega, show 3 * l + 2 < 3 * l + 3 by omega,
        dite_true, ih.2.1, ih.2.2, if_true]
    refine ⟨hz, ?_, ?_⟩
    · rw [srank, ladder_s]; simp [hz]
    · rw [srank, ladder_d]; simp [hz]

section Newton

variable (x : ℕ → ZMod 2)

lemma newton_zero : newtonStep ladder x 0 = 1 := by
  simp only [newtonStep]
  rw [newtonDelta, ladder_zero]
  show x 0 + (x 0 + 1) = 1
  generalize x 0 = a
  revert a; decide

lemma delta_s (l : ℕ) : newtonDelta ladder x (3 * l + 1) =
    (x (3 * l + 1) + x (3 * l)) - newtonDelta ladder x (3 * l) := by
  rw [newtonDelta, ladder_s]
  simp

lemma delta_d (l : ℕ) : newtonDelta ladder x (3 * l + 2) =
    (x (3 * l + 2) + x (3 * l)) - newtonDelta ladder x (3 * l) := by
  rw [newtonDelta, ladder_d]
  simp [show 3 * l < 3 * l + 2 by omega]

lemma delta_z (l : ℕ) : newtonDelta ladder x (3 * l + 3) =
    (x (3 * l + 3) + x (3 * l + 1) * x (3 * l + 2)) -
      (x (3 * l + 2) * newtonDelta ladder x (3 * l + 1) +
        x (3 * l + 1) * newtonDelta ladder x (3 * l + 2)) := by
  rw [newtonDelta, ladder_z]
  simp [show 3 * l + 1 < 3 * l + 3 by omega, show 3 * l + 2 < 3 * l + 3 by omega]

/-- A copy gate takes the new value of its parent. -/
lemma newton_s (l : ℕ) : newtonStep ladder x (3 * l + 1) = newtonStep ladder x (3 * l) := by
  simp only [newtonStep, delta_s]
  generalize x (3 * l + 1) = a
  generalize x (3 * l) = b
  generalize newtonDelta ladder x (3 * l) = c
  revert a b c; decide

lemma newton_d (l : ℕ) : newtonStep ladder x (3 * l + 2) = newtonStep ladder x (3 * l) := by
  simp only [newtonStep, delta_d]
  generalize x (3 * l + 2) = a
  generalize x (3 * l) = b
  generalize newtonDelta ladder x (3 * l) = c
  revert a b c; decide

/-- If the two copies carry equal values, the product takes their common old value. -/
lemma newton_z (l : ℕ) (h : x (3 * l + 1) = x (3 * l + 2)) :
    newtonStep ladder x (3 * l + 3) = x (3 * l + 1) := by
  simp only [newtonStep, delta_z, delta_s, delta_d]
  rw [← h]
  generalize x (3 * l + 1) = a
  generalize x (3 * l + 3) = b
  generalize x (3 * l) = c
  generalize newtonDelta ladder x (3 * l) = e
  revert a b c e; decide

end Newton

/-- The standard start: `z_0 = 1` and all other gates `0`. -/
def ladderStart : ℕ → ZMod 2 := fun i => if i = 0 then 1 else 0

/-- **Theorem 3.2 (exact Newton delay).** Newton iteration on the ladder from the standard start:
after `t` steps, `z_0 = 1`, `s_{ℓ+1} = d_{ℓ+1} = 1` iff `ℓ + 1 ≤ t`, and `z_{ℓ+1} = 1` iff
`ℓ + 1 < t`. -/
theorem ladder_newton (t : ℕ) :
    (newtonStep ladder)^[t] ladderStart 0 = 1 ∧
    ∀ l, (newtonStep ladder)^[t] ladderStart (3 * l + 1) = (if l + 1 ≤ t then 1 else 0) ∧
      (newtonStep ladder)^[t] ladderStart (3 * l + 2) = (if l + 1 ≤ t then 1 else 0) ∧
      (newtonStep ladder)^[t] ladderStart (3 * l + 3) = (if l + 1 < t then 1 else 0) := by
  induction t with
  | zero =>
    refine ⟨rfl, fun l => ?_⟩
    simp [ladderStart]
  | succ t ih =>
    obtain ⟨ih0, ih⟩ := ih
    set X := (newtonStep ladder)^[t] ladderStart with hX
    rw [Function.iterate_succ_apply']
    have hzl : ∀ l, newtonStep ladder X (3 * l) = if l ≤ t then 1 else 0 := by
      intro l
      rcases l with _ | l
      · simp [newton_zero]
      · rw [show 3 * (l + 1) = 3 * l + 3 by omega, newton_z X l (by rw [(ih l).1, (ih l).2.1]),
          (ih l).1]
    refine ⟨newton_zero X, fun l => ⟨?_, ?_, ?_⟩⟩
    · rw [newton_s, hzl]
      congr 1; apply propext; omega
    · rw [newton_d, hzl]
      congr 1; apply propext; omega
    · rw [newton_z X l (by rw [(ih l).1, (ih l).2.1]), (ih l).1]
      congr 1; apply propext; omega

/-- **Theorem 3.2, consequence.** On the ladder, the gate `z_k` (`k ≥ 1`, exact value `1`, rank
`ρ(z_k) = k`) is exact after `t` Newton steps iff `t ≥ k + 1 = ρ(z_k) + 1`. -/
theorem ladder_first_exact (k t : ℕ) (hk : 1 ≤ k) :
    (newtonStep ladder)^[t] ladderStart (3 * k) = evalC ladder (3 * k) ↔
      srank ladder (3 * k) + 1 ≤ t := by
  obtain ⟨l, rfl⟩ : ∃ l, k = l + 1 := ⟨k - 1, by omega⟩
  rw [(ladder_eval (l + 1)).1, (ladder_rank (l + 1)).1,
    show 3 * (l + 1) = 3 * l + 3 by omega, ((ladder_newton t).2 l).2.2]
  split_ifs with h
  · simp; omega
  · simp only [zero_ne_one, false_iff]; omega

end GC.Tabulation
