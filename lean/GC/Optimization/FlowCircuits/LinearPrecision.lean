import GC.Optimization.FlowCircuits.Circuit
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Logic.Relation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

/-!
# Manuscript 003f: Circuit LPs need linear precision

* `circuitLP_unique` : Theorem 4.1 (the sparse circuit LP of a monotone circuit has exactly one
  feasible point, the vector of gate values).
* `fib_precision`, `fibDelta_bounds` : Theorem 4.2 (the Fibonacci OR ladder: a point violating
  no constraint by more than `δ = 1/(2(F_{n+1}-1)) = Θ(φ^{-n})` has output `1/2`).
* `ladder_det`, `ladder_minor` : Theorem 4.3 (the ladder matrix `T_m` has determinant `1` and a
  minor of absolute value `F_m`).
* `losing_antitone`, `switched_not_losing`, `val_false_of_losing`, `val_true_of_not_losing` :
  Theorem 5.2 (i), (ii), (iv), (v) (simultaneous escape switching).
-/

namespace GC.FlowCircuits

open Finset

namespace MonCircuit

variable {n : ℕ} (C : MonCircuit n)

/-! ### The sparse circuit LP -/

/-- Feasibility for the circuit LP of Section 4: every variable in `[0,1]`, inputs fixed, and
for `z = x ∨ y`: `z ≥ x`, `z ≥ y`, `z ≤ x + y`; for `z = x ∧ y`: `z ≤ x`, `z ≤ y`,
`z ≥ x + y - 1`. -/
def LPFeasible (x : Fin n → ℝ) : Prop :=
  ∀ v, (0 ≤ x v ∧ x v ≤ 1) ∧ (∀ b, C.node v = .input b → x v = b2r b) ∧
    (∀ c₁ c₂, C.node v = .gate false c₁ c₂ → x c₁ ≤ x v ∧ x c₂ ≤ x v ∧ x v ≤ x c₁ + x c₂) ∧
    (∀ c₁ c₂, C.node v = .gate true c₁ c₂ → x v ≤ x c₁ ∧ x v ≤ x c₂ ∧ x c₁ + x c₂ - 1 ≤ x v)

/-- **Theorem 4.1 (sparse circuit LP; Dobkin–Lipton–Reiss).** The circuit LP of a monotone
circuit with fixed inputs has exactly one feasible point, the vector of gate values. -/
theorem circuitLP_unique (x : Fin n → ℝ) :
    C.LPFeasible x ↔ x = fun v => b2r (C.val v) := by
  constructor
  · intro hx
    funext v
    induction v using WellFoundedLT.induction with
    | _ v ih =>
    obtain ⟨hb, hin, hor, hand⟩ := hx v
    cases hnode : C.node v with
    | input b => rw [hin b hnode, C.val_input hnode]
    | gate a c₁ c₂ =>
      have ht := C.topo v a c₁ c₂ hnode
      rw [C.val_gate hnode]
      have e1 := ih c₁ ht.1
      have e2 := ih c₂ ht.2
      cases a
      · obtain ⟨h1, h2, h3⟩ := hor c₁ c₂ hnode
        simp only [e1, e2] at h1 h2 h3
        cases hv1 : C.val c₁ <;> cases hv2 : C.val c₂ <;> simp [b2r, hv1, hv2] at h1 h2 h3 ⊢ <;>
          linarith
      · obtain ⟨h1, h2, h3⟩ := hand c₁ c₂ hnode
        simp only [e1, e2] at h1 h2 h3
        cases hv1 : C.val c₁ <;> cases hv2 : C.val c₂ <;> simp [b2r, hv1, hv2] at h1 h2 h3 ⊢ <;>
          linarith
  · rintro rfl v
    refine ⟨by cases h : C.val v <;> simp [b2r, h], fun b h => by simp only [C.val_input h], ?_, ?_⟩
    · intro c₁ c₂ h
      simp only [C.val_gate h]
      cases hv1 : C.val c₁ <;> cases hv2 : C.val c₂ <;> simp [b2r, hv1, hv2]
    · intro c₁ c₂ h
      simp only [C.val_gate h]
      cases hv1 : C.val c₁ <;> cases hv2 : C.val c₂ <;> simp [b2r, hv1, hv2]

end MonCircuit

/-! ### The Fibonacci OR ladder -/

/-- `δ = 1 / (2 (F_{n+1} - 1))`. -/
noncomputable def fibDelta (n : ℕ) : ℝ := 1 / (2 * ((Nat.fib (n + 1) : ℝ) - 1))

/-- The point `x̃_i = δ (F_{i+1} - 1)`. -/
noncomputable def fibPoint (n i : ℕ) : ℝ := fibDelta n * ((Nat.fib (i + 1) : ℝ) - 1)

lemma two_le_fib {n : ℕ} (hn : 2 ≤ n) : (2 : ℝ) ≤ Nat.fib (n + 1) := by
  have : Nat.fib 3 ≤ Nat.fib (n + 1) := Nat.fib_mono (by omega)
  have h3 : Nat.fib 3 = 2 := by decide
  exact_mod_cast h3 ▸ this

lemma fibDelta_pos {n : ℕ} (hn : 2 ≤ n) : 0 < fibDelta n := by
  have := two_le_fib hn
  unfold fibDelta; apply div_pos one_pos; linarith

/-- **Theorem 4.2 (exponentially accurate feasibility is necessary).** For the Fibonacci OR ladder
`x_0 = x_1 = 0`, `x_i = x_{i-1} ∨ x_{i-2}` (`2 ≤ i ≤ n`), whose exact value vector is `0`, the
point `x̃` satisfies `x̃_0 = x̃_1 = 0`, `x̃_n = 1/2`, all box constraints and lower OR inequalities
exactly, and violates every upper OR inequality `x_i ≤ x_{i-1} + x_{i-2}` by exactly `δ`. -/
theorem fib_precision (n : ℕ) (hn : 2 ≤ n) :
    fibPoint n 0 = 0 ∧ fibPoint n 1 = 0 ∧ fibPoint n n = 1 / 2 ∧
    (∀ i ≤ n, 0 ≤ fibPoint n i ∧ fibPoint n i ≤ 1) ∧
    ∀ i, i + 2 ≤ n →
      fibPoint n (i + 1) ≤ fibPoint n (i + 2) ∧ fibPoint n i ≤ fibPoint n (i + 2) ∧
      fibPoint n (i + 2) - (fibPoint n (i + 1) + fibPoint n i) = fibDelta n := by
  have hF := two_le_fib hn
  have hδ := fibDelta_pos hn
  have hmono : ∀ i j, i ≤ j → fibPoint n i ≤ fibPoint n j := by
    intro i j hij
    unfold fibPoint
    have : (Nat.fib (i + 1) : ℝ) ≤ Nat.fib (j + 1) := by exact_mod_cast Nat.fib_mono (by omega)
    nlinarith
  have hn2 : fibPoint n n = 1 / 2 := by
    have hne : ((Nat.fib (n + 1) : ℝ) - 1) ≠ 0 := by linarith
    unfold fibPoint fibDelta
    rw [div_mul_eq_mul_div, one_mul, div_eq_iff (by positivity)]
    ring
  refine ⟨by simp [fibPoint], by simp [fibPoint], hn2, ?_, ?_⟩
  · intro i hi
    constructor
    · unfold fibPoint
      have : (1 : ℝ) ≤ Nat.fib (i + 1) := by exact_mod_cast Nat.fib_pos.mpr (by omega)
      nlinarith
    · have := hmono i n hi; linarith
  · intro i hi
    refine ⟨hmono _ _ (by omega), hmono _ _ (by omega), ?_⟩
    unfold fibPoint
    rw [show i + 2 + 1 = (i + 1) + 2 by ring, Nat.fib_add_two]
    push_cast
    rw [show i + 1 + 1 = i + 2 by ring]
    ring

open Real in
lemma goldenRatio_pow_le_fib : ∀ k : ℕ, goldenRatio ^ k ≤ Nat.fib (k + 2)
  | 0 => by simp
  | 1 => by
    have := goldenRatio_lt_two
    simp [Nat.fib_add_two]; norm_num; linarith
  | k + 2 => by
    have h1 := goldenRatio_pow_le_fib k
    have h2 := goldenRatio_pow_le_fib (k + 1)
    have e := goldenRatio_pow_sub_goldenRatio_pow k
    rw [show k + 2 + 2 = (k + 2) + 2 by rfl, Nat.fib_add_two]
    push_cast
    rw [show k + 2 + 1 = k + 1 + 2 by ring]
    linarith

open Real in
lemma fib_le_goldenRatio_pow : ∀ k : ℕ, (Nat.fib (k + 1) : ℝ) ≤ goldenRatio ^ k
  | 0 => by simp
  | 1 => by
    have := one_lt_goldenRatio
    simp; linarith
  | k + 2 => by
    have h1 := fib_le_goldenRatio_pow k
    have h2 := fib_le_goldenRatio_pow (k + 1)
    have e := goldenRatio_pow_sub_goldenRatio_pow k
    rw [show k + 2 + 1 = (k + 1) + 2 by rfl, Nat.fib_add_two]
    push_cast
    linarith

open Real in
/-- `δ = Θ(φ^{-n})`: `1 / (2 φ^n) ≤ δ ≤ 1 / φ^{n-1}` for `n ≥ 2`. -/
theorem fibDelta_bounds (n : ℕ) (hn : 2 ≤ n) :
    1 / (2 * goldenRatio ^ n) ≤ fibDelta n ∧ fibDelta n ≤ 1 / goldenRatio ^ (n - 1) := by
  have hF := two_le_fib hn
  have hlow : goldenRatio ^ (n - 1) ≤ Nat.fib (n + 1) := by
    have := goldenRatio_pow_le_fib (n - 1)
    rwa [show n - 1 + 2 = n + 1 by omega] at this
  have hup : (Nat.fib (n + 1) : ℝ) ≤ goldenRatio ^ n := fib_le_goldenRatio_pow n
  have hpos : 0 < goldenRatio ^ (n - 1) := pow_pos goldenRatio_pos _
  unfold fibDelta
  constructor
  · apply one_div_le_one_div_of_le
    · linarith
    · linarith
  · apply one_div_le_one_div_of_le hpos
    linarith

/-! ### The Fibonacci subdeterminant -/

/-- The matrix `T_m` of the upper OR inequalities `x_i - x_{i-1} - x_{i-2} ≤ 0` (`2 ≤ i ≤ n`) on
the columns `x_2, …, x_n` (`m = n - 1`): ones on the diagonal, minus ones on the first two
subdiagonals. -/
def ladderMatrix (m : ℕ) : Matrix (Fin m) (Fin m) ℤ := fun i j =>
  (if j = i then 1 else 0) - (if j.val + 1 = i.val then 1 else 0) -
    (if j.val + 2 = i.val then 1 else 0)

lemma ladder_lowerTriangular (m : ℕ) : (ladderMatrix m).IsLowerTriangular := by
  intro i j hij
  have : i < j := hij
  have hne : j ≠ i := ne_of_gt this
  simp only [ladderMatrix, hne, if_false]
  have h1 : ¬ (j.val + 1 = i.val) := by have := Fin.lt_def.mp this; omega
  have h2 : ¬ (j.val + 2 = i.val) := by have := Fin.lt_def.mp this; omega
  simp [h1, h2]

/-- `det T_m = 1`. -/
theorem ladder_det (m : ℕ) : (ladderMatrix m).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ (ladder_lowerTriangular m)]
  apply Finset.prod_eq_one
  intro i _
  simp [ladderMatrix]

lemma sum_shift {m : ℕ} (g : Fin m → ℤ) (i : Fin m) (c : ℕ) :
    ∑ j : Fin m, (if j.val + c = i.val then (1 : ℤ) else 0) * g j =
      if h : c ≤ i.val then g ⟨i.val - c, by omega⟩ else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨i.val - c, by omega⟩]
    · simp; omega
    · intro j _ hj
      have : j.val + c ≠ i.val := by
        intro e; apply hj; ext; simp; omega
      simp [this]
    · simp
  · apply Finset.sum_eq_zero
    intro j _
    have : j.val + c ≠ i.val := by omega
    simp [this]

/-- **Theorem 4.3 (Fibonacci subdeterminant).** The `(m-1) × (m-1)` minor of `T_m` obtained by
deleting the first row and the last column has absolute value `F_m` (here `m = k + 1`). -/
theorem ladder_minor (k : ℕ) :
    |((ladderMatrix (k + 1)).submatrix Fin.succ Fin.castSucc).det| = Nat.fib (k + 1) := by
  set T := ladderMatrix (k + 1)
  have hmul : T * T.adjugate = 1 := by rw [Matrix.mul_adjugate, ladder_det, one_smul]
  set u : Fin (k + 1) → ℤ := fun i => T.adjugate i 0 with hu
  have hrow : ∀ i : Fin (k + 1), u i -
      (if h : 1 ≤ i.val then u ⟨i.val - 1, by omega⟩ else 0) -
      (if h : 2 ≤ i.val then u ⟨i.val - 2, by omega⟩ else 0) = if i = 0 then 1 else 0 := by
    intro i
    have := congrFun (congrFun hmul i) 0
    rw [Matrix.mul_apply] at this
    have e : ∀ j, T i j * T.adjugate j 0 = (if j = i then 1 else 0) * u j -
        (if j.val + 1 = i.val then 1 else 0) * u j -
        (if j.val + 2 = i.val then 1 else 0) * u j := by
      intro j; simp only [T, ladderMatrix, hu]; ring
    simp_rw [e, Finset.sum_sub_distrib, sum_shift] at this
    have hs : ∑ x, (if x = i then (1 : ℤ) else 0) * u x = u i := by simp
    rw [hs, Matrix.one_apply] at this
    rw [this]
  have hfib : ∀ m : ℕ, ∀ i : Fin (k + 1), i.val = m → u i = Nat.fib (m + 1) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro i him
    have h := hrow i
    rcases Nat.lt_or_ge m 2 with hm | hm
    · interval_cases m
      · have hi0 : i = 0 := by ext; simp [him]
        simp [hi0] at h ⊢; linarith
      · have hi0 : i ≠ 0 := by intro e; rw [e] at him; simp at him
        simp [him, hi0] at h
        have := ih 0 (by omega) ⟨0, by omega⟩ rfl
        simp at this; simp; linarith
    · have hi0 : i ≠ 0 := by intro e; rw [e] at him; simp at him; omega
      rw [dif_pos (by omega), dif_pos (by omega), if_neg hi0] at h
      have h1 := ih (m - 1) (by omega) ⟨i.val - 1, by omega⟩ (by simp; omega)
      have h2 := ih (m - 2) (by omega) ⟨i.val - 2, by omega⟩ (by simp; omega)
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
      simp only [show m' + 2 - 1 = m' + 1 by omega, show m' + 2 - 2 = m' by omega] at h1 h2
      rw [show m' + 2 + 1 = (m' + 1) + 2 by ring, Nat.fib_add_two]
      push_cast
      rw [show m' + 1 + 1 = m' + 2 by ring]
      linarith
  have hlast := hfib k (Fin.last k) rfl
  simp only [hu] at hlast
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_zero, Fin.succAbove_last] at hlast
  have habs := congrArg (fun z : ℤ => |z|) hlast
  simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] at habs
  rw [habs]
  simp

/-! ### Escape switching (Section 5) -/

namespace MonCircuit

variable {n : ℕ} (C : MonCircuit n)

/-- The selected child of an OR gate under an OR strategy `σ` (`σ v = false` selects the first
child, `true` the second). -/
def sel (σ : Fin n → Bool) (v c₁ c₂ : Fin n) : Fin n := if σ v then c₂ else c₁

/-- The non-selected child. -/
def unsel (σ : Fin n → Bool) (v c₁ c₂ : Fin n) : Fin n := if σ v then c₁ else c₂

/-- Edges of the strategy graph: both child edges of an AND gate, the selected child edge of an
OR gate. -/
def StratEdge (σ : Fin n → Bool) (v c : Fin n) : Prop :=
  ∃ c₁ c₂, (C.node v = .gate true c₁ c₂ ∧ (c = c₁ ∨ c = c₂)) ∨
    (C.node v = .gate false c₁ c₂ ∧ c = sel σ v c₁ c₂)

/-- The losing set `L_σ`: vertices from which a false input is reachable in the strategy
graph. -/
def Losing (σ : Fin n → Bool) (v : Fin n) : Prop :=
  ∃ w, Relation.ReflTransGen (C.StratEdge σ) v w ∧ C.node w = .input false

/-- An escape: an OR gate in `L_σ` whose non-selected child lies outside `L_σ`. -/
def Escape (σ : Fin n → Bool) (v : Fin n) : Prop :=
  C.Losing σ v ∧ ∃ c₁ c₂, C.node v = .gate false c₁ c₂ ∧ ¬ C.Losing σ (unsel σ v c₁ c₂)

/-- Simultaneous escape switching: every escape switches to its other child. -/
noncomputable def switch (σ : Fin n → Bool) : Fin n → Bool := by
  classical
  exact fun v => if C.Escape σ v then !σ v else σ v

variable {C}

lemma losing_of_edge {σ : Fin n → Bool} {v c : Fin n} (he : C.StratEdge σ v c)
    (hc : C.Losing σ c) : C.Losing σ v := by
  obtain ⟨w, hw, hwi⟩ := hc
  exact ⟨w, Relation.ReflTransGen.head he hw, hwi⟩

lemma losing_gate {σ : Fin n → Bool} {v : Fin n} {a : Bool} {c₁ c₂ : Fin n}
    (hv : C.node v = .gate a c₁ c₂) (hL : C.Losing σ v) :
    ∃ c, C.StratEdge σ v c ∧ C.Losing σ c := by
  obtain ⟨w, hw, hwi⟩ := hL
  rcases Relation.ReflTransGen.cases_head hw with rfl | ⟨c, hvc, hcw⟩
  · rw [hv] at hwi; cases hwi
  · exact ⟨c, hvc, w, hcw, hwi⟩

/-- **Theorem 5.2 (v), and "`L_σ` contains every false vertex".** A vertex outside `L_σ` is
true. -/
theorem val_true_of_not_losing (σ : Fin n → Bool) (v : Fin n) (hv : ¬ C.Losing σ v) :
    C.val v = true := by
  induction v using WellFoundedLT.induction with
  | _ v ih =>
  cases hnode : C.node v with
  | input b =>
    rw [C.val_input hnode]
    cases b
    · exact absurd ⟨v, Relation.ReflTransGen.refl, hnode⟩ hv
    · rfl
  | gate a c₁ c₂ =>
    have ht := C.topo v a c₁ c₂ hnode
    rw [C.val_gate hnode]
    cases a
    · -- OR gate: its selected child is outside `L_σ`
      have hs : ¬ C.Losing σ (sel σ v c₁ c₂) := fun h =>
        hv (losing_of_edge ⟨c₁, c₂, Or.inr ⟨hnode, rfl⟩⟩ h)
      unfold sel at hs
      cases hσ : σ v
      · rw [hσ] at hs; simp [ih c₁ ht.1 hs]
      · rw [hσ] at hs; simp [ih c₂ ht.2 hs]
    · have h1 : ¬ C.Losing σ c₁ := fun h =>
        hv (losing_of_edge ⟨c₁, c₂, Or.inl ⟨hnode, Or.inl rfl⟩⟩ h)
      have h2 : ¬ C.Losing σ c₂ := fun h =>
        hv (losing_of_edge ⟨c₁, c₂, Or.inl ⟨hnode, Or.inr rfl⟩⟩ h)
      simp [ih c₁ ht.1 h1, ih c₂ ht.2 h2]

/-- **Theorem 5.2 (iv).** If there is no escape, every vertex of `L_σ` is false (in particular
the output, if it lies in `L_σ`). -/
theorem val_false_of_losing (σ : Fin n → Bool) (hno : ∀ v, ¬ C.Escape σ v) (v : Fin n)
    (hv : C.Losing σ v) : C.val v = false := by
  induction v using WellFoundedLT.induction with
  | _ v ih =>
  cases hnode : C.node v with
  | input b =>
    rw [C.val_input hnode]
    obtain ⟨w, hw, hwi⟩ := hv
    rcases Relation.ReflTransGen.cases_head hw with rfl | ⟨c, hvc, _⟩
    · rw [hnode] at hwi; cases hwi; rfl
    · obtain ⟨c₁, c₂, h⟩ := hvc
      rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [hnode] at h <;> cases h
  | gate a c₁ c₂ =>
    have ht := C.topo v a c₁ c₂ hnode
    rw [C.val_gate hnode]
    obtain ⟨c, hvc, hc⟩ := losing_gate hnode hv
    obtain ⟨d₁, d₂, h⟩ := hvc
    cases a
    · -- OR gate: the selected child is losing, and the other one too (no escape)
      rcases h with ⟨h, _⟩ | ⟨h, rfl⟩
      · rw [hnode] at h; cases h
      rw [hnode] at h; injection h with _ e1 e2; subst e1; subst e2
      have hother : C.Losing σ (unsel σ v c₁ c₂) := by
        by_contra hn; exact hno v ⟨hv, c₁, c₂, hnode, hn⟩
      unfold sel at hc; unfold unsel at hother
      cases hσ : σ v <;> rw [hσ] at hc hother <;> simp at hc hother
      · simp [ih c₁ ht.1 hc, ih c₂ ht.2 hother]
      · simp [ih c₂ ht.2 hc, ih c₁ ht.1 hother]
    · rcases h with ⟨h, hc'⟩ | ⟨h, _⟩
      · rw [hnode] at h; injection h with _ e1 e2; subst e1; subst e2
        rcases hc' with rfl | rfl
        · simp [ih _ ht.1 hc]
        · simp [ih _ ht.2 hc]
      · rw [hnode] at h; cases h

/-- **Theorem 5.2 (i).** Simultaneous switching shrinks the losing set:
`L_{σ'} ⊆ L_σ`. -/
theorem losing_antitone (σ : Fin n → Bool) (v : Fin n) (hv : C.Losing (C.switch σ) v) :
    C.Losing σ v := by
  classical
  by_contra hnot
  -- the complement `W` of `L_σ` is closed under the edges of the switched strategy
  have closed : ∀ x y, C.StratEdge (C.switch σ) x y → ¬ C.Losing σ x → ¬ C.Losing σ y := by
    intro x y hxy hx hy
    obtain ⟨c₁, c₂, h⟩ := hxy
    rcases h with ⟨h, hc⟩ | ⟨h, hc⟩
    · exact hx (losing_of_edge ⟨c₁, c₂, Or.inl ⟨h, hc⟩⟩ hy)
    · -- `x` is not an escape (escapes are losing), so it keeps its selection
      have hne : ¬ C.Escape σ x := fun he => hx he.1
      have hsw : C.switch σ x = σ x := by simp [switch, hne]
      have : y = sel σ x c₁ c₂ := by rw [hc]; unfold sel; rw [hsw]
      exact hx (losing_of_edge ⟨c₁, c₂, Or.inr ⟨h, this⟩⟩ hy)
  obtain ⟨w, hw, hwi⟩ := hv
  have : ∀ y, Relation.ReflTransGen (C.StratEdge (C.switch σ)) v y → ¬ C.Losing σ y := by
    intro y hy
    induction hy with
    | refl => exact hnot
    | tail _ hst ih => exact closed _ _ hst ih
  exact this w hw ⟨w, Relation.ReflTransGen.refl, hwi⟩

/-- **Theorem 5.2 (ii).** Every switched gate lies outside `L_{σ'}`. -/
theorem switched_not_losing (σ : Fin n → Bool) (v : Fin n) (he : C.Escape σ v) :
    ¬ C.Losing (C.switch σ) v := by
  classical
  intro hL
  obtain ⟨_, c₁, c₂, hnode, hout⟩ := he
  obtain ⟨c, hvc, hc⟩ := losing_gate hnode hL
  obtain ⟨d₁, d₂, h⟩ := hvc
  rcases h with ⟨h, _⟩ | ⟨h, rfl⟩
  · rw [hnode] at h; cases h
  rw [hnode] at h; injection h with _ e1 e2; subst e1; subst e2
  have hsw : C.switch σ v = !σ v := by
    simp [switch, show C.Escape σ v from ⟨‹_›, c₁, c₂, hnode, hout⟩]
  have hsel : sel (C.switch σ) v c₁ c₂ = unsel σ v c₁ c₂ := by
    unfold sel unsel; rw [hsw]; cases σ v <;> rfl
  rw [hsel] at hc
  exact hout (losing_antitone σ _ hc)

end MonCircuit


/-! ### The rank-biased escape bound -/

namespace MonCircuit

variable {n : ℕ}

/-- The Strahler rank (Definition 5.3): inputs have rank `0`; a gate whose two children coincide
has the rank of that child; a gate with distinct children of ranks `r₁ ≥ r₂` has rank `r₁` if
`r₁ > r₂` and `r₁ + 1` if `r₁ = r₂`. -/
def sr (C : MonCircuit n) (v : Fin n) : ℕ :=
  match h : C.node v with
  | .input _ => 0
  | .gate a c₁ c₂ =>
    have := C.topo v a c₁ c₂ h
    if c₁ = c₂ then sr C c₁ else
      if sr C c₁ = sr C c₂ then sr C c₁ + 1 else max (sr C c₁) (sr C c₂)
termination_by v
decreasing_by all_goals first | exact this.1 | exact this.2

/-- The rank-biased start: every OR gate selects a child of maximum rank. -/
def rankStart (C : MonCircuit n) (v : Fin n) : Bool :=
  match C.node v with
  | .gate _ c₁ c₂ => decide (C.sr c₁ < C.sr c₂)
  | .input _ => false

/-- The strategy after `k` rounds of simultaneous escape switching from the rank-biased start. -/
noncomputable def strat (C : MonCircuit n) (k : ℕ) : Fin n → Bool :=
  (C.switch)^[k] C.rankStart

variable {C : MonCircuit n}

lemma sr_gate {v c₁ c₂ : Fin n} {a : Bool} (h : C.node v = .gate a c₁ c₂) :
    C.sr v = if c₁ = c₂ then C.sr c₁ else
      if C.sr c₁ = C.sr c₂ then C.sr c₁ + 1 else max (C.sr c₁) (C.sr c₂) := by
  rw [sr]; split <;> simp_all

lemma sr_children {v c₁ c₂ : Fin n} {a : Bool} (h : C.node v = .gate a c₁ c₂) :
    C.sr c₁ ≤ C.sr v ∧ C.sr c₂ ≤ C.sr v := by
  rw [sr_gate h]
  by_cases he : c₁ = c₂
  · subst he; simp
  · simp only [he, if_false]; split_ifs <;> omega

lemma edge_or {σ : Fin n → Bool} {v c c₁ c₂ : Fin n} (h : C.node v = .gate false c₁ c₂)
    (he : C.StratEdge σ v c) : c = sel σ v c₁ c₂ := by
  obtain ⟨d₁, d₂, hd⟩ := he
  rcases hd with ⟨hd, _⟩ | ⟨hd, rfl⟩
  · rw [h] at hd; cases hd
  · rw [h] at hd; injection hd with _ e1 e2; subst e1; subst e2; rfl

lemma edge_and {σ : Fin n → Bool} {v c c₁ c₂ : Fin n} (h : C.node v = .gate true c₁ c₂)
    (he : C.StratEdge σ v c) : c = c₁ ∨ c = c₂ := by
  obtain ⟨d₁, d₂, hd⟩ := he
  rcases hd with ⟨hd, hc⟩ | ⟨hd, _⟩
  · rw [h] at hd; injection hd with _ e1 e2; subst e1; subst e2; exact hc
  · rw [h] at hd; cases hd

lemma not_losing_of_true_input {σ : Fin n → Bool} {v : Fin n} (h : C.node v = .input true) :
    ¬ C.Losing σ v := by
  rintro ⟨w, hw, hwi⟩
  rcases Relation.ReflTransGen.cases_head hw with rfl | ⟨c, hvc, _⟩
  · rw [h] at hwi; cases hwi
  · obtain ⟨d₁, d₂, hd⟩ := hvc
    rcases hd with ⟨hd, _⟩ | ⟨hd, _⟩ <;> rw [h] at hd <;> cases hd

lemma strat_succ (k : ℕ) : C.strat (k + 1) = C.switch (C.strat k) := by
  unfold strat; rw [Function.iterate_succ_apply']

lemma strat_mono {v : Fin n} {k : ℕ} (hk : ¬ C.Losing (C.strat k) v) :
    ∀ j, k ≤ j → ¬ C.Losing (C.strat j) v := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => exact hk
  | succ j _ ih =>
    rw [strat_succ]; exact fun h => ih (losing_antitone _ _ h)

/-- An OR gate keeps its initial selection until it leaves the losing set. -/
lemma strat_track (v : Fin n) :
    ∀ k, C.strat k v = C.rankStart v ∨ ¬ C.Losing (C.strat k) v := by
  classical
  intro k
  induction k with
  | zero => left; rfl
  | succ k ih =>
    rw [strat_succ]
    rcases ih with h | h
    · by_cases he : C.Escape (C.strat k) v
      · right; exact switched_not_losing _ _ he
      · left; simp [switch, he, h]
    · right; exact fun h' => h (losing_antitone _ _ h')

/-- **Theorem 5.5 (rank-biased escape bound).** Starting from the strategy that selects at every
OR gate a child of maximum Strahler rank, after `k ≥ sr(v)` rounds of simultaneous escape
switching every true vertex `v` lies outside the losing set. -/
theorem true_not_losing (v : Fin n) (hv : C.val v = true) :
    ∀ k, C.sr v ≤ k → ¬ C.Losing (C.strat k) v := by
  induction v using WellFoundedLT.induction with
  | _ v ih =>
  intro k hk
  cases hnode : C.node v with
  | input b =>
    rw [C.val_input hnode] at hv; subst hv
    exact not_losing_of_true_input hnode
  | gate a c₁ c₂ =>
    have ht := C.topo v a c₁ c₂ hnode
    have hsr := sr_children hnode
    rw [C.val_gate hnode] at hv
    cases a
    · -- OR gate
      simp only [Bool.false_eq_true, if_false, Bool.or_eq_true] at hv
      -- the initially selected child `x` has maximum rank
      have hstart : C.rankStart v = decide (C.sr c₁ < C.sr c₂) := by
        unfold rankStart; rw [hnode]
      have hrank := sr_gate hnode
      -- generic argument, given the selected child `x` and the other child `y`
      have key : ∀ x y : Fin n, x < v → y < v →
          (∀ σ : Fin n → Bool, σ v = C.rankStart v → sel σ v c₁ c₂ = x ∧ unsel σ v c₁ c₂ = y) →
          C.sr y ≤ C.sr x → C.sr x ≤ C.sr v → (x ≠ y → C.sr y + 1 ≤ C.sr v) →
          (C.val x = true ∨ C.val y = true) → ¬ C.Losing (C.strat k) v := by
        intro x y hx hy hsel hyx hxv hyv hval
        by_cases hxt : C.val x = true
        · have hxk := ih x hx hxt k (by omega)
          rcases strat_track v k with hs | hs
          · intro hL
            obtain ⟨c, hvc, hc⟩ := losing_gate hnode hL
            have := edge_or hnode hvc
            rw [(hsel _ hs).1] at this
            exact hxk (this ▸ hc)
          · exact hs
        · have hyt : C.val y = true := by tauto
          have hxy : x ≠ y := fun e => hxt (e ▸ hyt)
          set k' := C.sr y
          have hyk := ih y hy hyt k' le_rfl
          have hstep : ¬ C.Losing (C.strat (k' + 1)) v := by
            rcases strat_track v k' with hs | hs
            · by_cases hL : C.Losing (C.strat k') v
              · have hesc : C.Escape (C.strat k') v :=
                  ⟨hL, c₁, c₂, hnode, by rw [(hsel _ hs).2]; exact hyk⟩
                rw [strat_succ]; exact switched_not_losing _ _ hesc
              · exact strat_mono hL _ (by omega)
            · exact strat_mono hs _ (by omega)
          exact strat_mono hstep k (by have := hyv hxy; omega)
      by_cases hlt : C.sr c₁ < C.sr c₂
      · refine key c₂ c₁ ht.2 ht.1 (fun σ hσ => ?_) (by omega) hsr.2 ?_ (by tauto)
        · rw [hstart, decide_eq_true hlt] at hσ; simp [sel, unsel, hσ]
        · intro hne; rw [hrank, if_neg (Ne.symm hne)]; split_ifs <;> omega
      · refine key c₁ c₂ ht.1 ht.2 (fun σ hσ => ?_) (by omega) hsr.1 ?_ hv
        · rw [hstart, decide_eq_false hlt] at hσ; simp [sel, unsel, hσ]
        · intro hne; rw [hrank, if_neg hne]; split_ifs <;> omega
    · -- AND gate: both children are true
      simp only [if_true, Bool.and_eq_true] at hv
      have h1 := ih c₁ ht.1 hv.1 k (by omega)
      have h2 := ih c₂ ht.2 hv.2 k (by omega)
      intro hL
      obtain ⟨c, hvc, hc⟩ := losing_gate hnode hL
      rcases edge_and hnode hvc with rfl | rfl
      · exact h1 hc
      · exact h2 hc

/-- **Theorem 5.5, conclusion.** If every vertex has Strahler rank at most `r`, then after `r`
rounds the losing set is exactly the set of false vertices, there is no escape, and the output
`o` is decided by membership in `L_r`. So the circuit is decided after computing at most `r + 1`
losing sets `L_0, …, L_r`. -/
theorem rank_bound (r : ℕ) (hr : ∀ v, C.sr v ≤ r) :
    (∀ v, C.Losing (C.strat r) v ↔ C.val v = false) ∧ (∀ v, ¬ C.Escape (C.strat r) v) := by
  have hL : ∀ v, C.Losing (C.strat r) v ↔ C.val v = false := by
    intro v
    constructor
    · intro h
      by_contra hne
      exact true_not_losing v (by simpa using hne) r (hr v) h
    · intro h
      by_contra hne
      have := val_true_of_not_losing _ v hne
      rw [h] at this; cases this
  refine ⟨hL, ?_⟩
  rintro v ⟨hv, c₁, c₂, hnode, hout⟩
  have hvf := (hL v).mp hv
  rw [C.val_gate hnode] at hvf
  simp only [Bool.false_eq_true, if_false, Bool.or_eq_false_iff] at hvf
  apply hout
  rw [hL]
  unfold unsel; split_ifs
  · exact hvf.1
  · exact hvf.2

end MonCircuit

end GC.FlowCircuits
