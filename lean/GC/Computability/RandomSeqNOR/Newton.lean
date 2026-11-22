import GC.Computability.RandomSeqNOR.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Monotone.Basic

/-!
# Newton's method over GF(2) for Sequential NOR (manuscript 001a, deterministic core)

`newton P x` is the Newton iterate `x⁺` of the paper, computed by forward substitution of
`x⁺₀ = 1`, `x⁺ᵢ = Gᵢ(x) + Σₖ ∂ₖGᵢ(x) (x⁺ₖ + xₖ)`, with `Gᵢ(y) = (1 + yᵢ₋₁)(1 + y_{jᵢ})` at a binary
gate and `Gᵢ(y) = 1 + yᵢ₋₁` at a NOT gate (Remark "NOT-gate convention").
-/

namespace GC.RandomSeqNOR

/-- One Newton round over `GF(2)`: the forward-substitution solution `x⁺` of the linearised
system at `x`. -/
def newton (P : Inst) (x : ℕ → ZMod 2) : ℕ → ZMod 2
  | 0 => 1
  | i + 1 =>
    if P.j (i + 1) = i then
      (1 + x i) + (newton P x i + x i)
    else
      (1 + x i) * (1 + x (P.j (i + 1)))
        + (1 + x (P.j (i + 1))) * (newton P x i + x i)
        + (1 + x i) * (newton P x (P.j (i + 1)) + x (P.j (i + 1)))
termination_by i => i
decreasing_by
  all_goals first
    | omega
    | exact P.j_lt (i + 1) (Nat.succ_pos i)

/-- The `t`-th Newton iterate from the start `x0`. -/
def newtonIter (P : Inst) (x0 : ℕ → ZMod 2) (t : ℕ) : ℕ → ZMod 2 := (newton P)^[t] x0

/-- The error vector `e = x ⊕ x*`. -/
def err (P : Inst) (x : ℕ → ZMod 2) (i : ℕ) : ZMod 2 := x i + trace P i

/-- The standard start `x⁽⁰⁾ = (1, 0, 0, …)`. -/
def stdStart (i : ℕ) : ZMod 2 := if i = 0 then 1 else 0

/-- A source of round `t` (for the iterate `x`): a binary gate both of whose inputs are wrong. -/
def IsSource (P : Inst) (x : ℕ → ZMod 2) (i : ℕ) : Prop :=
  0 < i ∧ ¬ IsNot P i ∧ err P x (i - 1) = 1 ∧ err P x (P.j i) = 1

theorem newton_zero (P : Inst) (x : ℕ → ZMod 2) : newton P x 0 = 1 := by rw [newton]

theorem newton_succ_of_isNot (P : Inst) (x : ℕ → ZMod 2) (i : ℕ) (h : IsNot P (i + 1)) :
    newton P x (i + 1) = (1 + x i) + (newton P x i + x i) := by
  rw [newton]; simp only [(isNot_succ_iff P i).1 h, ↓reduceIte]

theorem newton_succ_of_not_isNot (P : Inst) (x : ℕ → ZMod 2) (i : ℕ) (h : ¬ IsNot P (i + 1)) :
    newton P x (i + 1) = (1 + x i) * (1 + x (P.j (i + 1)))
        + (1 + x (P.j (i + 1))) * (newton P x i + x i)
        + (1 + x i) * (newton P x (P.j (i + 1)) + x (P.j (i + 1))) := by
  have h' : ¬ P.j (i + 1) = i := fun h' => h ((isNot_succ_iff P i).2 h')
  rw [newton]; simp only [h', ↓reduceIte]

theorem newtonIter_zero (P : Inst) (x0 : ℕ → ZMod 2) : newtonIter P x0 0 = x0 := rfl

theorem newtonIter_succ (P : Inst) (x0 : ℕ → ZMod 2) (t : ℕ) :
    newtonIter P x0 (t + 1) = newton P (newtonIter P x0 t) := by
  unfold newtonIter; rw [Function.iterate_succ_apply']

theorem newtonIter_succ' (P : Inst) (x0 : ℕ → ZMod 2) (t : ℕ) :
    newtonIter P x0 (t + 1) = newtonIter P (newton P x0) t := by
  unfold newtonIter; rw [Function.iterate_succ_apply]

theorem err_eq_zero_iff (P : Inst) (x : ℕ → ZMod 2) (i : ℕ) :
    err P x i = 0 ↔ x i = trace P i := zmod2_add_eq_zero_iff _ _

/-! ### Lemma 4.2 (error recursion) -/

/-- Lemma 4.2, position `0`: every Newton iterate is exact at position `0`. -/
theorem err_newton_zero (P : Inst) (x : ℕ → ZMod 2) : err P (newton P x) 0 = 0 := by
  rw [err, newton_zero, trace_zero]; decide

/-- Lemma 4.2, NOT gates: `e⁺ᵢ = e⁺ᵢ₋₁`. -/
theorem err_newton_of_isNot (P : Inst) (x : ℕ → ZMod 2) (i : ℕ) (h : IsNot P (i + 1)) :
    err P (newton P x) (i + 1) = err P (newton P x) i := by
  rw [err, err, newton_succ_of_isNot P x i h, trace_succ_of_isNot P i h]
  generalize x i = a
  generalize newton P x i = b
  generalize trace P i = c
  revert a b c; decide

/-- Lemma 4.2, binary gates:
`e⁺ᵢ = (1 + x_{jᵢ}) e⁺ᵢ₋₁ + (1 + xᵢ₋₁) e⁺_{jᵢ} + eᵢ₋₁ e_{jᵢ}`. -/
theorem err_newton_of_not_isNot (P : Inst) (x : ℕ → ZMod 2) (i : ℕ) (h : ¬ IsNot P (i + 1)) :
    err P (newton P x) (i + 1) =
      (1 + x (P.j (i + 1))) * err P (newton P x) i
        + (1 + x i) * err P (newton P x) (P.j (i + 1))
        + err P x i * err P x (P.j (i + 1)) := by
  simp only [err]
  rw [newton_succ_of_not_isNot P x i h, trace_succ]
  generalize x i = a
  generalize x (P.j (i + 1)) = b
  generalize newton P x i = c
  generalize newton P x (P.j (i + 1)) = d
  generalize trace P i = e
  generalize trace P (P.j (i + 1)) = f
  revert a b c d e f; decide

/-- The truth `x*` is a fixed point of the Newton map. -/
theorem newton_trace (P : Inst) : newton P (trace P) = trace P := by
  funext i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    cases i with
    | zero => rw [newton_zero, trace_zero]
    | succ i =>
      have hlt := P.j_lt (i + 1) (Nat.succ_pos i)
      by_cases h : IsNot P (i + 1)
      · rw [newton_succ_of_isNot P _ i h, trace_succ_of_isNot P i h, ih i (by omega)]
        generalize trace P i = a
        revert a; decide
      · rw [newton_succ_of_not_isNot P _ i h, ih i (by omega), ih _ hlt, trace_succ]
        generalize trace P i = a
        generalize trace P (P.j (i + 1)) = b
        revert a b; decide

/-! ### Lemma 4.3 (front identity) -/

/-- Lemma 4.3, first half: the error of the next round vanishes up to `i` when no gate `≤ i`
is a source. -/
theorem err_newton_eq_zero_of_no_source (P : Inst) (x : ℕ → ZMod 2) :
    ∀ i, (∀ k ≤ i, ¬ IsSource P x k) → err P (newton P x) i = 0 := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hs
    cases i with
    | zero => exact err_newton_zero P x
    | succ i =>
      have hlt := P.j_lt (i + 1) (Nat.succ_pos i)
      by_cases h : IsNot P (i + 1)
      · rw [err_newton_of_isNot P x i h]
        exact ih i (by omega) (fun k hk => hs k (by omega))
      · rw [err_newton_of_not_isNot P x i h, ih i (by omega) (fun k hk => hs k (by omega)),
          ih _ hlt (fun k hk => hs k (by omega))]
        have h1 : err P x i * err P x (P.j (i + 1)) = 0 := by
          apply zmod2_mul_eq_zero_of_not
          rintro ⟨h1, h2⟩
          exact hs (i + 1) le_rfl ⟨Nat.succ_pos i, h, by simpa using h1, h2⟩
        rw [h1]; ring

/-- Lemma 4.3, second half: at the first source `s`, the next error is `1`.
Together with `err_newton_eq_zero_of_no_source` this is `f_{t+1} = min S_t`. -/
theorem err_newton_eq_one_of_first_source (P : Inst) (x : ℕ → ZMod 2) (s : ℕ)
    (hs : IsSource P x s) (hmin : ∀ k < s, ¬ IsSource P x k) :
    err P (newton P x) s = 1 := by
  obtain ⟨hpos, hnot, h1, h2⟩ := hs
  obtain ⟨i, rfl⟩ : ∃ i, s = i + 1 := ⟨s - 1, by omega⟩
  have hlt := P.j_lt (i + 1) (Nat.succ_pos i)
  rw [err_newton_of_not_isNot P x i hnot,
    err_newton_eq_zero_of_no_source P x i (fun k hk => hmin k (by omega)),
    err_newton_eq_zero_of_no_source P x _ (fun k hk => hmin k (by omega))]
  simp only [Nat.add_sub_cancel] at h1
  rw [h1, h2]; ring

/-- Lemma 4.3, front growth `f_{t+1} ≥ f_t + 2`: if the error vanishes below `f`, the next error
vanishes below `f + 2`. -/
theorem front_growth (P : Inst) (x : ℕ → ZMod 2) (f : ℕ) (hf : ∀ k < f, err P x k = 0) :
    ∀ k < f + 2, err P (newton P x) k = 0 := by
  intro k hk
  apply err_newton_eq_zero_of_no_source
  rintro m hm ⟨hpos, hnot, h1, h2⟩
  have hlt := P.j_lt m hpos
  have hne : P.j m + 1 ≠ m := hnot
  have hA : ¬ m - 1 < f := fun h => by rw [hf _ h] at h1; exact absurd h1 (by decide)
  have hB : ¬ P.j m < f := fun h => by rw [hf _ h] at h2; exact absurd h2 (by decide)
  omega

/-- Iterating `front_growth`: `f_t ≥ f_0 + 2t`. -/
theorem front_growth_iter (P : Inst) (x0 : ℕ → ZMod 2) (f : ℕ) (hf : ∀ k < f, err P x0 k = 0) :
    ∀ t, ∀ k < f + 2 * t, err P (newtonIter P x0 t) k = 0 := by
  intro t
  induction t with
  | zero => simpa [newtonIter] using hf
  | succ t ih =>
    intro k hk
    rw [newtonIter_succ]
    exact front_growth P _ _ ih k (by omega)

/-- Once exact on `[0, n]`, Newton stays exact on `[0, n]`. -/
theorem newton_exact_of_exact (P : Inst) (x : ℕ → ZMod 2) (n : ℕ)
    (h : ∀ i ≤ n, x i = trace P i) : ∀ i ≤ n, newton P x i = trace P i := by
  intro i hi
  rw [← err_eq_zero_iff]
  exact front_growth P x (n + 1) (fun k hk => (err_eq_zero_iff _ _ _).2 (h k (by omega))) i
    (by omega)

theorem newtonIter_exact_mono (P : Inst) (x0 : ℕ → ZMod 2) (n : ℕ) {t t' : ℕ} (htt : t ≤ t')
    (h : ∀ i ≤ n, newtonIter P x0 t i = trace P i) :
    ∀ i ≤ n, newtonIter P x0 t' i = trace P i := by
  induction htt with
  | refl => exact h
  | step _ ih =>
    rw [newtonIter_succ]
    exact newton_exact_of_exact P _ n ih

/-- The number of rounds `T_n` until the iterate is exact on `[0, n]`. -/
noncomputable def exactRounds (P : Inst) (x0 : ℕ → ZMod 2) (n : ℕ) : ℕ :=
  sInf {t | ∀ i ≤ n, newtonIter P x0 t i = trace P i}

theorem exactRounds_le (P : Inst) (x0 : ℕ → ZMod 2) (n t : ℕ)
    (h : ∀ i ≤ n, newtonIter P x0 t i = trace P i) : exactRounds P x0 n ≤ t :=
  Nat.sInf_le h

/-- If the iterate is exact at round `T` but not at round `T - 1`, then `T_n = T`. -/
theorem exactRounds_eq (P : Inst) (x0 : ℕ → ZMod 2) (n T : ℕ)
    (h : ∀ i ≤ n, newtonIter P x0 T i = trace P i)
    (hlow : ∀ t < T, ∃ i ≤ n, newtonIter P x0 t i ≠ trace P i) :
    exactRounds P x0 n = T := by
  apply le_antisymm (exactRounds_le P x0 n T h)
  by_contra hc
  push Not at hc
  have hmem : exactRounds P x0 n ∈ {t | ∀ i ≤ n, newtonIter P x0 t i = trace P i} :=
    Nat.sInf_mem ⟨T, h⟩
  obtain ⟨i, hi, hne⟩ := hlow _ hc
  exact hne (hmem i hi)

/-! ### Adaptedness (Lemma 4.4, deterministic part) -/

/-- Newton iterates on `[0, n]` depend only on `j₁, …, jₙ` and on the start on `[0, n]`. -/
theorem newton_congr {P Q : Inst} {n : ℕ} (hj : ∀ i, 0 < i → i ≤ n → P.j i = Q.j i)
    {x y : ℕ → ZMod 2} (hxy : ∀ i ≤ n, x i = y i) :
    ∀ i ≤ n, newton P x i = newton Q y i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    cases i with
    | zero => rw [newton_zero, newton_zero]
    | succ i =>
      have hji := hj (i + 1) (Nat.succ_pos i) hi
      have hlt := P.j_lt (i + 1) (Nat.succ_pos i)
      by_cases h : IsNot P (i + 1)
      · have h' : IsNot Q (i + 1) := by unfold IsNot at *; omega
        rw [newton_succ_of_isNot P x i h, newton_succ_of_isNot Q y i h',
          ih i (by omega) (by omega), hxy i (by omega)]
      · have h' : ¬ IsNot Q (i + 1) := by unfold IsNot at *; omega
        rw [newton_succ_of_not_isNot P x i h, newton_succ_of_not_isNot Q y i h',
          ih i (by omega) (by omega), ih _ hlt (by omega), hxy i (by omega),
          hxy _ (by omega), hji]

theorem newtonIter_congr {P Q : Inst} {n : ℕ} (hj : ∀ i, 0 < i → i ≤ n → P.j i = Q.j i)
    {x y : ℕ → ZMod 2} (hxy : ∀ i ≤ n, x i = y i) (t : ℕ) :
    ∀ i ≤ n, newtonIter P x t i = newtonIter Q y t i := by
  induction t with
  | zero => exact hxy
  | succ t ih =>
    rw [newtonIter_succ, newtonIter_succ]
    exact newton_congr hj ih

end GC.RandomSeqNOR
