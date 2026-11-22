import GC.Computability.Semisort.CutContraction
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Crossing area and the padding counterexample

Manuscript 011b, Lemma 5.2 (crossing-area identity) and Proposition 5.3 (padding
counterexample), which refutes the source's inference "quadratic total edge span gives an
efficient parallel regime": any circuit `C'` followed by `m` gates reading `x_0` has total span
`≥ n²/4` and a perfect top cut (`q = 0`), while its prefix is the unrestricted circuit `C'`.
-/

namespace GC.Semisort

open Finset

/-! ### Lemma 5.2 -/

/-- `c(b) = |{i > b : π_i ≤ b}|`, the number of edges `(π_i, i)` crossing the cut `b`. -/
def crossCount (π : ℕ → ℕ) (n b : ℕ) : ℕ := #((Ioc b n).filter fun i => π i ≤ b)

/-- `c(b) + q(b) = n - b`. -/
theorem crossCount_add_cutRank (π : ℕ → ℕ) (n b : ℕ) :
    crossCount π n b + cutRank π b n = n - b := by
  rw [cutRank_eq_card, crossCount, add_comm]
  have := card_filter_add_card_filter_not (s := Ioc b n) (fun i => b < π i)
  simp only [not_lt] at this
  rw [this, Nat.card_Ioc]

/-- **Lemma 5.2 (crossing-area identity).** `∑_{b=0}^{n-1} c(b) = ∑_{i=1}^{n} (i - π_i)`.
(It holds for every parent array; for a shape, `i - π_i` is the true span of edge `i`.) -/
theorem crossing_area_identity (π : ℕ → ℕ) (n : ℕ) :
    ∑ b ∈ range n, crossCount π n b = ∑ i ∈ Icc 1 n, (i - π i) := by
  have h1 : ∀ b, crossCount π n b =
      ∑ i ∈ Icc 1 n, if π i ≤ b ∧ b < i then 1 else 0 := by
    intro b
    rw [crossCount, ← card_filter]
    congr 1
    ext i; simp only [mem_filter, mem_Ioc, mem_Icc]; omega
  simp_rw [h1]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  rw [mem_Icc] at hi
  rw [← card_filter]
  have : (range n).filter (fun b => π i ≤ b ∧ b < i) = Ico (π i) i := by
    ext b; simp only [mem_filter, mem_range, mem_Ico]; omega
  rw [this, Nat.card_Ico]

/-- Lemma 5.2, consequences: if `∑_i (i - π_i) ≥ λ n²` then some cut `b` has `c(b) ≥ λ n`, and
then `b + q(b) ≤ (1 - λ) n`. -/
theorem exists_heavy_cut {π : ℕ → ℕ} {n : ℕ} (hn : 1 ≤ n) (lam : ℝ)
    (h : lam * (n : ℝ) ^ 2 ≤ ((∑ i ∈ Icc 1 n, (i - π i) : ℕ) : ℝ)) :
    ∃ b < n, lam * n ≤ crossCount π n b ∧
      (b : ℝ) + cutRank π b n ≤ (1 - lam) * n := by
  have hc : ∃ b < n, lam * n ≤ crossCount π n b := by
    by_contra hne
    simp only [not_exists, not_and, not_le] at hne
    have hlt : ∑ b ∈ range n, (crossCount π n b : ℝ) < ∑ b ∈ range n, lam * (n : ℝ) :=
      sum_lt_sum_of_nonempty ⟨0, mem_range.2 (by omega)⟩
        fun b hb => hne b (mem_range.1 hb)
    rw [← Nat.cast_sum, crossing_area_identity π n, sum_const, card_range, nsmul_eq_mul] at hlt
    nlinarith
  obtain ⟨b, hb, hcb⟩ := hc
  refine ⟨b, hb, hcb, ?_⟩
  have hnat := crossCount_add_cutRank π n b
  have : b + cutRank π b n + crossCount π n b = n := by omega
  have hR : (b : ℝ) + cutRank π b n + crossCount π n b = n := by exact_mod_cast this
  nlinarith

/-! ### Proposition 5.3 -/

/-- Parent array of the padded circuit: the gates of `C'` (`i ≤ m`), then gates with `π_i = 0`. -/
def padParent (π : ℕ → ℕ) (m i : ℕ) : ℕ := if i ≤ m then π i else 0

/-- Tables of the padded circuit: those of `C'`, then arbitrary tables `H`. -/
def padGate (G H : ℕ → Bool → Bool → Bool) (m i : ℕ) : Bool → Bool → Bool :=
  if i ≤ m then G i else H i

/-- The NOR table. -/
def norGate : ℕ → Bool → Bool → Bool := fun _ u v => !(u || v)

theorem cutRank_padParent (π : ℕ → ℕ) (m k : ℕ) : cutRank (padParent π m) m k = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [cutRank_succ, ih, ite_eq_right]
    rintro ⟨h1, h2⟩
    simp only [padParent, ite_eq_right (show ¬ k + 1 ≤ m by omega)] at h2
    omega

/-- **Proposition 5.3 (padding counterexample).** Let `C'` be any binary-table sequential
circuit with `m ≥ 1` gates, and let `C` have `n = 2m` gates: those of `C'`, followed by `m`
gates with parent `0` and arbitrary tables `H`. Then `C` has a valid shape and
* (a) `∑_{i=1}^{n} (i - π_i) ≥ n²/4`;
* (b) the cut `b = m` has `q(m) = 0`, so `(b/n)^γ + (q(b)/n)^γ = 2^{-γ} < 1` for every `γ > 0`;
* (c) the values of `C'` are the first `m + 1` values of `C`. -/
theorem padding_counterexample (x0 : Bool) {π : ℕ → ℕ} (G H : ℕ → Bool → Bool → Bool)
    {m : ℕ} (hπ : IsShape m π) (hm : 1 ≤ m) :
    IsShape (2 * m) (padParent π m) ∧
    (2 * m) ^ 2 ≤ 4 * ∑ i ∈ Icc 1 (2 * m), (i - padParent π m i) ∧
    cutRank (padParent π m) m (2 * m) = 0 ∧
    (∀ γ : ℝ, 0 < γ →
      ((m : ℝ) / ((2 * m : ℕ) : ℝ)) ^ γ +
          ((cutRank (padParent π m) m (2 * m) : ℝ) / ((2 * m : ℕ) : ℝ)) ^ γ = (2 : ℝ) ^ (-γ) ∧
        (2 : ℝ) ^ (-γ) < 1) ∧
    ∀ j ≤ m, circuitValue x0 (padParent π m) (padGate G H m) j = circuitValue x0 π G j := by
  refine ⟨?_, ?_, cutRank_padParent π m _, ?_, ?_⟩
  · intro i hi1 hi2
    unfold padParent
    split_ifs with h
    · exact hπ i hi1 h
    · omega
  · -- the last `m` gates contribute at least `m (m+1)`
    have hsub : Icc (m + 1) (2 * m) ⊆ Icc 1 (2 * m) := by
      intro i; simp only [mem_Icc]; omega
    have h1 : ∑ i ∈ Icc (m + 1) (2 * m), (i - padParent π m i) ≤
        ∑ i ∈ Icc 1 (2 * m), (i - padParent π m i) := sum_le_sum_of_subset hsub
    have h2 : #(Icc (m + 1) (2 * m)) • (m + 1) ≤
        ∑ i ∈ Icc (m + 1) (2 * m), (i - padParent π m i) := by
      apply card_nsmul_le_sum
      intro i hi
      rw [mem_Icc] at hi
      simp only [padParent, ite_eq_right (show ¬ i ≤ m by omega)]
      omega
    rw [Nat.card_Icc, smul_eq_mul] at h2
    have h3 : 2 * m + 1 - (m + 1) = m := by omega
    rw [h3] at h2
    nlinarith
  · intro γ hγ
    rw [cutRank_padParent]
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have e : (m : ℝ) / ((2 * m : ℕ) : ℝ) = 2⁻¹ := by
      push_cast; field_simp
    rw [e, Nat.cast_zero, zero_div, Real.zero_rpow hγ.ne', add_zero, Real.inv_rpow (by norm_num),
      ← Real.rpow_neg (by norm_num)]
    exact ⟨rfl, Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)⟩
  · intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      rcases Nat.eq_zero_or_pos j with rfl | hpos
      · rw [circuitValue_zero, circuitValue_zero]
      obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      have hp := hπ (k + 1) (by omega) hj
      have hp' : padParent π m (k + 1) < k + 1 := by
        simp only [padParent, ite_eq_left hj]; exact hp
      rw [circuitValue_succ _ _ _ hp', circuitValue_succ _ _ _ hp]
      simp only [padParent, padGate, ite_eq_left hj]
      rw [ih k (by omega) (by omega), ih (π (k + 1)) hp (by omega)]

/-- Proposition 5.3, last claim: if `C'` is a Sequential NOR circuit (`x_0 = 1`, all tables NOR),
so is `C` when the appended tables are NOR, and the appended gates all have value `0`. -/
theorem padding_counterexample_nor {π : ℕ → ℕ} {m : ℕ} :
    padGate norGate norGate m = norGate ∧
    ∀ j, m < j → circuitValue true (padParent π m) (padGate norGate norGate m) j = false := by
  refine ⟨?_, ?_⟩
  · funext i; unfold padGate; split_ifs <;> rfl
  · intro j hj
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    have hp : padParent π m (k + 1) < k + 1 := by
      simp only [padParent, ite_eq_right (show ¬ k + 1 ≤ m by omega)]; omega
    rw [circuitValue_succ _ _ _ hp]
    simp only [padParent, ite_eq_right (show ¬ k + 1 ≤ m by omega), circuitValue_zero, padGate,
      norGate]
    simp

end GC.Semisort
