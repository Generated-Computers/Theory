import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Prediction-alignment error equals collision energy

Manuscript 011a, Definition 6.1 and Lemma 6.2. Records `0, …, n-1` carry group identifiers
`g_i`; `f_h` is the size of group `h` and `B_h = ∑_{h' < h} f_{h'}`. The keys are
`y_i = (g_i, i)` in lexicographic order. Labels `q_i ∈ [0, f_{g_i} - 1]`, nondecreasing in `i`
inside each group, give the predictions `p_i = B_{g_i} + q_i`.
-/

namespace GC.Semisort

open Finset

/-- Group size `f_h = |{i : g_i = h}|`. -/
def groupFreq (g : ℕ → ℕ) (n h : ℕ) : ℕ := #((range n).filter fun i => g i = h)

/-- Group offset `B_h = ∑_{h' < h} f_{h'}`. -/
def groupOffset (g : ℕ → ℕ) (n h : ℕ) : ℕ := ∑ h' ∈ range h, groupFreq g n h'

/-- Prediction `p_i = B_{g_i} + q_i`. -/
def prediction (g q : ℕ → ℕ) (n i : ℕ) : ℕ := groupOffset g n (g i) + q i

/-- Definition 6.1: the prediction-alignment error
`PAE(y,p) = ∑_i |{j : y_j > y_i, p_j ≤ p_i}|` for the keys `y_i = (g_i, i)`. -/
def predictionAlignmentError (g q : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ i ∈ range n, #((range n).filter fun j =>
    (g i < g j ∨ (g i = g j ∧ i < j)) ∧ prediction g q n j ≤ prediction g q n i)

/-- Cell size `c_{h,r} = |{i : g_i = h, q_i = r}|`. -/
def cellSize (g q : ℕ → ℕ) (n : ℕ) (c : ℕ × ℕ) : ℕ :=
  #((range n).filter fun i => (g i, q i) = c)

/-- Collision energy `E_coll(q) = ∑_{h,r} C(c_{h,r}, 2)` (the sum over nonempty cells; empty
cells contribute `0`). -/
def collisionEnergy (g q : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ c ∈ (range n).image (fun i => (g i, q i)), (cellSize g q n c).choose 2

/-- The number of pairs `i < j` in a finite set of naturals is `C(|s|, 2)`. -/
theorem sum_card_filter_lt (s : Finset ℕ) :
    ∑ i ∈ s, #(s.filter fun j => i < j) = (#s).choose 2 := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
    have ha : a ∉ s := fun h => lt_irrefl a (hlt a h)
    rw [sum_insert ha, card_insert_of_notMem ha]
    have h0 : (insert a s).filter (fun j => a < j) = ∅ := by
      rw [filter_eq_empty_iff]
      intro x hx
      rcases mem_insert.1 hx with rfl | hx
      · exact lt_irrefl _
      · exact fun h => lt_asymm h (hlt x hx)
    have h1 : ∀ i ∈ s, #((insert a s).filter fun j => i < j) = #(s.filter fun j => i < j) + 1 := by
      intro i hi
      rw [filter_insert, ite_eq_left (hlt i hi), card_insert_of_notMem (by simp [ha])]
    rw [h0, card_empty, zero_add, sum_congr rfl h1, sum_add_distrib, ih, ← card_eq_sum_ones,
      Nat.choose_succ_succ', Nat.choose_one_right, add_comm]

theorem groupOffset_add_freq_le (g : ℕ → ℕ) (n : ℕ) {h h' : ℕ} (hh : h < h') :
    groupOffset g n h + groupFreq g n h ≤ groupOffset g n h' := by
  unfold groupOffset
  rw [← sum_range_succ]
  exact sum_le_sum_of_subset (range_subset_range.2 hh)

/-- **Lemma 6.2 (collision-energy identity).** For labels `q_i ≤ f_{g_i} - 1` that are
nondecreasing in `i` inside each group, the prediction-alignment error of the predictions
`p_i = B_{g_i} + q_i` equals the collision energy. -/
theorem predictionAlignmentError_eq_collisionEnergy (g q : ℕ → ℕ) (n : ℕ)
    (hq : ∀ i < n, q i < groupFreq g n (g i))
    (hmono : ∀ i < n, ∀ j < n, i < j → g i = g j → q i ≤ q j) :
    predictionAlignmentError g q n = collisionEnergy g q n := by
  -- each record contributes the number of later records in its own cell
  have hcell : ∀ i ∈ range n,
      #((range n).filter fun j =>
        (g i < g j ∨ (g i = g j ∧ i < j)) ∧ prediction g q n j ≤ prediction g q n i) =
      #(((range n).filter fun j => (g j, q j) = (g i, q i)).filter fun j => i < j) := by
    intro i hi
    rw [mem_range] at hi
    rw [filter_filter]
    congr 1
    apply filter_congr
    intro j hj
    rw [mem_range] at hj
    unfold prediction
    constructor
    · rintro ⟨hlex | ⟨hg, hij⟩, hp⟩
      · exfalso
        have h1 := groupOffset_add_freq_le g n hlex
        have h2 := hq i hi
        omega
      · have := hmono i hi j hj hij hg
        rw [hg] at hp
        refine ⟨?_, hij⟩
        rw [Prod.mk.injEq]; exact ⟨hg.symm, by omega⟩
    · rintro ⟨hc, hij⟩
      rw [Prod.mk.injEq] at hc
      refine ⟨Or.inr ⟨hc.1.symm, hij⟩, ?_⟩
      rw [hc.1, hc.2]
  unfold predictionAlignmentError collisionEnergy
  rw [sum_congr rfl hcell]
  rw [← sum_fiberwise_of_maps_to (g := fun i => (g i, q i))
    (t := (range n).image (fun i => (g i, q i))) (fun i hi => mem_image_of_mem _ hi)]
  apply sum_congr rfl
  intro c _
  unfold cellSize
  rw [← sum_card_filter_lt]
  apply sum_congr rfl
  intro i hi
  rw [(mem_filter.1 hi).2]

/-! ### Theorem 7.3 (density barrier) -/

/-- The collision energy of one group `s` under labels `q`: `∑_r C(c_r, 2)` over the labels `r`
that occur, `c_r = |{i ∈ s : q_i = r}|`. -/
def groupCollisionEnergy (s : Finset ℕ) (q : ℕ → ℕ) : ℕ :=
  ∑ r ∈ s.image q, (#(s.filter fun i => q i = r)).choose 2

/-- **Theorem 7.3 (density barrier).** If a group of size `f` is labeled with at most `k + 1`
distinct values, its collision energy is at least `(f²/(k+1) - f)/2`. (Monotonicity of the
labels is not needed.) -/
theorem density_barrier (s : Finset ℕ) (q : ℕ → ℕ) (k : ℕ) (hk : #(s.image q) ≤ k + 1) :
    ((#s : ℝ) ^ 2 / (k + 1) - #s) / 2 ≤ groupCollisionEnergy s q := by
  set c : ℕ → ℕ := fun r => #(s.filter fun i => q i = r) with hc
  have hsum : (#s : ℝ) = ∑ r ∈ s.image q, (c r : ℝ) := by
    rw [card_eq_sum_card_image q s]; push_cast; rfl
  have hE : (groupCollisionEnergy s q : ℝ) =
      ((∑ r ∈ s.image q, (c r : ℝ) ^ 2) - ∑ r ∈ s.image q, (c r : ℝ)) / 2 := by
    unfold groupCollisionEnergy
    push_cast
    rw [eq_div_iff two_ne_zero, ← sum_sub_distrib, sum_mul]
    apply sum_congr rfl
    intro r _
    rw [Nat.cast_choose_two]
    ring
  have hcs := sq_sum_le_card_mul_sum_sq (s := s.image q) (f := fun r => (c r : ℝ))
  have hk' : ((#(s.image q) : ℕ) : ℝ) ≤ k + 1 := by exact_mod_cast hk
  have hsq : (#s : ℝ) ^ 2 / (k + 1) ≤ ∑ r ∈ s.image q, (c r : ℝ) ^ 2 := by
    rw [div_le_iff₀ (by positivity), hsum]
    have h0 : 0 ≤ ∑ r ∈ s.image q, (c r : ℝ) ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
    nlinarith
  rw [hE, ← hsum]
  linarith

/-- Theorem 7.3, consequence: collision energy `≤ C f` with `f ≥ 1` forces
`k + 1 ≥ f / (2C + 1)`. -/
theorem density_barrier_count (s : Finset ℕ) (q : ℕ → ℕ) (k : ℕ) (hk : #(s.image q) ≤ k + 1)
    (C : ℝ) (hC : 0 ≤ C) (hE : (groupCollisionEnergy s q : ℝ) ≤ C * #s) :
    (#s : ℝ) / (2 * C + 1) ≤ k + 1 := by
  have h := density_barrier s q k hk
  have hk0 : (0 : ℝ) < k + 1 := by positivity
  rw [div_le_iff₀ (by linarith)]
  have h1 : (#s : ℝ) ^ 2 / (k + 1) ≤ (2 * C + 1) * #s := by linarith
  rw [div_le_iff₀ hk0] at h1
  rcases Nat.eq_zero_or_pos #s with h0 | h0
  · rw [h0]; push_cast; nlinarith
  · have hf : (0 : ℝ) < #s := by exact_mod_cast h0
    nlinarith

end GC.Semisort
