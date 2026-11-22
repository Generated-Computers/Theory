import GC.Combinatorics.GridCompilers.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Lattice.Nat
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# Row partitions and the cost `Γ` (shared by manuscripts 009b and 009c)

For an active rectangle with cells `β i j` (`1 ≤ i ≤ H`, `1 ≤ j ≤ W`), a column `j` *varies*
on the row interval `[a, b)` if `β i j ≠ β a j` for some `a < i < b`; the weight of the block
is `w(a, b) = 1 + v(a, b)` with `v(a, b)` the number of varying columns, and
`Γ(β) = min ∑_t w(r_{t-1}, r_t)` over partitions `1 = r_0 < r_1 < ⋯ < r_p = H + 1`.
A partition is encoded by the list of its block heights `r_t - r_{t-1}` (positive, sum `H`).
-/

namespace GC.GridCompilers

variable (W : ℕ) (β : ℕ → ℕ → Bool)

/-- The columns `1 ≤ j ≤ W` that vary on the row interval `[a, b)`. -/
def varCols (a b : ℕ) : Finset ℕ :=
  (Finset.Icc 1 W).filter (fun j => ∃ i ∈ Finset.Ioo a b, β i j ≠ β a j)

/-- The weight `w(a, b) = 1 + v(a, b)` of the row block `[a, b)`. -/
def blockWeight (a b : ℕ) : ℕ := 1 + (varCols W β a b).card

/-- The cost of the partition of rows `a, a + 1, …` into consecutive blocks of the given
heights. -/
def partitionCost : ℕ → List ℕ → ℕ
  | _, [] => 0
  | a, h :: hs => blockWeight W β a (a + h) + partitionCost (a + h) hs

/-- A partition of the rows `1, …, H` into consecutive blocks, given by its block heights. -/
def IsRowPartition (H : ℕ) (l : List ℕ) : Prop := (∀ h ∈ l, 1 ≤ h) ∧ l.sum = H

/-- `Γ(β)`: the least cost of a partition of the rows `1, …, H` into consecutive blocks. -/
noncomputable def Gamma (H : ℕ) : ℕ :=
  sInf {c | ∃ l, IsRowPartition H l ∧ partitionCost W β 1 l = c}

variable {W β}

theorem Gamma_le {H : ℕ} {l : List ℕ} (hl : IsRowPartition H l) :
    Gamma W β H ≤ partitionCost W β 1 l :=
  Nat.sInf_le ⟨l, hl, rfl⟩

theorem Gamma_spec (H : ℕ) :
    ∃ l, IsRowPartition H l ∧ partitionCost W β 1 l = Gamma W β H := by
  have hne : {c | ∃ l, IsRowPartition H l ∧ partitionCost W β 1 l = c}.Nonempty :=
    ⟨_, List.replicate H 1, ⟨fun h hh => by rw [(List.eq_of_mem_replicate hh)], by simp⟩, rfl⟩
  exact Nat.sInf_mem hne

theorem card_varCols_le (a b : ℕ) : (varCols W β a b).card ≤ W := by
  refine (Finset.card_filter_le _ _).trans ?_
  simp

theorem varCols_succ (a : ℕ) : varCols W β a (a + 1) = ∅ := by
  ext j; simp [varCols]; intro _ _ i h1 h2; omega

theorem partitionCost_replicate (n a : ℕ) :
    partitionCost W β a (List.replicate n 1) = n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, partitionCost, ih, blockWeight, varCols_succ]
    simp; omega

theorem one_le_partitionCost {a : ℕ} {l : List ℕ} (hl : l ≠ []) : 1 ≤ partitionCost W β a l := by
  cases l with
  | nil => exact absurd rfl hl
  | cons h hs => rw [partitionCost, blockWeight]; omega

/-- Rows `i` and `i'` carry different cell words on the columns `1, …, W`. -/
def RowsDiffer (W : ℕ) (β : ℕ → ℕ → Bool) (i i' : ℕ) : Prop :=
  ∃ j ∈ Finset.Icc 1 W, β i j ≠ β i' j

open Classical in
/-- The number of maximal segments of equal cell words among the rows `1, …, H`. -/
noncomputable def numSegments (W : ℕ) (β : ℕ → ℕ → Bool) (H : ℕ) : ℕ :=
  1 + ((Finset.Ico 1 H).filter (fun i => RowsDiffer W β i (i + 1))).card

open Classical in
/-- Number of segment boundaries `i` (rows `i`, `i+1` differ) with `a ≤ i < e`. -/
noncomputable def numBoundaries (W : ℕ) (β : ℕ → ℕ → Bool) (a e : ℕ) : ℕ :=
  ((Finset.Ico a e).filter (fun i => RowsDiffer W β i (i + 1))).card

/-- The key induction for `gamma_ge_min_segments`. -/
theorem partitionCost_ge_min (H d : ℕ)
    (hdist : ∀ i i', 1 ≤ i → i ≤ H → 1 ≤ i' → i' ≤ H → RowsDiffer W β i i' →
      d ≤ ((Finset.Icc 1 W).filter (fun j => β i j ≠ β i' j)).card) :
    ∀ (l : List ℕ) (a : ℕ), (∀ h ∈ l, 1 ≤ h) → l ≠ [] → 1 ≤ a → a + l.sum ≤ H + 1 →
      min (1 + numBoundaries W β a (a + l.sum - 1)) (d + 1) ≤ partitionCost W β a l := by
  classical
  intro l
  induction l with
  | nil => intro a _ h; exact absurd rfl h
  | cons h rest ih =>
    intro a hpos _ ha hsum
    have hh : 1 ≤ h := hpos h (by simp)
    simp only [List.sum_cons] at hsum ⊢
    rw [partitionCost]
    by_cases hvar : ∃ i ∈ Finset.Ioo a (a + h), RowsDiffer W β i a
    · -- the block contains a row differing from its first row
      obtain ⟨i, hi, hdiff⟩ := hvar
      rw [Finset.mem_Ioo] at hi
      have hd := hdist i a (by omega) (by omega) ha (by omega) hdiff
      have hsub : (Finset.Icc 1 W).filter (fun j => β i j ≠ β a j) ⊆ varCols W β a (a + h) := by
        intro j hj
        rw [Finset.mem_filter] at hj
        exact Finset.mem_filter.2 ⟨hj.1, i, Finset.mem_Ioo.2 hi, hj.2⟩
      have := Finset.card_le_card hsub
      rw [blockWeight]
      omega
    · push Not at hvar
      -- no boundary inside the block
      have hnob : ∀ i, a ≤ i → i + 1 < a + h → ¬ RowsDiffer W β i (i + 1) := by
        intro i h1 h2 hd
        obtain ⟨j, hj, hne⟩ := hd
        apply hne
        have e1 : ∀ k, a ≤ k → k < a + h → β k j = β a j := by
          intro k hk1 hk2
          rcases Nat.eq_or_lt_of_le hk1 with rfl | hk1
          · rfl
          · have := hvar k (Finset.mem_Ioo.2 ⟨hk1, hk2⟩)
            by_contra hc
            exact this ⟨j, hj, hc⟩
        rw [e1 i h1 (by omega), e1 (i + 1) (by omega) h2]
      have hzero : numBoundaries W β a (a + h - 1) = 0 := by
        rw [numBoundaries, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro i hi
        rw [Finset.mem_Ico] at hi
        exact hnob i hi.1 (by omega)
      rcases List.eq_nil_or_concat rest with rfl | hne
      · simp only [List.sum_nil, add_zero, partitionCost]
        rw [hzero, blockWeight]
        omega
      · have hrest : rest ≠ [] := by
          obtain ⟨L, b, rfl⟩ := hne; simp
        have hrsum : 1 ≤ rest.sum := by
          cases rest with
          | nil => exact absurd rfl hrest
          | cons r rs =>
            simp only [List.sum_cons]
            have := hpos r (by simp); omega
        have ih' := ih (a + h) (fun x hx => hpos x (by simp [hx])) hrest (by omega) (by omega)
        -- boundaries split
        have hsplit : numBoundaries W β a (a + (h + rest.sum) - 1) ≤
            1 + numBoundaries W β (a + h) (a + h + rest.sum - 1) := by
          unfold numBoundaries
          have hsub : (Finset.Ico a (a + (h + rest.sum) - 1)).filter
              (fun i => RowsDiffer W β i (i + 1)) ⊆
              insert (a + h - 1) ((Finset.Ico (a + h) (a + h + rest.sum - 1)).filter
                (fun i => RowsDiffer W β i (i + 1))) := by
            intro i hi
            rw [Finset.mem_filter, Finset.mem_Ico] at hi
            rw [Finset.mem_insert, Finset.mem_filter, Finset.mem_Ico]
            by_cases h1 : i + 1 < a + h
            · exact absurd hi.2 (hnob i hi.1.1 h1)
            · by_cases h2 : i = a + h - 1
              · left; exact h2
              · right; exact ⟨⟨by omega, by omega⟩, hi.2⟩
          exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _) |>.trans
            (by omega)
        rw [blockWeight]
        omega

/-- **Lower bound for `Γ`** (009c, Lemma 4.1). If the cell words of the rows `1, …, H`
pairwise differ, when they differ, in at least `d` columns, and the rows form `g` maximal
segments of equal cell words, then `Γ ≥ min(g, d + 1)`. -/
theorem gamma_ge_min_segments (H d : ℕ) (hH : 1 ≤ H)
    (hdist : ∀ i i', 1 ≤ i → i ≤ H → 1 ≤ i' → i' ≤ H → RowsDiffer W β i i' →
      d ≤ ((Finset.Icc 1 W).filter (fun j => β i j ≠ β i' j)).card) :
    min (numSegments W β H) (d + 1) ≤ Gamma W β H := by
  obtain ⟨l, ⟨hpos, hsum⟩, hcost⟩ := Gamma_spec (W := W) (β := β) H
  rw [← hcost]
  have hne : l ≠ [] := by rintro rfl; simp at hsum; omega
  have := partitionCost_ge_min H d hdist l 1 hpos hne le_rfl (by omega)
  rw [hsum, show 1 + H - 1 = H by omega] at this
  exact this

/-- **Bounds for `Γ`** (009b, Lemma 3.1): for `H ≥ 1`, `1 ≤ Γ(β) ≤ min(H, W + 1)`. -/
theorem gamma_bounds (H : ℕ) (hH : 1 ≤ H) :
    1 ≤ Gamma W β H ∧ Gamma W β H ≤ min H (W + 1) := by
  refine ⟨?_, le_min ?_ ?_⟩
  · obtain ⟨l, ⟨hpos, hsum⟩, hcost⟩ := Gamma_spec (W := W) (β := β) H
    rw [← hcost]
    apply one_le_partitionCost
    rintro rfl; simp at hsum; omega
  · calc Gamma W β H ≤ partitionCost W β 1 (List.replicate H 1) :=
          Gamma_le ⟨fun h hh => by rw [List.eq_of_mem_replicate hh], by simp⟩
      _ = H := partitionCost_replicate H 1
  · calc Gamma W β H ≤ partitionCost W β 1 [H] :=
          Gamma_le ⟨fun h hh => by simp at hh; omega, by simp⟩
      _ ≤ W + 1 := by
          simp only [partitionCost, blockWeight, add_zero]
          have := card_varCols_le (W := W) (β := β) 1 (1 + H)
          omega

end GC.GridCompilers
