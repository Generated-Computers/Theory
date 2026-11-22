import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Cases
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Order.Lattice.Nat

/-!
# Shared definitions for result family 005 (portals, separators and frontiers)

* the Horton–Strahler combination of two ranks;
* the balanced interval tree on the stages `lo, …, hi` (nodes are intervals `(lo, hi)`),
  its height, and the assignment of a write–read edge `(s, t)` to the unique node whose left
  child contains `s` and whose right child contains `t`.
-/

namespace GC.Portals

/-- Horton–Strahler combination of the ranks of the two premises of a binary rule. -/
def strahler (r₁ r₂ : ℕ) : ℕ := if r₁ = r₂ then r₁ + 1 else max r₁ r₂

theorem strahler_mono {a b a' b' : ℕ} (ha : a ≤ a') (hb : b ≤ b') :
    strahler a b ≤ strahler a' b' := by
  unfold strahler
  split_ifs <;> omega

theorem le_strahler_left (a b : ℕ) : a ≤ strahler a b := by
  unfold strahler; split_ifs <;> omega

theorem le_strahler_right (a b : ℕ) : b ≤ strahler a b := by
  unfold strahler; split_ifs <;> omega

/-! ## The balanced interval tree -/

/-- The split point of the interval `[lo, hi]`. -/
def mid (lo hi : ℕ) : ℕ := (lo + hi) / 2

/-- The nodes of the balanced interval tree with root interval `[lo, hi]`. -/
def treeNodes (lo hi : ℕ) : Finset (ℕ × ℕ) :=
  if lo < hi then
    insert (lo, hi) (treeNodes lo (mid lo hi) ∪ treeNodes (mid lo hi + 1) hi)
  else {(lo, hi)}
termination_by hi - lo
decreasing_by all_goals (unfold mid; omega)

/-- The height of the balanced interval tree with root interval `[lo, hi]`. -/
def treeHeight (lo hi : ℕ) : ℕ :=
  if lo < hi then
    max (treeHeight lo (mid lo hi)) (treeHeight (mid lo hi + 1) hi) + 1
  else 0
termination_by hi - lo
decreasing_by all_goals (unfold mid; omega)

/-- The edge `e = (s, t)` is assigned to the node `v = (lo, hi)`: `v` is internal, its left child
`[lo, mid]` contains `s` and its right child `[mid + 1, hi]` contains `t`. -/
def Assigned (v e : ℕ × ℕ) : Prop :=
  v.1 < v.2 ∧ v.1 ≤ e.1 ∧ e.1 ≤ mid v.1 v.2 ∧ mid v.1 v.2 < e.2 ∧ e.2 ≤ v.2

instance (v e : ℕ × ℕ) : Decidable (Assigned v e) := by unfold Assigned; infer_instance

/-- The internal nodes on the path from the root `[lo, hi]` to the leaf `τ`. -/
def pathNodes (lo hi τ : ℕ) : Finset (ℕ × ℕ) :=
  if lo < hi then
    insert (lo, hi)
      (if τ ≤ mid lo hi then pathNodes lo (mid lo hi) τ else pathNodes (mid lo hi + 1) hi τ)
  else ∅
termination_by hi - lo
decreasing_by all_goals (unfold mid; omega)

theorem treeNodes_eq (lo hi : ℕ) : treeNodes lo hi =
    if lo < hi then
      insert (lo, hi) (treeNodes lo (mid lo hi) ∪ treeNodes (mid lo hi + 1) hi)
    else {(lo, hi)} := by
  rw [treeNodes]

theorem treeHeight_eq (lo hi : ℕ) : treeHeight lo hi =
    if lo < hi then
      max (treeHeight lo (mid lo hi)) (treeHeight (mid lo hi + 1) hi) + 1
    else 0 := by
  rw [treeHeight]

theorem pathNodes_eq (lo hi τ : ℕ) : pathNodes lo hi τ =
    if lo < hi then
      insert (lo, hi)
        (if τ ≤ mid lo hi then pathNodes lo (mid lo hi) τ else pathNodes (mid lo hi + 1) hi τ)
    else ∅ := by
  rw [pathNodes]

/-- The height of the balanced interval tree on `n ≥ 1` stages is `⌈log₂ n⌉`. -/
theorem treeHeight_eq_clog (lo hi : ℕ) (h : lo ≤ hi) :
    treeHeight lo hi = Nat.clog 2 (hi + 1 - lo) := by
  induction' hn : hi - lo using Nat.strong_induction_on with k ih generalizing lo hi
  rw [treeHeight_eq]
  split_ifs with hlt
  · have h1 := ih (mid lo hi - lo) (by unfold mid; omega) lo (mid lo hi) (by unfold mid; omega) rfl
    have h2 := ih (hi - (mid lo hi + 1)) (by unfold mid; omega) (mid lo hi + 1) hi
      (by unfold mid; omega) rfl
    have hc : Nat.clog 2 (hi + 1 - lo) = Nat.clog 2 ((hi + 1 - lo + 2 - 1) / 2) + 1 :=
      Nat.clog_of_two_le Nat.one_lt_two (by omega)
    rw [h1, h2, hc]
    have e1 : mid lo hi + 1 - lo = (hi + 1 - lo + 2 - 1) / 2 := by unfold mid; omega
    have e2 : hi + 1 - (mid lo hi + 1) ≤ mid lo hi + 1 - lo := by unfold mid; omega
    rw [max_eq_left (Nat.clog_mono_right 2 e2), e1]
  · have : hi + 1 - lo = 1 := by omega
    rw [this, Nat.clog_one_right]

theorem mem_treeNodes_bounds {lo hi : ℕ} {v : ℕ × ℕ} (hv : v ∈ treeNodes lo hi) :
    lo ≤ v.1 ∧ v.2 ≤ hi := by
  induction' hn : hi - lo using Nat.strong_induction_on with k ih generalizing lo hi
  rw [treeNodes_eq] at hv
  split_ifs at hv with hlt
  · simp only [Finset.mem_insert, Finset.mem_union] at hv
    rcases hv with rfl | hv | hv
    · exact ⟨le_rfl, le_rfl⟩
    · have := ih _ (by unfold mid; omega) hv rfl
      unfold mid at this; omega
    · have := ih _ (by unfold mid; omega) hv rfl
      unfold mid at this; omega
  · simp at hv; subst hv; exact ⟨le_rfl, le_rfl⟩

theorem mem_treeNodes_le {lo hi : ℕ} (h : lo ≤ hi) {v : ℕ × ℕ} (hv : v ∈ treeNodes lo hi) :
    v.1 ≤ v.2 := by
  induction' hn : hi - lo using Nat.strong_induction_on with k ih generalizing lo hi
  rw [treeNodes_eq] at hv
  split_ifs at hv with hlt
  · simp only [Finset.mem_insert, Finset.mem_union] at hv
    rcases hv with rfl | hv | hv
    · exact h
    · exact ih _ (by unfold mid; omega) (by unfold mid; omega) hv rfl
    · exact ih _ (by unfold mid; omega) (by unfold mid; omega) hv rfl
  · simp at hv; subst hv; exact h

/-- Every edge is assigned to at most one node of the tree. -/
theorem card_assigned_le_one (lo hi : ℕ) (e : ℕ × ℕ) :
    ((treeNodes lo hi).filter (fun v => Assigned v e)).card ≤ 1 := by
  rw [Finset.card_le_one]
  induction' hn : hi - lo using Nat.strong_induction_on with k ih generalizing lo hi
  intro a ha b hb
  simp only [Finset.mem_filter] at ha hb
  obtain ⟨ha, haA⟩ := ha
  obtain ⟨hb, hbA⟩ := hb
  rw [treeNodes_eq] at ha hb
  split_ifs at ha hb with hlt
  · simp only [Finset.mem_insert, Finset.mem_union] at ha hb
    have hL := ih (mid lo hi - lo) (by unfold mid; omega) lo (mid lo hi) rfl
    have hR := ih (hi - (mid lo hi + 1)) (by unfold mid; omega) (mid lo hi + 1) hi rfl
    simp only [Finset.mem_filter] at hL hR
    unfold Assigned at haA hbA
    rcases ha with rfl | ha | ha <;> rcases hb with rfl | hb | hb
    · rfl
    · have := mem_treeNodes_bounds hb; simp at haA; omega
    · have := mem_treeNodes_bounds hb; simp at haA; omega
    · have := mem_treeNodes_bounds ha; simp at hbA; omega
    · exact hL a ⟨ha, haA⟩ b ⟨hb, hbA⟩
    · have h1 := mem_treeNodes_bounds ha; have h2 := mem_treeNodes_bounds hb; omega
    · have := mem_treeNodes_bounds ha; simp at hbA; omega
    · have h1 := mem_treeNodes_bounds ha; have h2 := mem_treeNodes_bounds hb; omega
    · exact hR a ⟨ha, haA⟩ b ⟨hb, hbA⟩
  · simp at ha hb; rw [ha, hb]

theorem card_pathNodes_le (lo hi τ : ℕ) : (pathNodes lo hi τ).card ≤ treeHeight lo hi := by
  induction' hn : hi - lo using Nat.strong_induction_on with k ih generalizing lo hi
  rw [pathNodes_eq, treeHeight_eq]
  split_ifs with hlt hτ
  · refine (Finset.card_insert_le _ _).trans ?_
    have := ih (mid lo hi - lo) (by unfold mid; omega) lo (mid lo hi) rfl
    omega
  · refine (Finset.card_insert_le _ _).trans ?_
    have := ih (hi - (mid lo hi + 1)) (by unfold mid; omega) (mid lo hi + 1) hi rfl
    omega
  · simp

/-- An edge of the interval `[lo, hi]` crossing the cut `τ` is assigned to a node on the path
from the root to the leaf `τ`. -/
theorem exists_pathNode_assigned (lo hi τ : ℕ) (e : ℕ × ℕ)
    (h1 : lo ≤ e.1) (h2 : e.1 ≤ τ) (h3 : τ < e.2) (h4 : e.2 ≤ hi) :
    ∃ v ∈ pathNodes lo hi τ, Assigned v e := by
  induction' hn : hi - lo using Nat.strong_induction_on with k ih generalizing lo hi
  rw [pathNodes_eq]
  have hlt : lo < hi := by omega
  rw [if_pos hlt]
  by_cases hA : Assigned (lo, hi) e
  · exact ⟨(lo, hi), Finset.mem_insert_self _ _, hA⟩
  · unfold Assigned at hA
    simp only at hA
    split_ifs with hτ
    · obtain ⟨v, hv, hvA⟩ := ih (mid lo hi - lo) (by unfold mid; omega) lo (mid lo hi)
        h1 (by omega) rfl
      exact ⟨v, Finset.mem_insert_of_mem hv, hvA⟩
    · obtain ⟨v, hv, hvA⟩ := ih (hi - (mid lo hi + 1)) (by unfold mid; omega) (mid lo hi + 1) hi
        (by omega) h4 rfl
      exact ⟨v, Finset.mem_insert_of_mem hv, hvA⟩

theorem pathNodes_subset (lo hi τ : ℕ) : pathNodes lo hi τ ⊆ treeNodes lo hi := by
  induction' hn : hi - lo using Nat.strong_induction_on with k ih generalizing lo hi
  rw [pathNodes_eq, treeNodes_eq]
  split_ifs with hlt hτ
  · exact Finset.insert_subset_insert _ ((ih _ (by unfold mid; omega) lo _ rfl).trans
      Finset.subset_union_left)
  · exact Finset.insert_subset_insert _ ((ih _ (by unfold mid; omega) _ hi rfl).trans
      Finset.subset_union_right)
  · exact Finset.empty_subset _

/-- An internal tree node whose interval contains `τ` lies on the path to the leaf `τ`. -/
theorem mem_pathNodes_of_mem {lo hi τ : ℕ} {v : ℕ × ℕ} (hv : v ∈ treeNodes lo hi)
    (hint : v.1 < v.2) (h1 : v.1 ≤ τ) (h2 : τ ≤ v.2) : v ∈ pathNodes lo hi τ := by
  induction' hn : hi - lo using Nat.strong_induction_on with k ih generalizing lo hi
  rw [treeNodes_eq] at hv
  by_cases hlt : lo < hi
  · rw [if_pos hlt] at hv
    rw [pathNodes_eq, if_pos hlt]
    simp only [Finset.mem_insert, Finset.mem_union] at hv
    rcases hv with hv | hv | hv
    · rw [hv]; exact Finset.mem_insert_self _ _
    · have hb := mem_treeNodes_bounds hv
      rw [if_pos (show τ ≤ mid lo hi by omega)]
      exact Finset.mem_insert_of_mem (ih _ (by unfold mid; omega) hv rfl)
    · have hb := mem_treeNodes_bounds hv
      rw [if_neg (show ¬ τ ≤ mid lo hi by omega)]
      exact Finset.mem_insert_of_mem (ih _ (by unfold mid; omega) hv rfl)
  · rw [if_neg hlt] at hv
    simp at hv; subst hv; simp at hint; omega

theorem mem_treeNodes_trans {lo hi : ℕ} {v w : ℕ × ℕ} (hv : v ∈ treeNodes lo hi)
    (hw : w ∈ treeNodes v.1 v.2) : w ∈ treeNodes lo hi := by
  induction' hn : hi - lo using Nat.strong_induction_on with k ih generalizing lo hi
  by_cases hlt : lo < hi
  · rw [treeNodes_eq, if_pos hlt] at hv ⊢
    simp only [Finset.mem_insert, Finset.mem_union] at hv
    rcases hv with hv | hv | hv
    · subst hv; rw [treeNodes_eq, if_pos hlt] at hw; exact hw
    · exact Finset.mem_insert_of_mem (Finset.mem_union_left _
        (ih _ (by unfold mid; omega) hv rfl))
    · exact Finset.mem_insert_of_mem (Finset.mem_union_right _
        (ih _ (by unfold mid; omega) hv rfl))
  · rw [treeNodes_eq, if_neg hlt] at hv
    simp at hv; subst hv; exact hw

/-! ## The search over the rank `K` (one-shot criteria of 005c and 005e) -/

/-- The search of Corollary "One-shot criterion" (005c) and Corollary "Searching for the best
rank" (005e): after rank `K` it knows `β_K = min_{K' ≤ K} (K' + c K')` and stops at the first `K`
with `β_K ≤ K`. The first stopping rank is at most `Φ = min_K (K + c K)`. -/
theorem search_first_stop_le (c : ℕ → ℕ) (K₀ : ℕ)
    (hfirst : ∀ K < K₀, ¬ ∃ K' ≤ K, K' + c K' ≤ K) :
    K₀ ≤ sInf (Set.range fun K => K + c K) := by
  obtain ⟨K, hK⟩ : sInf (Set.range fun K => K + c K) ∈ Set.range fun K => K + c K :=
    Nat.sInf_mem ⟨0 + c 0, 0, rfl⟩
  by_contra h
  exact hfirst _ (Nat.lt_of_not_le h) ⟨K, by simp only at hK; omega, by simp only at hK; omega⟩

end GC.Portals
