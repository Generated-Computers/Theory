import GC.Computability.RandomSeqNOR.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Smoothed instances: composition of smoothings and the gadgets (manuscript 001b, Section 3)

* Lemma 3.3 (composition of smoothings), as an exact identity of finite laws:
  `smoothKernel_comp`, `smoothLaw_comp`, `smoothing_upset`.
* Lemma 3.4 (gadgets `N` and `M`) and the 6-gate majority gadget `M'`:
  `gadget_N`, `gadget_M`, `gadget_M'`; the density facts used in Lemma 3.6:
  `gadget_N_has_one`, `gadget_M'_has_two_ones`.
-/

namespace GC.RandomSeqNOR

open Finset

/-! ### Lemma 3.3: composition of smoothings -/

/-- The law of one coordinate of the `ε`-smoothing: the pointer of gate `i` (with values in
`{0, …, i-1}`) is kept (`= j`) with probability `1 - ε` and resampled uniformly with probability
`ε`. `smoothKernel ε i j w` is the probability that the new pointer is `w`. -/
noncomputable def smoothKernel (ε : ℝ) (i j w : ℕ) : ℝ :=
  (1 - ε) * (if w = j then 1 else 0) + ε / i

/-- **Lemma 3.3 (one coordinate).** Applying `S_{ε'}` and then `S_ε` gives the law of
`S_{ε''}` with `1 - ε'' = (1 - ε)(1 - ε')`. -/
theorem smoothKernel_comp (ε ε' : ℝ) {i j v : ℕ} (hi : 0 < i) (hj : j < i) (hv : v < i) :
    ∑ w ∈ range i, smoothKernel ε' i j w * smoothKernel ε i w v =
      smoothKernel (1 - (1 - ε) * (1 - ε')) i j v := by
  have hi' : (i : ℝ) ≠ 0 := by exact_mod_cast hi.ne'
  simp only [smoothKernel]
  have e1 : ∀ w, ((1 - ε') * (if w = j then (1:ℝ) else 0) + ε' / i) *
      ((1 - ε) * (if v = w then 1 else 0) + ε / i) =
      (1 - ε') * (1 - ε) * ((if w = j then 1 else 0) * (if v = w then 1 else 0))
        + (1 - ε') * (ε / i) * (if w = j then 1 else 0)
        + ε' / i * (1 - ε) * (if v = w then 1 else 0) + ε' / i * (ε / i) := by
    intro w; ring
  simp only [e1, sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul]
  have s1 : ∑ w ∈ range i, ((if w = j then (1:ℝ) else 0) * (if v = w then 1 else 0)) =
      if v = j then 1 else 0 := by
    rw [sum_eq_single j]
    · by_cases h : v = j <;> simp [h]
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (mem_range.2 hj) h
  have s2 : ∑ w ∈ range i, (if w = j then (1:ℝ) else 0) = 1 := by
    rw [sum_ite_eq']; simp [hj]
  have s3 : ∑ w ∈ range i, (if v = w then (1:ℝ) else 0) = 1 := by
    rw [sum_ite_eq]; simp [hv]
  rw [s1, s2, s3]
  field_simp
  ring

/-- The law of the `ε`-smoothing of a base `j` of length `n`, as a function on parent arrays
`w` (with `w i ∈ {0, …, i}` the pointer of gate `i + 1`): the product of the one-coordinate laws
(the coordinates are independent). -/
noncomputable def smoothLaw (n : ℕ) (ε : ℝ) (j w : (i : Fin n) → Fin (i.1 + 1)) : ℝ :=
  ∏ i, smoothKernel ε (i.1 + 1) (j i) (w i)

/-- **Lemma 3.3.** `S_ε(S_{ε'}(j))` has the law of `S_{ε''}(j)`, where
`1 - ε'' = (1 - ε)(1 - ε')`: for every base `j` and array `v`,
`∑_w Pr[S_{ε'}(j) = w] Pr[S_ε(w) = v] = Pr[S_{ε''}(j) = v]`. -/
theorem smoothLaw_comp (n : ℕ) (ε ε' : ℝ) (j v : (i : Fin n) → Fin (i.1 + 1)) :
    ∑ w, smoothLaw n ε' j w * smoothLaw n ε w v = smoothLaw n (1 - (1 - ε) * (1 - ε')) j v := by
  simp only [smoothLaw, ← prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i (w : Fin (i.1 + 1)) =>
    smoothKernel ε' (i.1 + 1) (j i) w * smoothKernel ε (i.1 + 1) w (v i))]
  refine prod_congr rfl fun i _ => ?_
  rw [← smoothKernel_comp ε ε' (Nat.succ_pos _) (j i).2 (v i).2]
  rw [← Fin.sum_univ_eq_sum_range (fun w => smoothKernel ε' (i.1 + 1) (j i) w *
    smoothKernel ε (i.1 + 1) w (v i))]

/-- **Lemma 3.3, second claim (the noise levels form an up-set).** For `ε ≤ ε'' ≤ 1` there is
`ε' ∈ [0, 1]` with `1 - ε'' = (1 - ε)(1 - ε')`; so `S_{ε''} = S_ε ∘ S_{ε'}`. -/
theorem smoothing_upset {ε ε'' : ℝ} (h1 : ε ≤ ε'') (h2 : ε'' ≤ 1) :
    ∃ ε' : ℝ, 0 ≤ ε' ∧ ε' ≤ 1 ∧ ε'' = 1 - (1 - ε) * (1 - ε') := by
  rcases eq_or_lt_of_le (le_trans h1 h2) with h | h
  · have h'' : ε'' = 1 := le_antisymm h2 (h ▸ h1)
    exact ⟨1, zero_le_one, le_rfl, by rw [h'']; ring⟩
  · refine ⟨(ε'' - ε) / (1 - ε), div_nonneg (by linarith) (by linarith), ?_, ?_⟩
    · rw [div_le_one (by linarith)]; linarith
    · field_simp; ring

/-! ### Lemma 3.4: the gadgets -/

/-- Gates `k, …, k+3` carry the pointers `(0, a, 1, b)` of the gadget `N(a, b)`. -/
def CarriesN (P : Inst) (k a b : ℕ) : Prop :=
  P.j k = 0 ∧ P.j (k + 1) = a ∧ P.j (k + 2) = 1 ∧ P.j (k + 3) = b

/-- Gates `k, …, k+7` carry the pointers `(0, a, 1, b, b, k+1, c, k+3)` of the gadget
`M(a, b, c)`. -/
def CarriesM (P : Inst) (k a b c : ℕ) : Prop :=
  P.j k = 0 ∧ P.j (k + 1) = a ∧ P.j (k + 2) = 1 ∧ P.j (k + 3) = b ∧ P.j (k + 4) = b ∧
    P.j (k + 5) = k + 1 ∧ P.j (k + 6) = c ∧ P.j (k + 7) = k + 3

/-- Gates `k, …, k+5` carry the pointers `(a, a, c, k+1, b, k)` of the gadget `M'(a, b, c)`. -/
def CarriesM' (P : Inst) (k a b c : ℕ) : Prop :=
  P.j k = a ∧ P.j (k + 1) = a ∧ P.j (k + 2) = c ∧ P.j (k + 3) = k + 1 ∧ P.j (k + 4) = b ∧
    P.j (k + 5) = k

private theorem trace_step (P : Inst) (i q : ℕ) (h : P.j (i + 1) = q) :
    trace P (i + 1) = nor (trace P i) (trace P q) := by
  rw [trace_succ_eq_nor, h]

/-- **Lemma 3.4 (gadget `N`).** If gates `k, …, k+3` carry `N(a, b)`, then
`x*_{k+3} = NOR(x*_a, x*_b)`, whatever `x*_{k-1}`. -/
theorem gadget_N (P : Inst) {k a b : ℕ} (hk : 1 ≤ k) (h : CarriesN P k a b) :
    trace P (k + 3) = nor (trace P a) (trace P b) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  obtain ⟨h0, h1, h2, h3⟩ := h
  have v0 : trace P (m + 1) = nor (trace P m) 1 := by rw [trace_step P m 0 h0, trace_zero]
  have v1 : trace P (m + 2) = nor (nor (trace P m) 1) (trace P a) := by
    rw [trace_step P (m + 1) a h1, v0]
  have v2 : trace P (m + 3) = nor (nor (nor (trace P m) 1) (trace P a)) 0 := by
    rw [trace_step P (m + 2) 1 h2, v1, trace_one]
  have v3 : trace P (m + 4) = nor (nor (nor (nor (trace P m) 1) (trace P a)) 0) (trace P b) := by
    rw [trace_step P (m + 3) b h3, v2]
  rw [show m + 1 + 3 = m + 4 by ring, v3]
  generalize trace P m = x; generalize trace P a = y; generalize trace P b = z
  revert x y z; decide

/-- **Lemma 3.4 (gadget `M`).** If gates `k, …, k+7` carry `M(a, b, c)`, then
`x*_{k+7} = MAJ(x*_a, x*_b, x*_c)`, whatever `x*_{k-1}`. -/
theorem gadget_M (P : Inst) {k a b c : ℕ} (hk : 1 ≤ k) (h : CarriesM P k a b c) :
    trace P (k + 7) = maj (trace P a) (trace P b) (trace P c) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  have v0 : trace P (m + 1) = nor (trace P m) 1 := by rw [trace_step P m 0 h0, trace_zero]
  have v1 : trace P (m + 2) = nor (nor (trace P m) 1) (trace P a) := by
    rw [trace_step P (m + 1) a h1, v0]
  have v2 : trace P (m + 3) = nor (nor (nor (trace P m) 1) (trace P a)) 0 := by
    rw [trace_step P (m + 2) 1 h2, v1, trace_one]
  have v3 : trace P (m + 4) = nor (nor (nor (nor (trace P m) 1) (trace P a)) 0) (trace P b) := by
    rw [trace_step P (m + 3) b h3, v2]
  have v4 : trace P (m + 5) = nor (nor (nor (nor (nor (trace P m) 1) (trace P a)) 0)
      (trace P b)) (trace P b) := by
    rw [trace_step P (m + 4) b h4, v3]
  have v5 : trace P (m + 6) = nor (nor (nor (nor (nor (nor (trace P m) 1) (trace P a)) 0)
      (trace P b)) (trace P b)) (nor (nor (trace P m) 1) (trace P a)) := by
    rw [trace_step P (m + 5) (m + 2) h5, v4, v1]
  have v6 : trace P (m + 7) = nor (nor (nor (nor (nor (nor (nor (trace P m) 1) (trace P a)) 0)
      (trace P b)) (trace P b)) (nor (nor (trace P m) 1) (trace P a))) (trace P c) := by
    rw [trace_step P (m + 6) c h6, v5]
  have v7 : trace P (m + 8) = nor (nor (nor (nor (nor (nor (nor (nor (trace P m) 1)
      (trace P a)) 0) (trace P b)) (trace P b)) (nor (nor (trace P m) 1) (trace P a)))
      (trace P c)) (nor (nor (nor (nor (trace P m) 1) (trace P a)) 0) (trace P b)) := by
    rw [trace_step P (m + 7) (m + 4) h7, v6, v3]
  rw [show m + 1 + 7 = m + 8 by ring, v7]
  generalize trace P m = x; generalize trace P a = y; generalize trace P b = z
  generalize trace P c = w
  revert x y z w; decide

/-- **The 6-gate majority gadget `M'`.** If gates `k, …, k+5` carry `M'(a, b, c)` and
`c = k - 1`, then `x*_{k+5} = MAJ(x*_a, x*_b, x*_c)`, whatever the other values. -/
theorem gadget_M' (P : Inst) {k a b : ℕ} (hk : 1 ≤ k) (h : CarriesM' P k a b (k - 1)) :
    trace P (k + 5) = maj (trace P a) (trace P b) (trace P (k - 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h
  simp only [Nat.add_sub_cancel] at h2 ⊢
  have v0 : trace P (m + 1) = nor (trace P m) (trace P a) := trace_step P m a h0
  have v1 : trace P (m + 2) = nor (nor (trace P m) (trace P a)) (trace P a) := by
    rw [trace_step P (m + 1) a h1, v0]
  have v2 : trace P (m + 3) = nor (nor (nor (trace P m) (trace P a)) (trace P a))
      (trace P m) := by
    rw [trace_step P (m + 2) m h2, v1]
  have v3 : trace P (m + 4) = nor (nor (nor (nor (trace P m) (trace P a)) (trace P a))
      (trace P m)) (nor (nor (trace P m) (trace P a)) (trace P a)) := by
    rw [trace_step P (m + 3) (m + 2) h3, v2, v1]
  have v4 : trace P (m + 5) = nor (nor (nor (nor (nor (trace P m) (trace P a))
      (trace P a)) (trace P m)) (nor (nor (trace P m) (trace P a)) (trace P a)))
      (trace P b) := by
    rw [trace_step P (m + 4) b h4, v3]
  have v5 : trace P (m + 6) = nor (nor (nor (nor (nor (nor (trace P m) (trace P a))
      (trace P a)) (trace P m)) (nor (nor (trace P m) (trace P a)) (trace P a)))
      (trace P b)) (nor (trace P m) (trace P a)) := by
    rw [trace_step P (m + 5) (m + 1) h5, v4, v0]
  rw [show m + 1 + 5 = m + 6 by ring, v5]
  generalize trace P m = x; generalize trace P a = y; generalize trace P b = z
  revert x y z; decide

/-- Density fact of Lemma 3.6 for `N`: a gadget `N` that carries its pointers has a one among its
four positions. -/
theorem gadget_N_has_one (P : Inst) {k a b : ℕ} (hk : 1 ≤ k) (h : CarriesN P k a b) :
    trace P (k + 1) = 1 ∨ trace P (k + 2) = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  obtain ⟨-, -, h2, -⟩ := h
  rw [show m + 1 + 2 = (m + 2) + 1 by ring, trace_step P (m + 2) 1 h2, trace_one,
    show m + 1 + 1 = m + 2 by ring]
  generalize trace P (m + 2) = x
  revert x; decide

/-- Density fact of Lemma 3.6 for `M'`: a gadget `M'` (with `c = k - 1`) that carries its
pointers has at least two ones among its six positions, whatever `a, b, c`. -/
theorem gadget_M'_has_two_ones (P : Inst) {k a b : ℕ} (hk : 1 ≤ k)
    (h : CarriesM' P k a b (k - 1)) :
    2 ≤ ((range 6).filter (fun o => trace P (k + o) = 1)).card := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h
  simp only [Nat.add_sub_cancel] at h2
  have v0 : trace P (m + 1) = nor (trace P m) (trace P a) := trace_step P m a h0
  have v1 : trace P (m + 2) = nor (nor (trace P m) (trace P a)) (trace P a) := by
    rw [trace_step P (m + 1) a h1, v0]
  have v2 : trace P (m + 3) = nor (nor (nor (trace P m) (trace P a)) (trace P a))
      (trace P m) := by
    rw [trace_step P (m + 2) m h2, v1]
  have v3 : trace P (m + 4) = nor (nor (nor (nor (trace P m) (trace P a)) (trace P a))
      (trace P m)) (nor (nor (trace P m) (trace P a)) (trace P a)) := by
    rw [trace_step P (m + 3) (m + 2) h3, v2, v1]
  have v4 : trace P (m + 5) = nor (nor (nor (nor (nor (trace P m) (trace P a))
      (trace P a)) (trace P m)) (nor (nor (trace P m) (trace P a)) (trace P a)))
      (trace P b) := by
    rw [trace_step P (m + 4) b h4, v3]
  have v5 : trace P (m + 6) = nor (nor (nor (nor (nor (nor (trace P m) (trace P a))
      (trace P a)) (trace P m)) (nor (nor (trace P m) (trace P a)) (trace P a)))
      (trace P b)) (nor (trace P m) (trace P a)) := by
    rw [trace_step P (m + 5) (m + 1) h5, v4, v0]
  rw [card_filter]
  simp only [sum_range_succ, sum_range_zero]
  rw [show m + 1 + 0 = m + 1 by ring, show m + 1 + 1 = m + 2 by ring,
    show m + 1 + 2 = m + 3 by ring, show m + 1 + 3 = m + 4 by ring,
    show m + 1 + 4 = m + 5 by ring, show m + 1 + 5 = m + 6 by ring, v0, v1, v2, v3, v4, v5]
  generalize trace P m = x; generalize trace P a = y; generalize trace P b = z
  revert x y z; decide

end GC.RandomSeqNOR
