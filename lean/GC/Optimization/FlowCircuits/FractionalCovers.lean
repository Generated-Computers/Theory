import GC.Optimization.FlowCircuits.Carrier
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.ChainOfFn
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Manuscript 003b: Fractional covers do not certify sequential hardness

* `CarrierGraph.weak_duality` : the inequality `δ(C) ≥ ∑ y_e` of Theorem 3.1 for every feasible
  pair of the path-flow dual (dual certificates are sound).
* `CarrierGraph.concentration`, `CarrierGraph.concentration_incomparable` : Theorem 4.2 (two-path
  concentration), as an exact finite averaging statement over the path distribution, with and
  without the factor two for incomparable parents.
* `factorTwo_example` : Example 4.3 (the factor two cannot be removed in general).
* `railGraph_load` : Theorem 5.1 and Proposition 5.2, `δ = h/2` for two unary rails of length `h`
  with readouts containing a perfect matching (the matched-rail mirage and the complete readout
  grid).
* `mirage_height` : Theorem 5.1, the least catalyst height of the matched-rail mirage is
  `⌈h/2⌉`.
-/

namespace GC.FlowCircuits

open Finset

namespace CarrierGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : CarrierGraph V)

/-- The load `ℓ_v = ∑_{e ∋ v} y_e` of a vertex. -/
def load (y : V × V → ℝ) (v : V) : ℝ :=
  ∑ e ∈ G.fusion, y e * ((if e.1 = v then 1 else 0) + (if e.2 = v then 1 else 0))

/-- The path marginal `p_v = ∑_{P ∋ v} λ_P` of a finitely supported path weighting. -/
def marg (Λ : Finset (List V)) (lam : List V → ℝ) (v : V) : ℝ :=
  ∑ P ∈ Λ, if v ∈ P then lam P else 0

/-- Feasibility for the path-flow fusion-packing dual of Theorem 3.1: `y ≥ 0`, `λ ≥ 0` supported
on directed paths with total mass at most one, and `∑_{e ∋ v} y_e ≤ p_v` for every `v`. -/
def DualFeasible (y : V × V → ℝ) (Λ : Finset (List V)) (lam : List V → ℝ) : Prop :=
  (∀ e, 0 ≤ y e) ∧ (∀ P ∈ Λ, G.IsPath P) ∧ (∀ P, 0 ≤ lam P) ∧ (∑ P ∈ Λ, lam P ≤ 1) ∧
    ∀ v, G.load y v ≤ marg Λ lam v

variable {G}

/-- **Theorem 3.1, weak duality.** For every primal-feasible `(x, d)` with `d ≥ 0` and every
dual-feasible `(y, λ)`, `∑_e y_e ≤ d`. Hence every dual-feasible pair certifies `δ(C) ≥ ∑ y_e`. -/
theorem weak_duality {x : V → ℝ} {d : ℝ} (hx : G.LoadFeasible x d) (hd : 0 ≤ d)
    {y : V × V → ℝ} {Λ : Finset (List V)} {lam : List V → ℝ}
    (hy : G.DualFeasible y Λ lam) :
    ∑ e ∈ G.fusion, y e ≤ d := by
  obtain ⟨hx0, hxf, hxp⟩ := hx
  obtain ⟨hy0, hΛ, hl0, hl1, hload⟩ := hy
  calc ∑ e ∈ G.fusion, y e ≤ ∑ e ∈ G.fusion, y e * (x e.1 + x e.2) := by
        apply Finset.sum_le_sum; intro e he
        nlinarith [hy0 e, hxf e he]
    _ = ∑ v, x v * G.load y v := by
        simp only [load, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro e _
        simp only [mul_add, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib,
          Finset.sum_ite_eq, Finset.mem_univ, if_true]
        ring
    _ ≤ ∑ v, x v * marg Λ lam v := by
        apply Finset.sum_le_sum; intro v _
        exact mul_le_mul_of_nonneg_left (hload v) (hx0 v)
    _ = ∑ P ∈ Λ, lam P * weight x P := by
        simp only [marg, Finset.mul_sum, weight]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro P _
        simp only [mul_ite, mul_zero]
        rw [← Finset.sum_filter]
        have h1 : univ.filter (· ∈ P) = P.toFinset := by ext; simp
        rw [h1]
        apply Finset.sum_congr rfl; intro v _; ring
    _ ≤ ∑ P ∈ Λ, lam P * d := by
        apply Finset.sum_le_sum; intro P hP
        exact mul_le_mul_of_nonneg_left (hxp P (hΛ P hP)) (hl0 P)
    _ = (∑ P ∈ Λ, lam P) * d := by rw [Finset.sum_mul]
    _ ≤ 1 * d := mul_le_mul_of_nonneg_right hl1 hd
    _ = d := one_mul d

/-! ### Two-path concentration -/

/-- `e` crosses `(P, Q)`: one endpoint on `P` and the other on `Q`. -/
def Crosses (e : V × V) (P Q : List V) : Prop := (e.1 ∈ P ∧ e.2 ∈ Q) ∨ (e.2 ∈ P ∧ e.1 ∈ Q)

instance (e : V × V) (P Q : List V) : Decidable (Crosses e P Q) := by
  unfold Crosses; infer_instance

/-- Averaging: if a probability-weighted mean of `g` is at least `X`, some point attains `X`. -/
lemma exists_ge_of_mean {ι : Type*} {s : Finset ι} {w g : ι → ℝ} {X : ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = 1) (hX : X ≤ ∑ i ∈ s, w i * g i) :
    ∃ i ∈ s, X ≤ g i := by
  by_contra hcon
  push_neg at hcon
  have hpos : ∃ i ∈ s, 0 < w i := by
    by_contra h; push_neg at h
    have : ∑ i ∈ s, w i ≤ 0 := Finset.sum_nonpos h
    linarith
  have : 0 < ∑ i ∈ s, w i * (X - g i) := by
    apply Finset.sum_pos'
    · intro i hi; exact mul_nonneg (hw i hi) (by linarith [hcon i hi])
    · obtain ⟨i, hi, hwi⟩ := hpos
      exact ⟨i, hi, mul_pos hwi (by linarith [hcon i hi])⟩
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul] at this
  linarith

variable {y : V × V → ℝ} {Λ : Finset (List V)} {lam : List V → ℝ}

lemma le_marg (hy : ∀ e, 0 ≤ y e) (hload : ∀ v, G.load y v ≤ marg Λ lam v) {e : V × V}
    (he : e ∈ G.fusion) : y e ≤ marg Λ lam e.1 ∧ y e ≤ marg Λ lam e.2 := by
  have hterm : ∀ v, (v = e.1 ∨ v = e.2) → y e ≤ G.load y v := by
    intro v hv
    have hnn : ∀ e' ∈ G.fusion, 0 ≤ y e' * ((if e'.1 = v then 1 else 0) +
        (if e'.2 = v then 1 else 0)) := by
      intro e' _; apply mul_nonneg (hy e'); split_ifs <;> norm_num
    have := Finset.single_le_sum hnn he
    have h1 : (1 : ℝ) ≤ (if e.1 = v then 1 else 0) + (if e.2 = v then 1 else 0) := by
      rcases hv with rfl | rfl <;> simp <;> split_ifs <;> norm_num
    unfold load
    nlinarith [hy e]
  exact ⟨(hterm _ (Or.inl rfl)).trans (hload _), (hterm _ (Or.inr rfl)).trans (hload _)⟩

/-- The probability weight `λ_P λ_Q` of a pair of independently drawn paths. -/
def pw (lam : List V → ℝ) (pq : List V × List V) : ℝ := lam pq.1 * lam pq.2

lemma sum_pw (hsum : ∑ P ∈ Λ, lam P = 1) : ∑ pq ∈ Λ ×ˢ Λ, pw lam pq = 1 := by
  rw [Finset.sum_product]
  simp only [pw, ← Finset.mul_sum, ← Finset.sum_mul, hsum, one_mul]

lemma mean_indep (u w : V) :
    ∑ pq ∈ Λ ×ˢ Λ, pw lam pq * (if u ∈ pq.1 ∧ w ∈ pq.2 then 1 else 0) =
      marg Λ lam u * marg Λ lam w := by
  rw [Finset.sum_product, marg, marg, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl; intro P _
  apply Finset.sum_congr rfl; intro Q _
  simp only [pw]
  by_cases hu : u ∈ P <;> by_cases hw : w ∈ Q <;> simp [hu, hw]

lemma mean_crosses_ge (hlam : ∀ P, 0 ≤ lam P) (e : V × V) :
    marg Λ lam e.1 * marg Λ lam e.2 ≤
      ∑ pq ∈ Λ ×ˢ Λ, pw lam pq * (if Crosses e pq.1 pq.2 then 1 else 0) := by
  rw [← mean_indep]
  apply Finset.sum_le_sum; intro pq _
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hlam _) (hlam _))
  by_cases h1 : e.1 ∈ pq.1 ∧ e.2 ∈ pq.2
  · have h2 : Crosses e pq.1 pq.2 := Or.inl h1
    rw [if_pos h1, if_pos h2]
  · rw [if_neg h1]; by_cases h2 : Crosses e pq.1 pq.2
    · rw [if_pos h2]; norm_num
    · rw [if_neg h2]

lemma mean_crosses_eq (e : V × V) (hinc : ∀ P ∈ Λ, ¬ (e.1 ∈ P ∧ e.2 ∈ P)) :
    ∑ pq ∈ Λ ×ˢ Λ, pw lam pq * (if Crosses e pq.1 pq.2 then 1 else 0) =
      2 * (marg Λ lam e.1 * marg Λ lam e.2) := by
  have h := @mean_indep V _ _ Λ lam e.1 e.2
  have h' := @mean_indep V _ _ Λ lam e.2 e.1
  rw [two_mul]; nth_rewrite 2 [mul_comm]
  rw [← h, ← h', ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro pq hpq
  rw [Finset.mem_product] at hpq
  rw [← mul_add]; congr 1
  have hP := hinc pq.1 hpq.1
  unfold Crosses
  by_cases a1 : e.1 ∈ pq.1 <;> by_cases a2 : e.2 ∈ pq.2 <;> by_cases a3 : e.2 ∈ pq.1 <;>
    by_cases a4 : e.1 ∈ pq.2 <;> simp_all

/-- Expected crossing count, summed over a finite set of pairs. -/
lemma mean_sum (S : Finset (V × V)) (f : V × V → List V → List V → ℝ) :
    ∑ pq ∈ Λ ×ˢ Λ, pw lam pq * ∑ e ∈ S, f e pq.1 pq.2 =
      ∑ e ∈ S, ∑ pq ∈ Λ ×ˢ Λ, pw lam pq * f e pq.1 pq.2 := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]

lemma card_filter_crosses (S : Finset (V × V)) (P Q : List V) :
    ((S.filter (fun e => Crosses e P Q)).card : ℝ) =
      ∑ e ∈ S, (if Crosses e P Q then (1 : ℝ) else 0) := by
  rw [Finset.sum_boole]

lemma mean_weight (e : V × V) :
    ∑ pq ∈ Λ ×ˢ Λ, pw lam pq * (if Crosses e pq.1 pq.2 then y e else 0) =
      y e * ∑ pq ∈ Λ ×ˢ Λ, pw lam pq * (if Crosses e pq.1 pq.2 then 1 else 0) := by
  rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro pq _
  split_ifs <;> ring

/-- **Theorem 4.2 (two-path concentration).** Let `(y, λ)` be dual feasible with
`∑_P λ_P = 1`, `D = ∑_e y_e` and `s = |supp y|`. Then some two paths `P₀, Q₀` of the support
of `λ` are crossed by at least `D²/s` pairs of `supp y`, and some two paths `P₁, Q₁` carry crossing
dual weight at least `D³/s²`. -/
theorem concentration (hy : ∀ e, 0 ≤ y e) (hlam : ∀ P, 0 ≤ lam P)
    (hsum : ∑ P ∈ Λ, lam P = 1) (hload : ∀ v, G.load y v ≤ marg Λ lam v) :
    (∃ P ∈ Λ, ∃ Q ∈ Λ, (∑ e ∈ G.fusion, y e) ^ 2 / (G.fusion.filter (y · ≠ 0)).card ≤
      (((G.fusion.filter (y · ≠ 0)).filter (fun e => Crosses e P Q)).card : ℝ)) ∧
    (∃ P ∈ Λ, ∃ Q ∈ Λ, (∑ e ∈ G.fusion, y e) ^ 3 / ((G.fusion.filter (y · ≠ 0)).card) ^ 2 ≤
      ∑ e ∈ G.fusion, if Crosses e P Q then y e else 0) := by
  set S := G.fusion.filter (y · ≠ 0)
  have hD : ∑ e ∈ G.fusion, y e = ∑ e ∈ S, y e := by
    rw [Finset.sum_filter_ne_zero]
  have hw : ∀ pq ∈ Λ ×ˢ Λ, 0 ≤ pw lam pq := fun pq _ => mul_nonneg (hlam _) (hlam _)
  constructor
  · -- crossing count
    have hmean : (∑ e ∈ G.fusion, y e) ^ 2 / S.card ≤
        ∑ pq ∈ Λ ×ˢ Λ, pw lam pq * ∑ e ∈ S, (if Crosses e pq.1 pq.2 then (1 : ℝ) else 0) := by
      calc (∑ e ∈ G.fusion, y e) ^ 2 / S.card = (∑ e ∈ S, y e) ^ 2 / S.card := by rw [hD]
        _ ≤ ∑ e ∈ S, y e ^ 2 := by simpa using pow_sum_div_card_le_sum_pow (s := S) (fun e _ => hy e) 1
        _ ≤ ∑ e ∈ S, ∑ pq ∈ Λ ×ˢ Λ, pw lam pq * (if Crosses e pq.1 pq.2 then (1 : ℝ) else 0) := by
          apply Finset.sum_le_sum; intro e he
          have he' := (Finset.mem_filter.mp he).1
          obtain ⟨h1, h2⟩ := le_marg hy hload he'
          have := mean_crosses_ge (Λ := Λ) hlam e
          nlinarith [hy e]
        _ = _ := (mean_sum S (fun e P Q => if Crosses e P Q then (1 : ℝ) else 0)).symm
    obtain ⟨pq, hpq, hge⟩ := exists_ge_of_mean hw (sum_pw hsum) hmean
    rw [Finset.mem_product] at hpq
    exact ⟨pq.1, hpq.1, pq.2, hpq.2, by rw [card_filter_crosses]; exact hge⟩
  · -- crossing weight
    have hmean : (∑ e ∈ G.fusion, y e) ^ 3 / (S.card) ^ 2 ≤
        ∑ pq ∈ Λ ×ˢ Λ, pw lam pq * ∑ e ∈ G.fusion,
          (if Crosses e pq.1 pq.2 then y e else 0) := by
      calc (∑ e ∈ G.fusion, y e) ^ 3 / (S.card) ^ 2 = (∑ e ∈ S, y e) ^ 3 / (S.card) ^ 2 := by
            rw [hD]
        _ ≤ ∑ e ∈ S, y e ^ 3 := by simpa using pow_sum_div_card_le_sum_pow (s := S) (fun e _ => hy e) 2
        _ = ∑ e ∈ G.fusion, y e ^ 3 := by
            rw [Finset.sum_filter_of_ne]; intro e _ h; intro h0; apply h; rw [h0]; ring
        _ ≤ ∑ e ∈ G.fusion, ∑ pq ∈ Λ ×ˢ Λ, pw lam pq *
              (if Crosses e pq.1 pq.2 then y e else 0) := by
          apply Finset.sum_le_sum; intro e he
          obtain ⟨h1, h2⟩ := le_marg hy hload he
          have := mean_crosses_ge (Λ := Λ) hlam e
          rw [mean_weight]
          have hm : y e ^ 2 ≤ marg Λ lam e.1 * marg Λ lam e.2 := by nlinarith [hy e]
          nlinarith [hy e]
        _ = _ := (mean_sum G.fusion (fun e P Q => if Crosses e P Q then y e else 0)).symm
    obtain ⟨pq, hpq, hge⟩ := exists_ge_of_mean hw (sum_pw hsum) hmean
    rw [Finset.mem_product] at hpq
    exact ⟨pq.1, hpq.1, pq.2, hpq.2, hge⟩

/-- **Theorem 4.2, incomparable case.** If no path of the support of `λ` contains both vertices
of a pair of `supp y` (as when the two parents of every fusion are incomparable), both bounds hold
with an extra factor `2`. -/
theorem concentration_incomparable (hy : ∀ e, 0 ≤ y e) (hlam : ∀ P, 0 ≤ lam P)
    (hsum : ∑ P ∈ Λ, lam P = 1) (hload : ∀ v, G.load y v ≤ marg Λ lam v)
    (hinc : ∀ e ∈ G.fusion, y e ≠ 0 → ∀ P ∈ Λ, ¬ (e.1 ∈ P ∧ e.2 ∈ P)) :
    (∃ P ∈ Λ, ∃ Q ∈ Λ, 2 * ((∑ e ∈ G.fusion, y e) ^ 2 / (G.fusion.filter (y · ≠ 0)).card) ≤
      (((G.fusion.filter (y · ≠ 0)).filter (fun e => Crosses e P Q)).card : ℝ)) ∧
    (∃ P ∈ Λ, ∃ Q ∈ Λ,
      2 * ((∑ e ∈ G.fusion, y e) ^ 3 / ((G.fusion.filter (y · ≠ 0)).card) ^ 2) ≤
      ∑ e ∈ G.fusion, if Crosses e P Q then y e else 0) := by
  set S := G.fusion.filter (y · ≠ 0)
  have hD : ∑ e ∈ G.fusion, y e = ∑ e ∈ S, y e := by
    rw [Finset.sum_filter_ne_zero]
  have hw : ∀ pq ∈ Λ ×ˢ Λ, 0 ≤ pw lam pq := fun pq _ => mul_nonneg (hlam _) (hlam _)
  constructor
  · have hmean : 2 * ((∑ e ∈ G.fusion, y e) ^ 2 / S.card) ≤
        ∑ pq ∈ Λ ×ˢ Λ, pw lam pq * ∑ e ∈ S, (if Crosses e pq.1 pq.2 then (1 : ℝ) else 0) := by
      calc 2 * ((∑ e ∈ G.fusion, y e) ^ 2 / S.card) ≤ 2 * ∑ e ∈ S, y e ^ 2 := by
            have : (∑ e ∈ S, y e) ^ 2 / S.card ≤ ∑ e ∈ S, y e ^ 2 := by
              simpa using pow_sum_div_card_le_sum_pow (s := S) (fun e _ => hy e) 1
            rw [hD]; linarith
        _ = ∑ e ∈ S, 2 * y e ^ 2 := by rw [Finset.mul_sum]
        _ ≤ ∑ e ∈ S, ∑ pq ∈ Λ ×ˢ Λ, pw lam pq * (if Crosses e pq.1 pq.2 then (1 : ℝ) else 0) := by
          apply Finset.sum_le_sum; intro e he
          have he' := Finset.mem_filter.mp he
          obtain ⟨h1, h2⟩ := le_marg hy hload he'.1
          rw [mean_crosses_eq e (hinc e he'.1 he'.2)]
          nlinarith [hy e]
        _ = _ := (mean_sum S (fun e P Q => if Crosses e P Q then (1 : ℝ) else 0)).symm
    obtain ⟨pq, hpq, hge⟩ := exists_ge_of_mean hw (sum_pw hsum) hmean
    rw [Finset.mem_product] at hpq
    exact ⟨pq.1, hpq.1, pq.2, hpq.2, by rw [card_filter_crosses]; exact hge⟩
  · have hmean : 2 * ((∑ e ∈ G.fusion, y e) ^ 3 / (S.card) ^ 2) ≤
        ∑ pq ∈ Λ ×ˢ Λ, pw lam pq * ∑ e ∈ G.fusion,
          (if Crosses e pq.1 pq.2 then y e else 0) := by
      calc 2 * ((∑ e ∈ G.fusion, y e) ^ 3 / (S.card) ^ 2) ≤ 2 * ∑ e ∈ S, y e ^ 3 := by
            have : (∑ e ∈ S, y e) ^ 3 / (S.card) ^ 2 ≤ ∑ e ∈ S, y e ^ 3 := by
              simpa using pow_sum_div_card_le_sum_pow (s := S) (fun e _ => hy e) 2
            rw [hD]; linarith
        _ = ∑ e ∈ S, 2 * y e ^ 3 := by rw [Finset.mul_sum]
        _ ≤ ∑ e ∈ G.fusion, ∑ pq ∈ Λ ×ˢ Λ, pw lam pq *
              (if Crosses e pq.1 pq.2 then y e else 0) := by
          rw [Finset.sum_filter]
          apply Finset.sum_le_sum; intro e he
          split_ifs with h0
          · obtain ⟨h1, h2⟩ := le_marg hy hload he
            rw [mean_weight, mean_crosses_eq e (hinc e he h0)]
            have hm : y e ^ 2 ≤ marg Λ lam e.1 * marg Λ lam e.2 := by nlinarith [hy e]
            nlinarith [hy e]
          · apply Finset.sum_nonneg; intro pq hpq
            apply mul_nonneg (hw pq hpq); split_ifs <;> simp [hy e]
        _ = _ := (mean_sum G.fusion (fun e P Q => if Crosses e P Q then y e else 0)).symm
    obtain ⟨pq, hpq, hge⟩ := exists_ge_of_mean hw (sum_pw hsum) hmean
    rw [Finset.mem_product] at hpq
    exact ⟨pq.1, hpq.1, pq.2, hpq.2, hge⟩

end CarrierGraph

/-! ### Example 4.3: the factor two is needed -/

/-- A single arc `u → w` (`u = 0`, `w = 1`) with fusion pair `{u, w}`. -/
def arcGraph : CarrierGraph (Fin 2) where
  arc u v := u = 0 ∧ v = 1
  fusion := {(0, 1)}

/-- **Example 4.3.** For a single arc `u → w` with `E_f = {{u, w}}`, the pair `y = 1`,
`λ = δ_{u → w}` is dual feasible with `D = s = 1`, but no two paths are crossed by more than one
pair, so the bound `2 D²/s = 2` of the incomparable case fails. -/
theorem factorTwo_example :
    arcGraph.DualFeasible (fun _ => 1) {[0, 1]} (fun _ => 1) ∧
    ∀ P Q : List (Fin 2),
      (((arcGraph.fusion.filter (fun _ => (1 : ℝ) ≠ 0)).filter
        (fun e => CarrierGraph.Crosses e P Q)).card : ℝ) <
      2 * ((∑ e ∈ arcGraph.fusion, (1 : ℝ)) ^ 2 /
        (arcGraph.fusion.filter (fun _ => (1 : ℝ) ≠ 0)).card) := by
  constructor
  · refine ⟨fun _ => zero_le_one, ?_, fun _ => zero_le_one, by simp, ?_⟩
    · intro P hP; simp at hP; subst hP
      exact ⟨by simp, by simp [arcGraph]⟩
    · intro v; fin_cases v <;> simp [CarrierGraph.load, CarrierGraph.marg, arcGraph] <;>
        exact ⟨[0, 1], by simp⟩
  · intro P Q
    have hc : ((arcGraph.fusion.filter (fun _ => (1 : ℝ) ≠ 0)).filter
        (fun e => CarrierGraph.Crosses e P Q)).card ≤ 1 :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans
        ((Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp [arcGraph]))
    have hr : 2 * ((∑ e ∈ arcGraph.fusion, (1 : ℝ)) ^ 2 /
        (arcGraph.fusion.filter (fun _ => (1 : ℝ) ≠ 0)).card) = 2 := by
      simp [arcGraph]
    rw [hr]
    have : (((arcGraph.fusion.filter (fun _ => (1 : ℝ) ≠ 0)).filter
        (fun e => CarrierGraph.Crosses e P Q)).card : ℝ) ≤ 1 := by exact_mod_cast hc
    linarith

/-! ### The matched-rail mirage and the complete readout grid -/

/-- Two unary rails `A_0 → ⋯ → A_{h-1}` and `B_0 → ⋯ → B_{h-1}` (`Sum.inl i = A_i`,
`Sum.inr (Sum.inl j) = B_j`) and readout fusions `Z_r = ψ_r(A_{ra r}, B_{rb r})`
(`Sum.inr (Sum.inr r) = Z_r`) that feed nothing. -/
def railGraph (h : ℕ) {ρ : Type*} [DecidableEq ρ] (ra rb : ρ → Fin h) [Fintype ρ] :
    CarrierGraph (Fin h ⊕ Fin h ⊕ ρ) where
  arc u v := match u, v with
    | .inl i, .inl j => j.val = i.val + 1
    | .inr (.inl i), .inr (.inl j) => j.val = i.val + 1
    | .inl i, .inr (.inr r) => ra r = i
    | .inr (.inl i), .inr (.inr r) => rb r = i
    | _, _ => False
  fusion := univ.image (fun r => (Sum.inl (ra r), Sum.inr (Sum.inl (rb r))))

section Rails

variable {h : ℕ} {ρ : Type*} [Fintype ρ] [DecidableEq ρ] {ra rb : ρ → Fin h}

/-- Not on the `B` rail. -/
def notB : Fin h ⊕ Fin h ⊕ ρ → Bool
  | .inr (.inl _) => false
  | _ => true

/-- Not on the `A` rail. -/
def notA : Fin h ⊕ Fin h ⊕ ρ → Bool
  | .inl _ => false
  | _ => true

lemma chain_notB : ∀ (l : List (Fin h ⊕ Fin h ⊕ ρ)) (a : Fin h ⊕ Fin h ⊕ ρ),
    (a :: l).IsChain (railGraph h ra rb).arc → notB a = true → ∀ v ∈ a :: l, notB v = true
  | [], a, _, ha, v, hv => by simp at hv; rw [hv]; exact ha
  | b :: l, a, hch, ha, v, hv => by
    rw [List.isChain_cons_cons] at hch
    have hb : notB b = true := by
      obtain ⟨hab, _⟩ := hch
      rcases a with i | i | r <;> rcases b with j | j | r' <;> simp_all [notB, railGraph]
    rcases List.mem_cons.mp hv with rfl | hv
    · exact ha
    · exact chain_notB l b hch.2 hb v hv

lemma chain_notA : ∀ (l : List (Fin h ⊕ Fin h ⊕ ρ)) (a : Fin h ⊕ Fin h ⊕ ρ),
    (a :: l).IsChain (railGraph h ra rb).arc → notA a = true → ∀ v ∈ a :: l, notA v = true
  | [], a, _, ha, v, hv => by simp at hv; rw [hv]; exact ha
  | b :: l, a, hch, ha, v, hv => by
    rw [List.isChain_cons_cons] at hch
    have hb : notA b = true := by
      obtain ⟨hab, _⟩ := hch
      rcases a with i | i | r <;> rcases b with j | j | r' <;> simp_all [notA, railGraph]
    rcases List.mem_cons.mp hv with rfl | hv
    · exact ha
    · exact chain_notA l b hch.2 hb v hv

/-- A directed path lies in one rail, possibly followed by one readout. -/
lemma rail_path (P : List (Fin h ⊕ Fin h ⊕ ρ)) (hP : (railGraph h ra rb).IsPath P) :
    (∀ v ∈ P, notB v = true) ∨ (∀ v ∈ P, notA v = true) := by
  obtain ⟨hne, hch⟩ := hP
  rcases P with _ | ⟨a, l⟩
  · exact absurd rfl hne
  rcases a with i | i | r
  · exact Or.inl (chain_notB l _ hch rfl)
  · exact Or.inr (chain_notA l _ hch rfl)
  · -- a readout has no outgoing arc
    rcases l with _ | ⟨b, l⟩
    · left; intro v hv; simp at hv; subst hv; rfl
    · rw [List.isChain_cons_cons] at hch
      rcases b with j | j | r' <;> simp [railGraph] at hch

lemma weight_ofFn {n : ℕ} (x : Fin h ⊕ Fin h ⊕ ρ → ℝ) (f : Fin n → Fin h ⊕ Fin h ⊕ ρ)
    (hf : Function.Injective f) : CarrierGraph.weight x (List.ofFn f) = ∑ i, x (f i) := by
  unfold CarrierGraph.weight
  have : (List.ofFn f).toFinset = univ.image f := by ext; simp [List.mem_ofFn]
  rw [this, Finset.sum_image (fun a _ b _ hab => hf hab)]

lemma railA_path (hh : 1 ≤ h) :
    (railGraph h ra rb).IsPath (List.ofFn (fun i : Fin h => (Sum.inl i : Fin h ⊕ Fin h ⊕ ρ))) := by
  refine ⟨by simp; omega, ?_⟩
  rw [List.isChain_ofFn]; intro i hi; simp [railGraph]

lemma railB_path (hh : 1 ≤ h) :
    (railGraph h ra rb).IsPath
      (List.ofFn (fun i : Fin h => (Sum.inr (Sum.inl i) : Fin h ⊕ Fin h ⊕ ρ))) := by
  refine ⟨by simp; omega, ?_⟩
  rw [List.isChain_ofFn]; intro i hi; simp [railGraph]

/-- **Theorem 5.1 and Proposition 5.2 (`δ = h/2`).** For two unary rails of length `h ≥ 1` and
any family of readouts `Z_r = ψ_r(A_{ra r}, B_{rb r})` that contains a perfect matching
`{A_i, B_{π i}}` (the matched-rail mirage for one permutation `π`, or the complete readout grid),
weight `1/2` on every rail vertex is a feasible fractional load of value `h/2`, and every feasible
fractional load has value at least `h/2`. -/
theorem railGraph_load (hh : 1 ≤ h) (π : Equiv.Perm (Fin h))
    (hπ : ∀ i, ∃ r, ra r = i ∧ rb r = π i) :
    (railGraph h ra rb).LoadFeasible (fun v => match v with
      | .inr (.inr _) => 0
      | _ => 1 / 2) (h / 2) ∧
    ∀ x d, (railGraph h ra rb).LoadFeasible x d → (h : ℝ) / 2 ≤ d := by
  constructor
  · refine ⟨fun v => by rcases v with i | i | r <;> norm_num, ?_, ?_⟩
    · intro e he
      simp [railGraph] at he
      obtain ⟨r, rfl⟩ := he
      norm_num
    · intro P hP
      set x : Fin h ⊕ Fin h ⊕ ρ → ℝ := fun v => match v with
        | .inr (.inr _) => 0
        | _ => 1 / 2
      have hx0 : ∀ v, 0 ≤ x v := fun v => by rcases v with i | i | r <;> norm_num [x]
      rcases rail_path P hP with hB | hA
      · calc CarrierGraph.weight x P
            = ∑ v ∈ P.toFinset, (if notB v = true then x v else 0) := by
              apply Finset.sum_congr rfl; intro v hv
              rw [List.mem_toFinset] at hv; simp [hB v hv]
          _ ≤ ∑ v, (if notB v = true then x v else 0) := by
              apply Finset.sum_le_univ_sum_of_nonneg
              intro v; split_ifs <;> simp [hx0 v]
          _ = h / 2 := by
              simp [Fintype.sum_sum_type, notB, x]; ring
      · calc CarrierGraph.weight x P
            = ∑ v ∈ P.toFinset, (if notA v = true then x v else 0) := by
              apply Finset.sum_congr rfl; intro v hv
              rw [List.mem_toFinset] at hv; simp [hA v hv]
          _ ≤ ∑ v, (if notA v = true then x v else 0) := by
              apply Finset.sum_le_univ_sum_of_nonneg
              intro v; split_ifs <;> simp [hx0 v]
          _ = h / 2 := by
              simp [Fintype.sum_sum_type, notA, x]; ring
  · rintro x d ⟨hx0, hxf, hxp⟩
    have hA := hxp _ (railA_path (ra := ra) (rb := rb) hh)
    have hB := hxp _ (railB_path (ra := ra) (rb := rb) hh)
    rw [weight_ofFn x _ (fun a b hab => Sum.inl_injective hab)] at hA
    rw [weight_ofFn x _ (fun a b hab => Sum.inl_injective (Sum.inr_injective hab))] at hB
    have hpair : ∀ i, 1 ≤ x (Sum.inl i) + x (Sum.inr (Sum.inl (π i))) := by
      intro i
      obtain ⟨r, hr1, hr2⟩ := hπ i
      have := hxf _ (Finset.mem_image.mpr ⟨r, mem_univ r, rfl⟩)
      simpa [hr1, hr2] using this
    have hsum : (h : ℝ) ≤ ∑ i, x (Sum.inl i) + ∑ i, x (Sum.inr (Sum.inl i)) := by
      rw [← Equiv.sum_comp π (fun i => x (Sum.inr (Sum.inl i))), ← Finset.sum_add_distrib]
      calc (h : ℝ) = ∑ _i : Fin h, (1 : ℝ) := by simp
        _ ≤ _ := Finset.sum_le_sum (fun i _ => hpair i)
    linarith

/-- The matched-rail mirage for a permutation `π`: readouts `Z_i = ψ_i(A_i, B_{π i})`. -/
abbrev mirage (h : ℕ) (π : Equiv.Perm (Fin h)) :
    CarrierGraph (Fin h ⊕ Fin h ⊕ Fin h) := railGraph h id π

lemma coverCount_ofFn {n : ℕ} (H : Finset (Fin h ⊕ Fin h ⊕ ρ)) (f : Fin n → Fin h ⊕ Fin h ⊕ ρ)
    (hf : Function.Injective f) :
    CarrierGraph.coverCount H (List.ofFn f) = ∑ i, if f i ∈ H then 1 else 0 := by
  unfold CarrierGraph.coverCount
  have : (List.ofFn f).toFinset = univ.image f := by ext; simp [List.mem_ofFn]
  rw [this, Finset.card_filter, Finset.sum_image (fun a _ b _ hab => hf hab)]

/-- **Theorem 5.1 (integral catalyst height of the mirage).** Every catalyst cover of the
matched-rail mirage has a rail containing at least `h/2` of its nodes, and the cover
`{A_i : i < ⌈h/2⌉} ∪ {B_{π i} : i ≥ ⌈h/2⌉}` has height `⌈h/2⌉`. Hence `χ = ⌈h/2⌉`. -/
theorem mirage_height (hh : 1 ≤ h) (π : Equiv.Perm (Fin h)) :
    (∀ H, (mirage h π).IsCatalystCover H →
      ∃ P, (mirage h π).IsPath P ∧ h ≤ 2 * CarrierGraph.coverCount H P) ∧
    ∃ H, (mirage h π).IsCatalystCover H ∧ (mirage h π).HeightLE H ((h + 1) / 2) := by
  constructor
  · intro H hH
    have hcov : ∀ i, 1 ≤ (if (Sum.inl i : Fin h ⊕ Fin h ⊕ Fin h) ∈ H then 1 else 0) +
        (if (Sum.inr (Sum.inl (π i)) : Fin h ⊕ Fin h ⊕ Fin h) ∈ H then 1 else 0) := by
      intro i
      rcases hH _ (Finset.mem_image.mpr ⟨i, mem_univ i, rfl⟩) with h1 | h1 <;>
        simp at h1 <;> simp [h1]
    have hsum : h ≤ (∑ i, if (Sum.inl i : Fin h ⊕ Fin h ⊕ Fin h) ∈ H then 1 else 0) +
        ∑ i, if (Sum.inr (Sum.inl i) : Fin h ⊕ Fin h ⊕ Fin h) ∈ H then 1 else 0 := by
      rw [← Equiv.sum_comp π (fun i =>
        if (Sum.inr (Sum.inl i) : Fin h ⊕ Fin h ⊕ Fin h) ∈ H then 1 else 0),
        ← Finset.sum_add_distrib]
      calc h = ∑ _i : Fin h, 1 := by simp
        _ ≤ _ := Finset.sum_le_sum (fun i _ => hcov i)
    rw [← coverCount_ofFn H _ (fun a b hab => Sum.inl_injective hab),
      ← coverCount_ofFn H _ (fun a b hab => Sum.inl_injective (Sum.inr_injective hab))] at hsum
    by_cases hc : CarrierGraph.coverCount H (List.ofFn (fun i : Fin h =>
        (Sum.inl i : Fin h ⊕ Fin h ⊕ Fin h))) ≥ CarrierGraph.coverCount H (List.ofFn
        (fun i : Fin h => (Sum.inr (Sum.inl i) : Fin h ⊕ Fin h ⊕ Fin h)))
    · exact ⟨_, railA_path hh, by omega⟩
    · exact ⟨_, railB_path hh, by omega⟩
  · set k := (h + 1) / 2
    let H : Finset (Fin h ⊕ Fin h ⊕ Fin h) :=
      (univ.filter (fun i : Fin h => i.val < k)).image Sum.inl ∪
        (univ.filter (fun i : Fin h => k ≤ i.val)).image (fun i => Sum.inr (Sum.inl (π i)))
    refine ⟨H, ?_, ?_⟩
    · intro e he
      simp only [railGraph, Finset.mem_image, mem_univ, true_and] at he
      obtain ⟨i, rfl⟩ := he
      by_cases hi : i.val < k
      · left; simp [H, hi]
      · right; simp [H]; omega
    · intro P hP
      unfold CarrierGraph.coverCount
      rcases rail_path P hP with hB | hA
      · calc (P.toFinset.filter (· ∈ H)).card
            ≤ ((univ.filter (fun i : Fin h => i.val < k)).image
                (Sum.inl : Fin h → Fin h ⊕ Fin h ⊕ Fin h)).card := by
              apply Finset.card_le_card
              intro v hv
              rw [Finset.mem_filter, List.mem_toFinset] at hv
              have hnb := hB v hv.1
              have := hv.2
              simp only [H, Finset.mem_union] at this
              rcases this with h1 | h1
              · exact h1
              · simp at h1; obtain ⟨i, _, rfl⟩ := h1; simp [notB] at hnb
          _ ≤ (univ.filter (fun i : Fin h => i.val < k)).card := Finset.card_image_le
          _ ≤ (Finset.range k).card := by
              apply Finset.card_le_card_of_injOn Fin.val
              · intro i hi; simp at hi ⊢; exact hi
              · intro a _ b _ hab; exact Fin.ext hab
          _ = k := Finset.card_range k
      · calc (P.toFinset.filter (· ∈ H)).card
            ≤ ((univ.filter (fun i : Fin h => k ≤ i.val)).image
                (fun i => (Sum.inr (Sum.inl (π i)) : Fin h ⊕ Fin h ⊕ Fin h))).card := by
              apply Finset.card_le_card
              intro v hv
              rw [Finset.mem_filter, List.mem_toFinset] at hv
              have hna := hA v hv.1
              have := hv.2
              simp only [H, Finset.mem_union] at this
              rcases this with h1 | h1
              · simp at h1; obtain ⟨i, _, rfl⟩ := h1; simp [notA] at hna
              · exact h1
          _ ≤ (univ.filter (fun i : Fin h => k ≤ i.val)).card := Finset.card_image_le
          _ ≤ (Finset.Ico k h).card := by
              apply Finset.card_le_card_of_injOn Fin.val
              · intro i hi; simp at hi ⊢; omega
              · intro a _ b _ hab; exact Fin.ext hab
          _ = h - k := Nat.card_Ico k h
          _ ≤ k := by omega

end Rails

end GC.FlowCircuits
