import GC.Optimization.FlowCircuits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fintype.Option

/-!
# Manuscript 003c: What flow reductions need for RNC speedups

The main results of this manuscript are conditional statements about parallel complexity
(PRAM depth, RNC, the solver hypotheses 3.1 and 3.2); they are not formalized. Formalized are the
exact mathematical facts the ledger rests on:

* `sum_netOut_eq_zero`, `gadget_conservation` : Proposition 7.1 (conservation is
  cost-independent: in a gadget with no internal supplies, external outflow equals external
  inflow, for every feasible flow; costs do not enter).
* `lasVegas_expected_trials` : the expectation in Corollary 6.2 (repeating a trial that succeeds
  with probability `p` until success takes `1/p` trials in expectation), together with
  `lasVegas_total_probability`.
* `ledger_exponent`, `calibration` : the parameter arithmetic of Theorem 4.1, Corollary 4.2 and
  Proposition 4.4.
-/

namespace GC.FlowCircuits

open Finset

/-- Summing the net outflows over all vertices gives zero: every arc is counted once with `+` at
its tail and once with `-` at its head. -/
theorem sum_netOut_eq_zero {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V]
    (tail head : A → V) (f : A → ℤ) : ∑ v, netOut tail head f v = 0 := by
  unfold netOut inc
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro a _
  rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  simp

/-- **Proposition 7.1 (conservation is cost-independent).** Let a gadget on vertices `W` be
embedded in a network whose only other vertex is the outside `none`, with no internal supplies:
conservation holds at every vertex of the gadget. Then the total flow on arcs leaving the gadget
equals the total flow on arcs entering it. The statement involves no costs, so it holds for every
choice of costs, random ones included. -/
theorem gadget_conservation {W A : Type*} [Fintype W] [Fintype A] [DecidableEq W]
    (tail head : A → Option W) (f : A → ℤ)
    (hcons : ∀ w : W, netOut tail head f (some w) = 0) :
    ∑ a ∈ univ.filter (fun a => head a = none ∧ tail a ≠ none), f a =
      ∑ a ∈ univ.filter (fun a => tail a = none ∧ head a ≠ none), f a := by
  have h0 : netOut tail head f none = 0 := by
    have := sum_netOut_eq_zero tail head f
    rw [Fintype.sum_option] at this
    rw [Finset.sum_eq_zero (fun w _ => hcons w), add_zero] at this
    exact this
  unfold netOut inc at h0
  rw [Finset.sum_filter, Finset.sum_filter]
  have : ∀ a, f a * ((if tail a = none then 1 else 0) - (if head a = none then 1 else 0)) =
      (if tail a = none ∧ head a ≠ none then f a else 0) -
        (if head a = none ∧ tail a ≠ none then f a else 0) := by
    intro a
    by_cases h1 : tail a = none <;> by_cases h2 : head a = none <;> simp [h1, h2]
  simp_rw [this, Finset.sum_sub_distrib] at h0
  linarith

/-- **Corollary 6.2, expected number of trials.** If each independent trial succeeds with
probability `p ∈ (0, 1]`, the number of trials until the first success has expectation
`∑_{k ≥ 1} k p (1 - p)^{k - 1} = 1 / p`. -/
theorem lasVegas_expected_trials {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    HasSum (fun n : ℕ => ((n : ℝ) + 1) * (p * (1 - p) ^ n)) (1 / p) := by
  have hq : ‖1 - p‖ < 1 := by
    rw [Real.norm_eq_abs, abs_lt]; constructor <;> linarith
  have hq' : 0 ≤ 1 - p := by linarith
  have h1 := hasSum_coe_mul_geometric_of_norm_lt_one hq
  have h2 := hasSum_geometric_of_lt_one hq' (by linarith : 1 - p < 1)
  have h := (h1.add h2).mul_left p
  convert h using 1
  · funext n; ring
  · have : (1 : ℝ) - (1 - p) = p := by ring
    rw [this]; field_simp; ring

/-- The trial count is a probability distribution: `∑_{k ≥ 1} p (1 - p)^{k - 1} = 1`. -/
theorem lasVegas_total_probability {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    HasSum (fun n : ℕ => p * (1 - p) ^ n) 1 := by
  have h2 := (hasSum_geometric_of_lt_one (by linarith : (0 : ℝ) ≤ 1 - p)
    (by linarith : 1 - p < 1)).mul_left p
  convert h2 using 1
  have : (1 : ℝ) - (1 - p) = p := by ring
  rw [this, mul_inv_cancel₀ hp0.ne']

/-- **Theorem 4.1 and Corollary 4.2, exponent arithmetic.** For `N = S^α` and `L = S^λ`,
`√N · L = S^{α/2 + λ}`; for `α = 1`, `λ = 1/2 - ε` the exponent is `1 - ε`, and for
`α = 2 - δ`, `λ = δ/2 - ε` it is `1 - ε`. -/
theorem ledger_exponent {S : ℝ} (hS : 0 < S) (α lam : ℝ) :
    Real.sqrt (S ^ α) * S ^ lam = S ^ (α / 2 + lam) ∧
    (1 : ℝ) / 2 + (1 / 2 - lam) = 1 - lam ∧
    ∀ δ ε : ℝ, (2 - δ) / 2 + (δ / 2 - ε) = 1 - ε := by
  refine ⟨?_, by ring, fun _ _ => by ring⟩
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hS.le, ← Real.rpow_add hS]
  ring_nf

/-- **Proposition 4.4 (calibration).** (i) If `N ≥ 1` and `L ≥ d ≥ 0` then `√N · L ≥ d`: a
priority hierarchy whose bit length tracks the depth gains nothing. (ii) For the
Goldschlager–Shaw–Staples parameters `N = L = S ≥ 1`, `√N · L = S^{3/2} ≥ S ≥ d` whenever
`d ≤ S`. (iii) If `N ≥ S > 0` and `√N · L ≤ d · S^{-ε}`, then `L ≤ d · S^{-1/2-ε}`. -/
theorem calibration :
    (∀ N L d : ℝ, 1 ≤ N → 0 ≤ d → d ≤ L → d ≤ Real.sqrt N * L) ∧
    (∀ S d : ℝ, 1 ≤ S → d ≤ S → Real.sqrt S * S = S ^ ((3 : ℝ) / 2) ∧ d ≤ Real.sqrt S * S) ∧
    (∀ N S L d ε : ℝ, 0 < S → S ≤ N → 0 ≤ L →
      Real.sqrt N * L ≤ d * S ^ (-ε) → L ≤ d * S ^ (-(1 / 2) - ε)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro N L d hN hd hdL
    have : 1 ≤ Real.sqrt N := by rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hN
    nlinarith
  · intro S d hS hd
    have hS0 : 0 < S := by linarith
    constructor
    · rw [Real.sqrt_eq_rpow, show ((3 : ℝ) / 2) = 1 / 2 + 1 by norm_num, Real.rpow_add hS0,
        Real.rpow_one]
    · have : 1 ≤ Real.sqrt S := by
        rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hS
      nlinarith
  · intro N S L d ε hS hSN hL h
    have hsq : Real.sqrt S ≤ Real.sqrt N := Real.sqrt_le_sqrt hSN
    have hpos : 0 < Real.sqrt S := Real.sqrt_pos.mpr hS
    have h1 : Real.sqrt S * L ≤ d * S ^ (-ε) := le_trans (by nlinarith) h
    have e : S ^ (-(1 / 2) - ε) = S ^ (-ε) / Real.sqrt S := by
      rw [Real.sqrt_eq_rpow, sub_eq_add_neg, Real.rpow_add hS, Real.rpow_neg hS.le]
      ring
    rw [e, mul_div_assoc', le_div_iff₀ hpos]
    linarith

end GC.FlowCircuits
