import GC.Computability.RandomSeqNOR.KleenePrefix
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Average-case AC¹ and SC² (manuscript 001c): deterministic results

* Lemma 3.2 is `kp_rounds_eq_depth` (file `KleenePrefix.lean`).
* Dependency chains and the deterministic first step of Theorem 3.4:
  `exists_depChain`, `kp_finishes_of_no_long_chain`.
* The thresholds: `epsK_threshold` (Theorem 3.4: `θ < 1` is achievable iff `ε > (√17-1)/4`),
  `fixed_point_density` (Lemma 3.5: the limit equation), `epsB_threshold` (Theorem 3.6),
  `varpi_threshold` (Theorem 3.9: `εϖ(ε) > 1 - ε` iff `ε > 3/4`).
-/

namespace GC.RandomSeqNOR

/-! ### Dependency chains -/

/-- A dependency step from `p` to `q`: some non-NOT gate `k` with `max(ϱ(p), 1) ≤ k ≤ p` and
`q = jₖ`. -/
def DepStep (P : Inst) (p q : ℕ) : Prop :=
  ∃ k, max (lastReset P p) 1 ≤ k ∧ k ≤ p ∧ ¬ IsNot P k ∧ P.j k = q

/-- `pos 0, pos 1, …, pos L` is a dependency chain of length `L`. -/
def IsDepChain (P : Inst) (L : ℕ) (pos : ℕ → ℕ) : Prop :=
  ∀ s < L, DepStep P (pos s) (pos (s + 1))

/-- Following a maximiser: if `d(p) ≥ 2`, some dependency step leads to a position of depth
`d(p) - 1`. -/
theorem exists_depStep (P : Inst) {p : ℕ} (hp : 2 ≤ depth P p) :
    ∃ q, DepStep P p q ∧ depth P q + 1 = depth P p := by
  have hle := (depth_le_succ_iff P p (depth P p - 1)).1 (by omega)
  by_contra hc
  push Not at hc
  have : depth P p ≤ (depth P p - 2) + 1 := by
    rw [depth_le_succ_iff]
    intro k hk1 hk2 hk3
    have h1 := hle k hk1 hk2 hk3
    have h2 := hc (P.j k) ⟨k, hk1, hk2, hk3, rfl⟩
    omega
  omega

/-- If `d(p) ≥ L + 1`, there is a dependency chain of length `L` from `p` with
`d(P_s) = d(p) - s`. -/
theorem exists_depChain (P : Inst) (p : ℕ) :
    ∀ L, L + 1 ≤ depth P p → ∃ pos : ℕ → ℕ, pos 0 = p ∧ IsDepChain P L pos ∧
      ∀ s ≤ L, depth P (pos s) = depth P p - s := by
  intro L
  induction L with
  | zero => intro _; exact ⟨fun _ => p, rfl, fun s hs => absurd hs (Nat.not_lt_zero _),
      fun s hs => by simp [show s = 0 by omega]⟩
  | succ L ih =>
    intro hL
    obtain ⟨pos, h0, hch, hd⟩ := ih (by omega)
    obtain ⟨q, hq1, hq2⟩ := exists_depStep P (p := pos L) (by rw [hd L le_rfl]; omega)
    refine ⟨fun s => if s ≤ L then pos s else q, by simp [h0], ?_, ?_⟩
    · intro s hs
      by_cases hsL : s + 1 ≤ L
      · simp only [show s ≤ L by omega, hsL, ↓reduceIte]; exact hch s (by omega)
      · simp only [show s ≤ L by omega, hsL, ↓reduceIte]
        rw [show s = L by omega]; exact hq1
    · intro s hs
      by_cases hsL : s ≤ L
      · simp only [hsL, ↓reduceIte]; exact hd s hsL
      · simp only [hsL, ↓reduceIte]
        have := hd L le_rfl
        rw [show s = L + 1 by omega]; omega

/-- **Theorem 3.4, deterministic first step.** Let `g₀ ≥ 1`. If no dependency chain of length `L`
has all its positions at least `g₀` (the event `Γ`), then `max_i d(i) < L + g₀`, and hence, by
Lemma 3.2, the Kleene–prefix iteration knows every position after `L + g₀ - 1` rounds. -/
theorem kp_finishes_of_no_long_chain (P : Inst) {L g₀ : ℕ} (hg₀ : 1 ≤ g₀)
    (hΓ : ¬ ∃ pos : ℕ → ℕ, IsDepChain P L pos ∧ ∀ s ≤ L, g₀ ≤ pos s) :
    (∀ i, depth P i < L + g₀) ∧ ∀ i, i ∈ (kpIter P (L + g₀ - 1)).known := by
  have h1 : ∀ i, depth P i < L + g₀ := by
    intro i
    by_contra hc
    push Not at hc
    obtain ⟨pos, -, hch, hd⟩ := exists_depChain P i L (by omega)
    exact hΓ ⟨pos, hch, fun s hs => by
      have := hd s hs
      have := depth_le_self P (pos s)
      omega⟩
  refine ⟨h1, fun i => ?_⟩
  rw [(kp_rounds_eq_depth P _).1]
  show depth P i ≤ L + g₀ - 1
  have := h1 i; omega

/-! ### The thresholds -/

/-- **Theorem 3.4, the threshold `ε_K`.** For `0 < ε ≤ 1`, there are `η ∈ (0, ε/(2+ε))` and
`λ > 0` with `θ = (ε/(λ+1) + 1 - ε)/(ε c) < 1`, `c = ε/(2+ε) - η`, if and only if
`ε > ε_K = (√17 - 1)/4`. -/
theorem epsK_threshold {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (∃ η lam : ℝ, 0 < η ∧ η < ε / (2 + ε) ∧ 0 < lam ∧
        (ε / (lam + 1) + 1 - ε) / (ε * (ε / (2 + ε) - η)) < 1) ↔
      (Real.sqrt 17 - 1) / 4 < ε := by
  have h2e : 0 < 2 + ε := by linarith
  have hs : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 17 := Real.sqrt_nonneg _
  -- `ε > ε_K` iff `ε²/(2+ε) > 1 - ε` iff `2ε² + ε - 2 > 0`
  have key : (Real.sqrt 17 - 1) / 4 < ε ↔ 0 < 2 * ε ^ 2 + ε - 2 := by
    constructor
    · intro h; nlinarith
    · intro h; by_contra hc; push Not at hc; nlinarith
  rw [key]
  constructor
  · rintro ⟨η, lam, hη0, hη1, hlam, hθ⟩
    have hc : 0 < ε / (2 + ε) - η := by linarith
    have hden : 0 < ε * (ε / (2 + ε) - η) := mul_pos hε0 hc
    rw [div_lt_one hden] at hθ
    have hl : 0 < ε / (lam + 1) := div_pos hε0 (by linarith)
    have : 1 - ε < ε * (ε / (2 + ε)) := by nlinarith
    rw [mul_div_assoc', lt_div_iff₀ h2e] at this
    nlinarith
  · intro h
    set g := ε * (ε / (2 + ε)) - (1 - ε) with hg
    have hgpos : 0 < g := by
      rw [hg, mul_div_assoc', sub_pos, lt_div_iff₀ h2e]; nlinarith
    have hgle : g ≤ ε * (ε / (2 + ε)) := by rw [hg]; linarith
    refine ⟨g / (4 * ε), 4 * ε / g, by positivity, ?_, by positivity, ?_⟩
    · rw [div_lt_iff₀ (by positivity)]
      have : ε * (ε / (2 + ε)) < ε / (2 + ε) * (4 * ε) := by
        have : 0 < ε / (2 + ε) := by positivity
        nlinarith
      linarith
    · have hc : ε * (ε / (2 + ε) - g / (4 * ε)) = ε * (ε / (2 + ε)) - g / 4 := by
        field_simp
      have hl : ε / (4 * ε / g + 1) < g / 2 := by
        rw [div_lt_iff₀ (by positivity)]
        field_simp
        nlinarith
      have hden : 0 < ε * (ε / (2 + ε) - g / (4 * ε)) := by rw [hc]; linarith
      rw [div_lt_one hden, hc]
      linarith

/-- **Lemma 3.5, the limit equation.** Let `0 ≤ ε ≤ 1`, `L(μ) = ε(1-μ)/(1+ε(1-μ))` and
`U(ℓ) = (1-εℓ)/(2-εℓ)`. If `ℓ = L(μ)`, `μ = U(ℓ)` and `0 ≤ ℓ ≤ 1`, then
`εℓ = (2 + ε - √(4 + 4ε - 3ε²))/2`. -/
theorem fixed_point_density {ε ℓ μ : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hℓ0 : 0 ≤ ℓ) (hℓ1 : ℓ ≤ 1)
    (hL : ℓ = ε * (1 - μ) / (1 + ε * (1 - μ))) (hU : μ = (1 - ε * ℓ) / (2 - ε * ℓ)) :
    ε * ℓ = (2 + ε - Real.sqrt (4 + 4 * ε - 3 * ε ^ 2)) / 2 := by
  set w := ε * ℓ with hw
  have hw1 : w ≤ 1 := by rw [hw]; nlinarith
  have hw0 : 0 ≤ w := by rw [hw]; positivity
  have h2w : 0 < 2 - w := by linarith
  have h1μ : 1 - μ = 1 / (2 - w) := by rw [hU]; field_simp; ring
  have hden : 0 < 1 + ε * (1 - μ) := by rw [h1μ]; positivity
  have hℓ : ℓ = ε / (2 - w + ε) := by
    rw [hL, h1μ]; field_simp
  -- `w² - (2+ε)w + ε² = 0`
  have hq : w ^ 2 - (2 + ε) * w + ε ^ 2 = 0 := by
    have : w = ε * (ε / (2 - w + ε)) := by rw [hw, ← hℓ]
    have h3 : 0 < 2 - w + ε := by linarith
    field_simp at this
    nlinarith
  have hD : 0 ≤ 4 + 4 * ε - 3 * ε ^ 2 := by nlinarith
  have hs := Real.sq_sqrt hD
  have hs0 := Real.sqrt_nonneg (4 + 4 * ε - 3 * ε ^ 2)
  have hfac : (w - (2 + ε - Real.sqrt (4 + 4 * ε - 3 * ε ^ 2)) / 2) *
      (w - (2 + ε + Real.sqrt (4 + 4 * ε - 3 * ε ^ 2)) / 2) = 0 := by nlinarith
  rcases mul_eq_zero.1 hfac with h | h
  · linarith
  · -- the larger root is at least `1 + ε/2 > w` unless `w = 1` and `ε = 0`
    have : w = (2 + ε + Real.sqrt (4 + 4 * ε - 3 * ε ^ 2)) / 2 := by linarith
    have hge : 1 + ε / 2 ≤ w := by rw [this]; linarith
    have hε : ε = 0 := by linarith
    subst hε
    have : w = 0 := by rw [hw]; ring
    linarith

/-- **Theorem 3.6, the threshold `ε_B`.** For `0 ≤ ε ≤ 1`, `f(ε) = εℓ*(ε) - (1-ε) > 0` with
`εℓ* = (2 + ε - √(4 + 4ε - 3ε²))/2` iff `ε > ε_B = (1 + √13)/6`. -/
theorem epsB_threshold {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    1 - ε < (2 + ε - Real.sqrt (4 + 4 * ε - 3 * ε ^ 2)) / 2 ↔ (1 + Real.sqrt 13) / 6 < ε := by
  have hD : 0 ≤ 4 + 4 * ε - 3 * ε ^ 2 := by nlinarith
  have hs := Real.sq_sqrt hD
  have hs0 := Real.sqrt_nonneg (4 + 4 * ε - 3 * ε ^ 2)
  have h13 : Real.sqrt 13 ^ 2 = 13 := Real.sq_sqrt (by norm_num)
  have h130 := Real.sqrt_nonneg 13
  constructor
  · intro h
    -- `√(4 + 4ε - 3ε²) < 3ε`, so `3ε² - ε - 1 > 0`
    have h1 : Real.sqrt (4 + 4 * ε - 3 * ε ^ 2) < 3 * ε := by linarith
    have h2 : 0 < 3 * ε ^ 2 - ε - 1 := by nlinarith
    by_contra hc; push Not at hc
    have e : 3 * (ε - (1 + Real.sqrt 13) / 6) * (ε - (1 - Real.sqrt 13) / 6) =
        3 * ε ^ 2 - ε - 1 := by linear_combination (-1 / 12) * h13
    have h3 : 0 ≤ ε - (1 - Real.sqrt 13) / 6 := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.2 hc) h3]
  · intro h
    have h2 : 0 < 3 * ε ^ 2 - ε - 1 := by nlinarith
    have h1 : Real.sqrt (4 + 4 * ε - 3 * ε ^ 2) < 3 * ε := by
      rw [Real.sqrt_lt' (by nlinarith)]; nlinarith
    linarith

/-- **Theorem 3.9, the threshold `3/4`.** With `ϖ(ε) = (2ε + 1 - √(4ε + 1))/(2ε)` the root in
`(0, 1/2)` of `ϖ = ε(1 - ϖ)²`: for `0 < ε`, `εϖ(ε) > 1 - ε` iff `ε > 3/4`; and
`ϖ(3/4) = 1/3`. -/
theorem varpi_threshold {ε : ℝ} (hε0 : 0 < ε) :
    (1 - ε < ε * ((2 * ε + 1 - Real.sqrt (4 * ε + 1)) / (2 * ε)) ↔ 3 / 4 < ε) ∧
      (2 * (3 / 4 : ℝ) + 1 - Real.sqrt (4 * (3 / 4) + 1)) / (2 * (3 / 4)) = 1 / 3 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 4 * ε + 1 by linarith)
  have hs0 := Real.sqrt_nonneg (4 * ε + 1)
  have e : ε * ((2 * ε + 1 - Real.sqrt (4 * ε + 1)) / (2 * ε)) =
      (2 * ε + 1 - Real.sqrt (4 * ε + 1)) / 2 := by field_simp
  refine ⟨?_, ?_⟩
  · rw [e]
    constructor
    · intro h
      have h1 : Real.sqrt (4 * ε + 1) < 4 * ε - 1 := by linarith
      nlinarith
    · intro h
      have h1 : Real.sqrt (4 * ε + 1) < 4 * ε - 1 := by
        rw [Real.sqrt_lt' (by linarith)]; nlinarith
      linarith
  · have : Real.sqrt (4 * (3 / 4 : ℝ) + 1) = 2 := by
      rw [show (4 * (3 / 4 : ℝ) + 1) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [this]; norm_num

end GC.RandomSeqNOR
