import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The numbers of Theorems 3.5 and 3.7 (manuscript 001b)

The recursion `q₀ = 1 - (1-ε)⁴(1-β_u)(1-β_v)`, `q_{l+1} = 1 - (1-ε)⁸(1 - φ(q_l))`,
`φ(q) = 3q² - 2q³`, of Step 2 of Theorem 3.5, the bounds of its Step 3, the constant of its
Step 4, and the ten-step bound `q₁₀ ≤ 0.1161` of Theorem 3.7.
-/

namespace GC.RandomSeqNOR

/-- `φ(q) = 3q² - 2q³`, the probability that at least two of three independent events of
probability `q` occur. -/
def phi (q : ℝ) : ℝ := 3 * q ^ 2 - 2 * q ^ 3

/-- The conditional probabilities `q_l` of Step 2 of Theorem 3.5. -/
def qSeq (ε βu βv : ℝ) : ℕ → ℝ
  | 0 => 1 - (1 - ε) ^ 4 * (1 - βu) * (1 - βv)
  | l + 1 => 1 - (1 - ε) ^ 8 * (1 - phi (qSeq ε βu βv l))

theorem phi_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) : phi x ≤ phi y := by
  unfold phi
  have h : phi y - phi x = (y - x) * (3 * (x + y) - 2 * (x ^ 2 + x * y + y ^ 2)) := by
    unfold phi; ring
  have h2 : 0 ≤ 3 * (x + y) - 2 * (x ^ 2 + x * y + y ^ 2) := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.2 hxy) h2]

theorem phi_nonneg {q : ℝ} (h1 : q ≤ 1) : 0 ≤ phi q := by
  unfold phi; nlinarith [sq_nonneg q, mul_nonneg (sq_nonneg q) (sub_nonneg.2 h1)]

theorem phi_le_one {q : ℝ} (h0 : 0 ≤ q) : phi q ≤ 1 := by
  unfold phi; nlinarith [mul_nonneg (sq_nonneg (1 - q)) (by linarith : (0:ℝ) ≤ 1 + 2 * q)]

theorem one_sub_pow_ge {ε : ℝ} (hε : ε ≤ 1) (n : ℕ) : 1 - n * ε ≤ (1 - ε) ^ n := by
  have := one_add_mul_le_pow (a := -ε) (by linarith) n
  simpa [sub_eq_add_neg, mul_neg] using this

theorem qSeq_mem {ε βu βv : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hu0 : 0 ≤ βu) (hu1 : βu ≤ 1)
    (hv0 : 0 ≤ βv) (hv1 : βv ≤ 1) : ∀ l, 0 ≤ qSeq ε βu βv l ∧ qSeq ε βu βv l ≤ 1 := by
  have hp : ∀ n : ℕ, 0 ≤ (1 - ε) ^ n ∧ (1 - ε) ^ n ≤ 1 := fun n =>
    ⟨pow_nonneg (by linarith) n, pow_le_one₀ (by linarith) (by linarith)⟩
  intro l
  induction l with
  | zero =>
    simp only [qSeq]
    obtain ⟨a0, a1⟩ := hp 4
    have b0 : 0 ≤ (1 - βu) * (1 - βv) := mul_nonneg (by linarith) (by linarith)
    have b1 : (1 - βu) * (1 - βv) ≤ 1 := by nlinarith
    constructor
    · nlinarith [mul_le_mul a1 b1 b0 zero_le_one]
    · nlinarith [mul_nonneg a0 b0]
  | succ l ih =>
    simp only [qSeq]
    obtain ⟨a0, a1⟩ := hp 8
    have c0 := phi_nonneg ih.2
    have c1 := phi_le_one ih.1
    constructor
    · nlinarith [mul_le_mul a1 (by linarith : 1 - phi (qSeq ε βu βv l) ≤ 1)
        (by linarith : 0 ≤ 1 - phi (qSeq ε βu βv l)) zero_le_one]
    · nlinarith [mul_nonneg a0 (by linarith : 0 ≤ 1 - phi (qSeq ε βu βv l))]

/-- **Theorem 3.5, Step 3.** For `ε ≤ 1/1000` and `β_u, β_v ≤ 1/10`:
`q₀ ≤ 0.204`, `q₁ ≤ 0.11587`, `q₂ ≤ 0.04517`, `q₃ ≤ 0.01394 = q̄`. -/
theorem embed_step3 {ε βu βv : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 1000) (hu0 : 0 ≤ βu)
    (hu : βu ≤ 1 / 10) (hv0 : 0 ≤ βv) (hv : βv ≤ 1 / 10) :
    qSeq ε βu βv 0 ≤ 0.204 ∧ qSeq ε βu βv 1 ≤ 0.11587 ∧ qSeq ε βu βv 2 ≤ 0.04517 ∧
      qSeq ε βu βv 3 ≤ 0.01394 := by
  have hm := qSeq_mem hε0 (by linarith) hu0 (by linarith) hv0 (by linarith)
  -- `q_{l+1} ≤ 8ε + φ(q_l)`
  have step : ∀ l, qSeq ε βu βv (l + 1) ≤ 8 * ε + phi (qSeq ε βu βv l) := by
    intro l
    simp only [qSeq]
    have h8 := one_sub_pow_ge (ε := ε) (by linarith) 8
    have c0 := phi_nonneg (hm l).2
    have c1 := phi_le_one (hm l).1
    push_cast at h8
    nlinarith [mul_le_mul_of_nonneg_right h8 (by linarith : 0 ≤ 1 - phi (qSeq ε βu βv l)),
      mul_nonneg hε0 c0]
  have b0 : qSeq ε βu βv 0 ≤ 0.204 := by
    simp only [qSeq]
    have h4 := one_sub_pow_ge (ε := ε) (by linarith) 4
    push_cast at h4
    have e1 : 1 - βu - βv ≤ (1 - βu) * (1 - βv) := by nlinarith
    have e2 : (1 - 4 * ε) * (1 - βu - βv) ≤ (1 - ε) ^ 4 * ((1 - βu) * (1 - βv)) :=
      mul_le_mul h4 e1 (by linarith) (by positivity)
    nlinarith
  have b1 : qSeq ε βu βv 1 ≤ 0.11587 := by
    have := step 0
    have := phi_mono (hm 0).1 b0 (by norm_num)
    have : phi 0.204 ≤ 0.10787 := by norm_num [phi]
    linarith
  have b2 : qSeq ε βu βv 2 ≤ 0.04517 := by
    have := step 1
    have := phi_mono (hm 1).1 b1 (by norm_num)
    have : phi 0.11587 ≤ 0.03717 := by norm_num [phi]
    linarith
  have b3 : qSeq ε βu βv 3 ≤ 0.01394 := by
    have := step 2
    have := phi_mono (hm 2).1 b2 (by norm_num)
    have : phi 0.04517 ≤ 0.00594 := by norm_num [phi]
    linarith
  exact ⟨b0, b1, b2, b3⟩

/-- **Theorem 3.5, Step 4, constant:** `10 e q̄ < 0.38` for `q̄ = 0.01394`; hence
`(10 e q̄)^k ≤ 2^{-k}`. -/
theorem embed_step4_const : 10 * Real.exp 1 * 0.01394 < 0.38 ∧
    ∀ k : ℕ, (10 * Real.exp 1 * 0.01394) ^ k ≤ (1 / 2) ^ k := by
  have h := Real.exp_one_lt_d9
  have h0 := Real.exp_pos 1
  refine ⟨by linarith, fun k => pow_le_pow_left₀ (by positivity) (by linarith) k⟩

/-- **Theorem 3.7, the ten iterations.** Let `ε ≤ 1/64` and let `q₀, …, q₁₀ ≥ 0` satisfy
`q₀ ≤ 1 - (1 - 2.931ε)(5/6)²` and `q_{l+1} ≤ 1 - (1 - 4.86ε)(1 - φ(q_l))`.
Then `q₁₀ ≤ q̄ = 0.1161`. -/
theorem embed64_ten_iterations {ε : ℝ} (hε : ε ≤ 1 / 64) (q : ℕ → ℝ)
    (hq0 : ∀ l, 0 ≤ q l)
    (h0 : q 0 ≤ 1 - (1 - 2.931 * ε) * (5 / 6) ^ 2)
    (hs : ∀ l, q (l + 1) ≤ 1 - (1 - 4.86 * ε) * (1 - phi (q l))) :
    q 10 ≤ 0.1161 := by
  -- one step of the chain, monotone in `ε` and in `q_l`
  have step : ∀ (l : ℕ) (b c : ℝ), 0 ≤ q l → q l ≤ b → b ≤ 1 →
      1 - (1 - 4.86 / 64) * (1 - phi b) ≤ c → q (l + 1) ≤ c := by
    intro l b c h0' hb hb1 hc
    have p1 := phi_mono h0' hb hb1
    have p2 := phi_le_one (le_trans h0' hb)
    have := hs l
    nlinarith [mul_le_mul (by linarith : 1 - 4.86 / 64 ≤ 1 - 4.86 * ε)
      (by linarith : 1 - phi b ≤ 1 - phi (q l)) (by linarith) (by linarith)]
  have b0 : q 0 ≤ 0.337359 := by nlinarith
  have step' : ∀ (l : ℕ) (b c : ℝ), q l ≤ b → b ≤ 1 →
      1 - (1 - 4.86 / 64) * (1 - phi b) ≤ c → q (l + 1) ≤ c :=
    fun l b c hb hb1 hc => step l b c (hq0 l) hb hb1 hc
  have b1 : q 1 ≤ 0.320485 := step' 0 _ _ b0 (by norm_num) (by norm_num [phi])
  have b2 : q 2 ≤ 0.299836 := step' 1 _ _ b1 (by norm_num) (by norm_num [phi])
  have b3 : q 3 ≤ 0.275345 := step' 2 _ _ b2 (by norm_num) (by norm_num [phi])
  have b4 : q 4 ≤ 0.247531 := step' 3 _ _ b3 (by norm_num) (by norm_num [phi])
  have b5 : q 5 ≤ 0.217765 := step' 4 _ _ b4 (by norm_num) (by norm_num [phi])
  have b6 : q 6 ≤ 0.188314 := step' 5 _ _ b5 (by norm_num) (by norm_num [phi])
  have b7 : q 7 ≤ 0.161904 := step' 6 _ _ b6 (by norm_num) (by norm_num [phi])
  have b8 : q 8 ≤ 0.140762 := step' 7 _ _ b7 (by norm_num) (by norm_num [phi])
  have b9 : q 9 ≤ 0.125711 := step' 8 _ _ b8 (by norm_num) (by norm_num [phi])
  have b10 : q 10 ≤ 0.116076 := step' 9 _ _ b9 (by norm_num) (by norm_num [phi])
  exact le_trans b10 (by norm_num)

end GC.RandomSeqNOR
