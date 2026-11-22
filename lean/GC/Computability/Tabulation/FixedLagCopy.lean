import GC.Computability.Tabulation.GlobalTable
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Barrier: fixed-lag copy (manuscript 010e, Section 2)

Synchronous correction with radius `L` (Definition 2.1) for a general append-only machine, and
the linear correction rank of the copy program (Theorem 2.2).
-/

namespace GC.Tabulation

namespace AppendMachine

variable {Q W : Type*} (M : AppendMachine Q W)

/-- The candidate `C^g` of synchronous correction with radius `L` on a block with exact boundary
`a`, for the guess vector `g` (Definition 2.1). `C^g_t = C*_t` for `t ≤ a`; for `t > a`,
`C^g_t = Φ_t(C^g_{t-1}, ĥ_t)` where `ĥ_t` is the real read result for an initial or invalid address
or a cell written at a stage `s ≤ a + 1`, is `w(C^g_{s-1})` for a cell written at `s ∈ (a+1, t)` with
gap `t - s + 1 ≤ L`, and is the guess `g_t` for such a cell with gap `> L`. -/
def cand (a L : ℕ) (g : ℕ → W) : ℕ → Q
  | 0 => M.real 0
  | t + 1 =>
    if t + 1 ≤ a then M.real (t + 1) else
    M.Φ (t + 1) (cand a L g t)
      (if 0 ≤ M.p (cand a L g t) ∧ M.p (cand a L g t) < M.m then
        some (M.Hin (M.p (cand a L g t)).toNat)
       else if _h : (M.m : ℤ) ≤ M.p (cand a L g t) ∧ M.p (cand a L g t) < M.m + t then
         if (M.p (cand a L g t) - M.m).toNat + 1 ≤ a + 1 then
           some (M.w (M.real (M.p (cand a L g t) - M.m).toNat))
         else if t + 1 - ((M.p (cand a L g t) - M.m).toNat + 1) + 1 ≤ L then
           some (M.w (cand a L g (M.p (cand a L g t) - M.m).toNat))
         else some (g (t + 1))
       else none)
termination_by t => t
decreasing_by all_goals omega

/-- Stage `t` of the block makes a *long* read under the candidate: an internal read of a cell
written at a stage `s ∈ (a + 1, t)` with gap `t - s + 1 > L`. -/
def IsLong (a L : ℕ) (g : ℕ → W) (t : ℕ) : Prop :=
  a < t ∧ (M.m : ℤ) ≤ M.p (M.cand a L g (t - 1)) ∧ M.p (M.cand a L g (t - 1)) < M.m + t - 1 ∧
    a + 1 < (M.p (M.cand a L g (t - 1)) - M.m).toNat + 1 ∧
    L < t - ((M.p (M.cand a L g (t - 1)) - M.m).toNat + 1) + 1

open Classical in
/-- The correction of `g`: at every stage with a long read, the guess is replaced by the word
`w(C^g_{s-1})` written by the candidate. -/
noncomputable def correct (a L : ℕ) (g : ℕ → W) : ℕ → W := fun t =>
  if M.IsLong a L g t then M.w (M.cand a L g (M.p (M.cand a L g (t - 1)) - M.m).toNat) else g t

/-- The guess vectors `g^{(r)}`, starting from the constant default word `ω`. -/
noncomputable def guesses (a L : ℕ) (ω : W) (r : ℕ) : ℕ → W :=
  (M.correct a L)^[r] (fun _ => ω)

lemma cand_of_le (a L : ℕ) (g : ℕ → W) {t : ℕ} (ht : t ≤ a) : M.cand a L g t = M.real t := by
  cases t with
  | zero => rw [cand]
  | succ t => rw [cand, if_pos ht]

lemma cand_succ (a L : ℕ) (g : ℕ → W) {t : ℕ} (ht : a ≤ t) :
    M.cand a L g (t + 1) = M.Φ (t + 1) (M.cand a L g t)
      (if 0 ≤ M.p (M.cand a L g t) ∧ M.p (M.cand a L g t) < M.m then
        some (M.Hin (M.p (M.cand a L g t)).toNat)
       else if (M.m : ℤ) ≤ M.p (M.cand a L g t) ∧ M.p (M.cand a L g t) < M.m + t then
         if (M.p (M.cand a L g t) - M.m).toNat + 1 ≤ a + 1 then
           some (M.w (M.real (M.p (M.cand a L g t) - M.m).toNat))
         else if t + 1 - ((M.p (M.cand a L g t) - M.m).toNat + 1) + 1 ≤ L then
           some (M.w (M.cand a L g (M.p (M.cand a L g t) - M.m).toNat))
         else some (g (t + 1))
       else none) := by
  rw [cand, if_neg (by omega)]
  simp only [dite_eq_ite]

end AppendMachine

/-! ### The copy program with lag `d = L + 1` -/

section CopyCorrection

variable {L : ℕ} (hL : 1 ≤ L)

include hL

local notation "Mc" => copyMachine (L + 1) (fun _ : ℕ => true)

lemma copyC_fst (a : ℕ) (g : ℕ → Bool) (t : ℕ) : ((Mc).cand a L g t).1 = t := by
  rcases le_or_gt t a with h | h
  · rw [AppendMachine.cand_of_le _ _ _ _ h]
    exact copy_real_fst _ t
  · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    rw [AppendMachine.cand_succ _ _ _ _ (by omega)]
    rfl

lemma copyC_real_snd (k : ℕ) : ((Mc).real k).2 = true := by
  cases k with
  | zero => simp [AppendMachine.real_zero, copyMachine]
  | succ k => rw [copy_real (by omega)]

/-- In a block from the boundary `a`, relative stage `t ≥ 1` of the candidate reads the real
value `1` if `t ≤ d` and its guess otherwise. -/
lemma copyC_snd (a : ℕ) (g : ℕ → Bool) (t : ℕ) (ht : 1 ≤ t) :
    ((Mc).cand a L g (a + t)).2 = if t ≤ L + 1 then true else g (a + t) := by
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  rw [show a + (t' + 1) = (a + t') + 1 by ring, AppendMachine.cand_succ _ _ _ _ (by omega),
    copy_p, copyC_fst hL, copy_Φ, copy_m, copy_Hin]
  by_cases h1 : a + t' + 1 ≤ L + 1
  · rw [if_pos h1, if_pos (by omega), if_pos (by omega)]
    rfl
  · rw [if_neg h1, if_neg (by omega), if_pos (by omega)]
    have e : ((a + t' : ℕ) + 1 - ((L + 1 : ℕ) : ℤ)).toNat = a + t' - L := by omega
    simp only [copy_m] at e ⊢
    rw [e]
    by_cases h2 : a + t' - L + 1 ≤ a + 1
    · rw [if_pos h2, if_pos (by omega), copy_w, copyC_real_snd hL]
      rfl
    · rw [if_neg h2, if_neg (by omega), if_neg (by omega)]
      rfl

lemma copyC_isLong (a : ℕ) (g : ℕ → Bool) (t : ℕ) (ht : 1 ≤ t) :
    (Mc).IsLong a L g (a + t) ↔ L + 1 < t := by
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  simp only [AppendMachine.IsLong, show a + (t' + 1) - 1 = a + t' by omega, copy_p, copyC_fst hL,
    copy_m]
  by_cases h1 : a + t' + 1 ≤ L + 1
  · rw [if_pos h1]
    constructor
    · rintro ⟨-, h2, -⟩; push_cast at h2; omega
    · intro h; omega
  · rw [if_neg h1]
    push_cast
    omega

/-- **Theorem 2.2(a).** For the copy program with lag `d = L + 1 ≥ 2`, all initial words `1` and
default guess `0`: in a block with boundary `a`, the value coordinate of `C^{g^{(r)}}_{a+t}`
(`t ≥ 1`) is `1` exactly when `t ≤ (r + 1) d`. -/
theorem copy_correction_value (a r : ℕ) (t : ℕ) (ht : 1 ≤ t) :
    ((Mc).cand a L ((Mc).guesses a L false r) (a + t)).2 = decide (t ≤ (r + 1) * (L + 1)) := by
  induction r generalizing t with
  | zero =>
    rw [copyC_snd hL _ _ _ ht]
    split_ifs with h
    · simp [h]
    · simp only [AppendMachine.guesses, Function.iterate_zero, id]
      simp; omega
  | succ r ih =>
    rw [copyC_snd hL _ _ _ ht]
    split_ifs with h
    · symm; rw [decide_eq_true_iff]; nlinarith
    · simp only [AppendMachine.guesses, Function.iterate_succ_apply']
      rw [AppendMachine.correct, if_pos ((copyC_isLong hL a _ t ht).mpr (by omega))]
      simp only [show a + t - 1 = a + (t - 1) by omega, copy_p, copyC_fst hL, copy_m, copy_w]
      rw [if_neg (by omega)]
      have e : ((a + (t - 1) : ℕ) + 1 - ((L + 1 : ℕ) : ℤ)).toNat = a + (t - (L + 1)) := by omega
      rw [e]
      have := ih (t - (L + 1)) (by omega)
      simp only [AppendMachine.guesses] at this
      rw [this]
      have hm : (r + 1 + 1) * (L + 1) = (r + 1) * (L + 1) + (L + 1) := by ring
      rw [hm]
      apply decide_eq_decide.mpr
      generalize (r + 1) * (L + 1) = P
      omega

/-- **Theorem 2.2(a), correction rank.** The block `J = (a, a + m]` is exact after `r` correction
rounds iff `m ≤ (r + 1) d`; hence `χ_L(J) = ⌈m/d⌉ - 1`. -/
theorem copy_block_exact_iff (a mlen r : ℕ) :
    (∀ t, a < t → t ≤ a + mlen → (Mc).cand a L ((Mc).guesses a L false r) t = (Mc).real t) ↔
      mlen ≤ (r + 1) * (L + 1) := by
  have hreal : ∀ t, (Mc).real t = (t, true) := fun t =>
    Prod.ext (copy_real_fst _ t) (copyC_real_snd hL t)
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos mlen with h0 | h0
    · omega
    · have := h (a + mlen) (by omega) le_rfl
      have h2 := congrArg Prod.snd this
      rw [copy_correction_value hL a r mlen h0, hreal] at h2
      simpa using h2
  · intro h t ht1 ht2
    obtain ⟨t', rfl⟩ : ∃ t', t = a + t' := ⟨t - a, by omega⟩
    rw [hreal]
    refine Prod.ext (copyC_fst hL _ _ _) ?_
    rw [copy_correction_value hL a r t' (by omega)]
    simp only [decide_eq_true_eq]
    omega

end CopyCorrection

/-- `⌈x/d⌉ + ⌈y/d⌉ ≥ ⌈(x + y)/d⌉`. -/
lemma ceil_div_add_le (d x y : ℕ) (hd : 0 < d) :
    (x + y + d - 1) / d ≤ (x + d - 1) / d + (y + d - 1) / d := by
  have hx := Nat.lt_div_mul_add (a := x + d - 1) hd
  have hy := Nat.lt_div_mul_add (a := y + d - 1) hd
  rw [Nat.div_le_iff_le_mul_add_pred hd, mul_add]
  rw [Nat.mul_comm] at hx hy
  generalize d * ((x + d - 1) / d) = X at *
  generalize d * ((y + d - 1) / d) = Y at *
  omega

/-- **Theorem 2.2(b), lower bound.** For every partition of `(0, N]` into blocks
`0 = c_0 < c_1 < ⋯ < c_k = N`, the total number of correction rounds
`∑_j (χ_L(J_j) + 1) = ∑_j ⌈(c_{j+1} - c_j)/d⌉` (Theorem 2.2(a)) is at least `⌈N/d⌉`. The
partition into blocks of length `d` attains it, each block having `χ_L = 0`
(`copy_block_exact_iff` with `r = 0`). -/
theorem copy_multiscale_lower (d N : ℕ) (hd : 0 < d) (c : ℕ → ℕ) (k : ℕ) (hc0 : c 0 = 0)
    (hck : c k = N) (hmono : ∀ j < k, c j ≤ c (j + 1)) :
    (N + d - 1) / d ≤ ∑ j ∈ Finset.range k, ((c (j + 1) - c j) + d - 1) / d := by
  subst hck
  induction k with
  | zero =>
    simp only [hc0, Finset.range_zero, Finset.sum_empty, zero_add, nonpos_iff_eq_zero]
    exact Nat.div_eq_of_lt (by omega)
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have := ih (fun j hj => hmono j (by omega))
    have h2 := ceil_div_add_le d (c k) (c (k + 1) - c k) hd
    have h3 := hmono k (by omega)
    rw [show c k + (c (k + 1) - c k) = c (k + 1) by omega] at h2
    omega

end GC.Tabulation
