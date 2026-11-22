import GC.Computability.SeqNORNormalForms.Basic

/-!
# 006b: the reset normal form of Sequential NOR

A position `i ≥ 1` is a reset if `x_{j_i} = 1`; a virtual reset sits at `-1`. Sets
`R ⊆ {-1, 1, …, n}` containing `-1` are represented by their indicator `R : ℕ → Bool` on
the positive positions (position `0` is never a reset, and `-1 ∈ R` is implicit).
-/

namespace GC.SeqNORNormalForms

/-- `pred_R(p) = max {r ∈ R : r ≤ p}` for `R ∋ -1`, `R ⊆ {-1, 1, 2, …}`. -/
def predR (R : ℕ → Bool) : ℕ → ℤ
  | 0 => -1
  | p + 1 => if R (p + 1) then ((p + 1 : ℕ) : ℤ) else predR R p

/-- The reset set `R⋆ = {-1} ∪ {i ≥ 1 : x_{j_i} = 1}` (on positive positions). -/
def resetSet (j : ℕ → ℕ) (i : ℕ) : Bool := decide (1 ≤ i) && trace j (j i)

/-- The reset operator `Φ(R) = {-1} ∪ {i ∈ [1,n] : j_i - pred_R(j_i) is odd}`. -/
def resetOp (n : ℕ) (j : ℕ → ℕ) (R : ℕ → Bool) (i : ℕ) : Bool :=
  decide (1 ≤ i ∧ i ≤ n ∧ ((j i : ℤ) - predR R (j i)) % 2 = 1)

/-- Two candidate sets agree on the positions `1, …, m`. -/
def AgreeUpTo (m : ℕ) (R R' : ℕ → Bool) : Prop := ∀ i, 1 ≤ i → i ≤ m → R i = R' i

theorem predR_congr {R R' : ℕ → Bool} {m : ℕ} (h : AgreeUpTo m R R') :
    ∀ p, p ≤ m → predR R p = predR R' p := by
  intro p
  induction p with
  | zero => intro _; rfl
  | succ p ih =>
    intro hp
    simp only [predR, h (p + 1) (by omega) hp, ih (by omega)]

theorem predR_le (R : ℕ → Bool) : ∀ p, predR R p ≤ p ∧ -1 ≤ predR R p := by
  intro p
  induction p with
  | zero => simp [predR]
  | succ p ih => simp only [predR]; split <;> omega

/-- **Theorem 3.1 of 006b (reset-predecessor normal form).** For `0 ≤ i ≤ n`,
`x_i = (i - pred_{R⋆}(i)) mod 2`, and for `1 ≤ i ≤ n`, `i ∈ R⋆` iff `j_i - pred_{R⋆}(j_i)` is
odd. -/
theorem reset_normal_form (n : ℕ) (j : ℕ → ℕ) (hj : IsParentArray n j) :
    (∀ i, i ≤ n → (trace j i = true ↔ ((i : ℤ) - predR (resetSet j) i) % 2 = 1)) ∧
    (∀ i, 1 ≤ i → i ≤ n →
      (resetSet j i = true ↔ ((j i : ℤ) - predR (resetSet j) (j i)) % 2 = 1)) := by
  have h1 : ∀ i, i ≤ n → (trace j i = true ↔ ((i : ℤ) - predR (resetSet j) i) % 2 = 1) := by
    intro i
    induction i with
    | zero => intro _; simp [trace_zero, predR]
    | succ i ih =>
      intro hi
      have hs := trace_succ j i (hj (i + 1) (by omega) hi)
      simp only [predR]
      by_cases hr : resetSet j (i + 1) = true
      · have ht : trace j (j (i + 1)) = true := by simpa [resetSet] using hr
        rw [hs, ht, if_pos hr]; simp [nor]
      · have ht : trace j (j (i + 1)) = false := by simpa [resetSet] using hr
        rw [hs, ht, if_neg hr]
        have := ih (by omega)
        cases h : trace j i <;> simp [nor, h] at this ⊢ <;> omega
  refine ⟨h1, ?_⟩
  intro i hi hin
  have := h1 (j i) (by have := hj i hi hin; omega)
  simp only [resetSet, show decide (1 ≤ i) = true by simp [hi], Bool.true_and]
  exact this

/-- **Theorem 3.1 (stage-wise form) / Proposition 3.3 (fixed point).** `R⋆` is a fixed point
of `Φ` on the positions `1, …, n`. -/
theorem resetOp_fixed (n : ℕ) (j : ℕ → ℕ) (hj : IsParentArray n j) :
    AgreeUpTo n (resetOp n j (resetSet j)) (resetSet j) := by
  intro i hi hin
  have := (reset_normal_form n j hj).2 i hi hin
  unfold resetOp
  by_cases h : resetSet j i = true
  · rw [h]; simp [hi, hin, this.1 h]
  · rw [Bool.not_eq_true] at h; rw [h]
    simp only [hi, hin, true_and, decide_eq_false_iff_not]
    intro h'; exact absurd (this.2 h') (by simp [h])

/-- Membership of `i` in `Φ(R)` depends only on `R` below `i`. -/
theorem resetOp_local (n : ℕ) (j : ℕ → ℕ) (hj : IsParentArray n j) {R R' : ℕ → Bool} {i : ℕ}
    (hi : 1 ≤ i) (hin : i ≤ n) (h : AgreeUpTo (i - 1) R R') :
    resetOp n j R i = resetOp n j R' i := by
  unfold resetOp
  rw [predR_congr h (j i) (by have := hj i hi hin; omega)]

/-- **Lemma 3.4 of 006b (first disagreement).** Let `q ∈ [1,n]` be the least position where
`R` and `Φ(R)` disagree. Then `R` agrees with `R⋆` below `q`, `q ∈ R⋆ ↔ q ∈ Φ(R)`, and
hence `q` is the first error of `R`. -/
theorem first_disagreement (n : ℕ) (j : ℕ → ℕ) (hj : IsParentArray n j) (R : ℕ → Bool)
    (q : ℕ) (hq : 1 ≤ q) (hqn : q ≤ n) (hdis : R q ≠ resetOp n j R q)
    (hmin : AgreeUpTo (q - 1) R (resetOp n j R)) :
    AgreeUpTo (q - 1) R (resetSet j) ∧ resetSet j q = resetOp n j R q ∧ R q ≠ resetSet j q := by
  have hfix := resetOp_fixed n j hj
  have hagree : AgreeUpTo (q - 1) R (resetSet j) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi hiq
      rw [hmin i hi hiq, resetOp_local n j hj hi (by omega)
        (fun k hk hki => ih k (by omega) hk (by omega)), hfix i hi (by omega)]
  have hq' : resetSet j q = resetOp n j R q := by
    rw [← hfix q hq hqn, resetOp_local n j hj hq hqn (fun k hk hkq => (hagree k hk hkq).symm)]
  exact ⟨hagree, hq', by rw [hq']; exact hdis⟩

/-- **Proposition 3.3 of 006b (uniqueness).** `R⋆` is the unique fixed point of `Φ` on the
positions `1, …, n`. -/
theorem resetOp_unique (n : ℕ) (j : ℕ → ℕ) (hj : IsParentArray n j) (R : ℕ → Bool)
    (hR : AgreeUpTo n (resetOp n j R) R) : AgreeUpTo n R (resetSet j) := by
  have hfix := resetOp_fixed n j hj
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi hin
    rw [← hR i hi hin, resetOp_local n j hj hi hin (fun k hk hki => ih k (by omega) hk (by omega)),
      hfix i hi hin]

/-- **Corollary 3.5 of 006b.** For every start `R₀`, the iterates `R_{t+1} = Φ(R_t)` agree
with `R⋆` on `1, …, t`; in particular `R_t = R⋆` (on `1, …, n`) for all `t ≥ n`. -/
theorem resetOp_iterate (n : ℕ) (j : ℕ → ℕ) (hj : IsParentArray n j) (R₀ : ℕ → Bool) :
    ∀ t, AgreeUpTo (min t n) ((resetOp n j)^[t] R₀) (resetSet j) := by
  have hfix := resetOp_fixed n j hj
  intro t
  induction t with
  | zero => intro i hi hit; omega
  | succ t ih =>
    intro i hi hit
    rw [Function.iterate_succ_apply']
    rw [resetOp_local n j hj hi (by omega) (fun k hk hki => ih k hk (by omega)),
      hfix i hi (by omega)]

theorem resetOp_iterate_n (n : ℕ) (j : ℕ → ℕ) (hj : IsParentArray n j) (R₀ : ℕ → Bool)
    (t : ℕ) (ht : n ≤ t) : AgreeUpTo n ((resetOp n j)^[t] R₀) (resetSet j) := by
  have := resetOp_iterate n j hj R₀ t
  rwa [Nat.min_eq_right ht] at this

/-- **Remark 3.6(b) of 006b.** `Φ²` is not monotone: for `j = (0,0,2,1,4)`,
`A = {-1,3,5} ⊆ B = {-1,1,2,3,4,5}` but `Φ²(A) = {-1,1,2,5} ⊄ Φ²(B) = {-1,1,2}`. -/
theorem resetOp_sq_not_monotone :
    let j : ℕ → ℕ := fun i => if i = 1 then 0 else if i = 2 then 0 else if i = 3 then 2
      else if i = 4 then 1 else if i = 5 then 4 else 0
    let A : ℕ → Bool := fun i => decide (i = 3 ∨ i = 5)
    let B : ℕ → Bool := fun i => decide (1 ≤ i ∧ i ≤ 5)
    (∀ i, A i = true → B i = true) ∧
    (∀ i, i ≤ 6 → resetOp 5 j (resetOp 5 j A) i = decide (i = 1 ∨ i = 2 ∨ i = 5)) ∧
    (∀ i, i ≤ 6 → resetOp 5 j (resetOp 5 j B) i = decide (i = 1 ∨ i = 2)) := by
  refine ⟨by intro i; simp; omega, ?_, ?_⟩ <;> decide

/-- **Proposition 3.2 of 006b (event queue).** With child lists `C_s = {i > s : j_i = s}` and
pending events `E_t = ⋃_{s ≤ t, x_s = 1} C_s ∩ {t+1, …, n}`: `x_i = 1` iff `x_{i-1} = 0` and
`i ∉ E_{i-1}`. -/
theorem event_queue (n : ℕ) (j : ℕ → ℕ) (hj : IsParentArray n j) (i : ℕ) (hi : 1 ≤ i)
    (hin : i ≤ n) :
    let E : ℕ → ℕ → Prop := fun t m => t < m ∧ m ≤ n ∧ ∃ s, s ≤ t ∧ trace j s = true ∧ j m = s
    (trace j i = true ↔ trace j (i - 1) = false ∧ ¬ E (i - 1) i) ∧
    (∀ m, E i m ↔ (E (i - 1) m ∧ m ≠ i) ∨ (trace j i = true ∧ i < m ∧ m ≤ n ∧ j m = i)) := by
  intro E
  have hji := hj i hi hin
  have hE : E (i - 1) i ↔ trace j (j i) = true := by
    simp only [E]
    constructor
    · rintro ⟨-, -, s, -, hs, rfl⟩; exact hs
    · intro h; exact ⟨by omega, hin, j i, by omega, h, rfl⟩
  refine ⟨?_, ?_⟩
  · rw [hE, trace_at j i hi hji]
    cases trace j (i - 1) <;> cases trace j (j i) <;> simp [nor]
  · intro m
    simp only [E]
    constructor
    · rintro ⟨h1, h2, s, hs, hxs, hjm⟩
      by_cases hsi : s = i
      · subst hsi; right; exact ⟨hxs, h1, h2, hjm⟩
      · left; exact ⟨⟨by omega, h2, s, by omega, hxs, hjm⟩, by omega⟩
    · rintro (⟨⟨h1, h2, s, hs, hxs, hjm⟩, hmi⟩ | ⟨hxi, h1, h2, hjm⟩)
      · exact ⟨by omega, h2, s, by omega, hxs, hjm⟩
      · exact ⟨h1, h2, i, le_rfl, hxi, hjm⟩

/-- **Theorem 3.7 of 006b (realizable traces).** Every string `z_0, …, z_n` with `z_0 = 1`,
`z_1 = 0` and no two consecutive ones is the trace of the parent array `j_1 = 0`,
`j_i = 1` if `z_i = 1` and `j_i = 0` if `z_i = 0`. -/
theorem realizable_traces (n : ℕ) (z : ℕ → Bool) (hz0 : z 0 = true) (hz1 : 1 ≤ n → z 1 = false)
    (hcons : ∀ i, 1 ≤ i → i ≤ n → z i = true → z (i - 1) = false) :
    let j : ℕ → ℕ := fun i => if i ≤ 1 then 0 else if z i then 1 else 0
    IsParentArray n j ∧ ∀ i, i ≤ n → trace j i = z i := by
  intro j
  have hpa : IsParentArray n j := by
    intro i hi hin; simp only [j]; split_ifs <;> omega
  refine ⟨hpa, ?_⟩
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hin
    rcases Nat.lt_or_ge i 2 with h | h
    · interval_cases i
      · simp [trace_zero, hz0]
      · rw [trace_step j 1 0 le_rfl (by simp [j]) (by omega), hz1 hin]
        simp [trace_zero, nor]
    · by_cases hzi : z i = true
      · rw [trace_step j i 1 (by omega) (by simp [j, hzi] <;> omega) (by omega),
          ih (i - 1) (by omega) (by omega), ih 1 (by omega) (by omega), hcons i (by omega) hin hzi,
          hz1 (by omega), hzi]
        rfl
      · rw [trace_step j i 0 (by omega) (by simp [j, hzi] <;> omega) (by omega), trace_zero]
        simp only [Bool.not_eq_true] at hzi
        rw [hzi]; simp [nor]

end GC.SeqNORNormalForms
