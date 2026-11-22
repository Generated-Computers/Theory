import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Logic.Function.Iterate

/-!
# Phase repair of reset masks (manuscript 007a, Section 3)

A legal parent array `j` defines the Sequential NOR trace `x₀ = 1`, `xᵢ = NOR(xᵢ₋₁, x_{jᵢ})`.
A reset mask `R` (indexed by `1, …, n`) defines `x_q(R)`: `1` at `q = 0`, `0` at a reset, and
alternating between resets. The map `Φ_j(R)ᵢ = x_{jᵢ}(R)` has the true mask `R⋆ᵢ = x_{jᵢ}` as its
unique fixed point (Lemma 3.2), and the greedy repair map `T_j` removes exactly one phase switch of
the error per round (Theorem 3.6).

Parent arrays are functions `ℕ → ℕ` with `j i < i` for `i ≥ 1`; an instance of length `n` is the
restriction to `1, …, n`, and all statements are made with an explicit horizon `n`.
-/

namespace GC.StructuralCompilers

/-- A legal parent array: `j i < i` for every positive coordinate `i`. -/
structure ParentArray where
  /-- the parent pointers `j₁, j₂, …` (the value at `0` is unused) -/
  j : ℕ → ℕ
  /-- legality: `0 ≤ jᵢ < i` -/
  lt : ∀ i, 1 ≤ i → j i < i

/-- The Sequential NOR trace: `x₀ = 1`, `x_{i} = NOR(x_{i-1}, x_{j_i})`. -/
def ParentArray.x (J : ParentArray) : ℕ → Bool
  | 0 => true
  | i + 1 =>
    have : J.j (i + 1) < i + 1 := J.lt (i + 1) (Nat.succ_pos i)
    !(J.x i || J.x (J.j (i + 1)))

/-- `maskVal R q = x_q(R)`: it is `1` at `q = 0`, `0` at a reset `R q = 1`, and alternates
between resets (Definition 3.1). -/
def maskVal (R : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | q + 1 => if R (q + 1) then false else !(maskVal R q)

/-- `Φ_j(R)ᵢ = x_{jᵢ}(R)`. -/
def phiMap (J : ParentArray) (R : ℕ → Bool) : ℕ → Bool := fun i => maskVal R (J.j i)

/-- The true mask `R⋆ᵢ = x_{jᵢ}`. -/
def trueMask (J : ParentArray) : ℕ → Bool := fun i => J.x (J.j i)

/-- Agreement of two masks on the positions `1, …, n`. -/
def AgreeUpTo (n : ℕ) (Q R : ℕ → Bool) : Prop := ∀ i, 1 ≤ i → i ≤ n → Q i = R i

/-- The defect `dᵢ(Q) = Qᵢ ⊕ Φ_j(Q)ᵢ`. -/
def defect (J : ParentArray) (Q : ℕ → Bool) (i : ℕ) : Bool := xor (Q i) (phiMap J Q i)

/-- The prefix OR `bᵢ(Q) = ⋁_{1 ≤ h ≤ i} d_h(Q)`. -/
def prefixDefect (J : ParentArray) (Q : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | i + 1 => prefixDefect J Q i || defect J Q (i + 1)

/-- One greedy repair round `T_j(Q)ᵢ = Qᵢ ⊕ bᵢ(Q)` (equation (3.1)). -/
def repairStep (J : ParentArray) (Q : ℕ → Bool) : ℕ → Bool :=
  fun i => xor (Q i) (prefixDefect J Q i)

/-- The number of switches `|{i ∈ {2, …, n} : eᵢ ≠ eᵢ₋₁}|` of an error vector. -/
def switchCount (n : ℕ) (e : ℕ → Bool) : ℕ :=
  ((Finset.Icc 2 n).filter (fun i => e i ≠ e (i - 1))).card

/-! ### The unique fixed point (Lemma 3.2) -/

@[simp] lemma ParentArray.x_zero (J : ParentArray) : J.x 0 = true := by
  rw [ParentArray.x]

lemma ParentArray.x_succ (J : ParentArray) (i : ℕ) :
    J.x (i + 1) = !(J.x i || J.x (J.j (i + 1))) := by
  rw [ParentArray.x]

lemma prefixDefect_iff (J : ParentArray) (Q : ℕ → Bool) (i : ℕ) :
    prefixDefect J Q i = true ↔ ∃ h, 1 ≤ h ∧ h ≤ i ∧ defect J Q h = true := by
  induction i with
  | zero => simp [prefixDefect]
  | succ i ih =>
    simp only [prefixDefect, Bool.or_eq_true, ih]
    constructor
    · rintro (⟨h, h1, h2, h3⟩ | h)
      · exact ⟨h, h1, by omega, h3⟩
      · exact ⟨i + 1, by omega, le_rfl, h⟩
    · rintro ⟨h, h1, h2, h3⟩
      rcases Nat.lt_or_ge h (i + 1) with hlt | hge
      · exact Or.inl ⟨h, h1, by omega, h3⟩
      · right; rwa [show h = i + 1 by omega] at h3

lemma maskVal_congr {R R' : ℕ → Bool} {q : ℕ} (h : ∀ i, 1 ≤ i → i ≤ q → R i = R' i) :
    maskVal R q = maskVal R' q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    simp only [maskVal]
    rw [h (q + 1) (by omega) le_rfl, ih (fun i h1 h2 => h i h1 (by omega))]

lemma maskVal_trueMask (J : ParentArray) (q : ℕ) : maskVal (trueMask J) q = J.x q := by
  induction q with
  | zero => simp [maskVal]
  | succ q ih =>
    simp only [maskVal, trueMask, ih]
    rw [ParentArray.x_succ]
    cases J.x (J.j (q + 1)) <;> simp

/-- **Lemma 3.2 (existence).** `R⋆` is a fixed point of `Φ_j`, and `x_q(R⋆) = x_q`. -/
theorem trueMask_fixed (J : ParentArray) :
    phiMap J (trueMask J) = trueMask J ∧ ∀ q, maskVal (trueMask J) q = J.x q := by
  refine ⟨?_, maskVal_trueMask J⟩
  funext i
  simp [phiMap, maskVal_trueMask, trueMask]

/-- **Lemma 3.2 (uniqueness).** A mask that is a fixed point of `Φ_j` on `1, …, n` agrees with
`R⋆` on `1, …, n`. -/
theorem fixedPoint_unique (J : ParentArray) (n : ℕ) (R : ℕ → Bool)
    (hR : AgreeUpTo n (phiMap J R) R) : AgreeUpTo n R (trueMask J) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro h1 hn
    rw [← hR i h1 hn]
    have hlt := J.lt i h1
    have : phiMap J R i = phiMap J (trueMask J) i := by
      simp only [phiMap]
      exact maskVal_congr (fun h hh1 hh2 => ih h (by omega) hh1 (by omega))
    rw [this, (trueMask_fixed J).1]

/-! ### Greedy phase repair (Theorem 3.6) -/

lemma trueMask_one (J : ParentArray) : trueMask J 1 = true := by
  have := J.lt 1 le_rfl
  simp only [trueMask]
  rw [show J.j 1 = 0 by omega]
  simp

/-- The error of `Q` relative to `R⋆`. -/
def errVec (J : ParentArray) (Q : ℕ → Bool) : ℕ → Bool := fun i => xor (Q i) (trueMask J i)

/-- An error with first bit `0` and no switch on `1, …, n` vanishes there. -/
lemma agree_of_switch_zero (J : ParentArray) (n : ℕ) (Q : ℕ → Bool)
    (h1 : Q 1 = trueMask J 1) (h0 : switchCount n (errVec J Q) = 0) :
    AgreeUpTo n Q (trueMask J) := by
  have hall : ∀ i, 2 ≤ i → i ≤ n → errVec J Q i = errVec J Q (i - 1) := by
    intro i h2 hn
    by_contra hne
    have : i ∈ (Finset.Icc 2 n).filter (fun i => errVec J Q i ≠ errVec J Q (i - 1)) := by
      simp [Finset.mem_filter, Finset.mem_Icc, h2, hn, hne]
    rw [switchCount, Finset.card_eq_zero] at h0
    rw [h0] at this
    simp at this
  have hz : ∀ i, 1 ≤ i → i ≤ n → errVec J Q i = false := by
    intro i
    induction i with
    | zero => intro h; omega
    | succ i ih =>
      intro _ hn
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · simp [errVec, h1]
      · rw [hall (i + 1) (by omega) hn]
        exact ih hi (by omega)
  intro i h1' hn
  have := hz i h1' hn
  simp only [errVec] at this
  revert this
  cases Q i <;> cases trueMask J i <;> simp

/-- The key round lemma: if the error has first bit `0` and is nonzero on `1, …, n`, one round
of `T_j` removes exactly the first switch and keeps the first bit `0`. -/
lemma repairStep_switch (J : ParentArray) (n : ℕ) (Q : ℕ → Bool)
    (h1 : Q 1 = trueMask J 1) (hne : ¬ AgreeUpTo n Q (trueMask J)) :
    repairStep J Q 1 = trueMask J 1 ∧
      switchCount n (errVec J (repairStep J Q)) + 1 = switchCount n (errVec J Q) := by
  classical
  -- the least disagreement
  have hex : ∃ s, 1 ≤ s ∧ s ≤ n ∧ Q s ≠ trueMask J s := by
    by_contra h
    push Not at h
    exact hne h
  obtain ⟨s, hs, hmin⟩ : ∃ s, (1 ≤ s ∧ s ≤ n ∧ Q s ≠ trueMask J s) ∧
      ∀ i, 1 ≤ i → i < s → Q i = trueMask J i := by
    refine ⟨Nat.find hex, Nat.find_spec hex, fun i hi1 his => ?_⟩
    have := Nat.find_min hex his
    push Not at this
    exact this hi1 (by have := (Nat.find_spec hex).2.1; omega)
  have hs2 : 2 ≤ s := by
    by_contra h
    have : s = 1 := by omega
    exact hs.2.2 (this ▸ h1)
  have hes : errVec J Q s = true := by
    have := hs.2.2
    simp only [errVec]
    revert this
    cases Q s <;> cases trueMask J s <;> simp
  have hes' : errVec J Q (s - 1) = false := by
    simp only [errVec, hmin (s - 1) (by omega) (by omega)]
    cases trueMask J (s - 1) <;> simp
  -- Φ_j(Q) agrees with R⋆ up to s
  have hphi : ∀ i, 1 ≤ i → i ≤ s → phiMap J Q i = trueMask J i := by
    intro i hi1 his
    have hlt := J.lt i hi1
    have : phiMap J Q i = phiMap J (trueMask J) i := by
      simp only [phiMap]
      exact maskVal_congr (fun h hh1 hh2 => hmin h hh1 (by omega))
    rw [this, (trueMask_fixed J).1]
  have hdef : ∀ i, 1 ≤ i → i ≤ s → (defect J Q i = true ↔ i = s) := by
    intro i hi1 his
    simp only [defect, hphi i hi1 his]
    constructor
    · intro h
      by_contra hne'
      have := hmin i hi1 (by omega)
      rw [this] at h
      simp at h
    · intro h
      rw [h]
      have := hs.2.2
      revert this
      cases Q s <;> cases trueMask J s <;> simp
  have hpre : ∀ i, (prefixDefect J Q i = true ↔ s ≤ i) := by
    intro i
    rw [prefixDefect_iff]
    constructor
    · rintro ⟨h, hh1, hhi, hd⟩
      by_contra hlt
      have := (hdef h hh1 (by omega)).1 hd
      omega
    · intro hsi
      exact ⟨s, hs.1, hsi, (hdef s hs.1 le_rfl).2 rfl⟩
  have hnew : ∀ i,
      errVec J (repairStep J Q) i = xor (errVec J Q i) (decide (s ≤ i)) := by
    intro i
    have hpd : prefixDefect J Q i = decide (s ≤ i) := by
      rw [Bool.eq_iff_iff, hpre i, decide_eq_true_iff]
    simp only [errVec, repairStep, hpd]
    generalize Q i = a
    generalize trueMask J i = b
    generalize decide (s ≤ i) = c
    cases a <;> cases b <;> cases c <;> rfl
  refine ⟨?_, ?_⟩
  · have := hnew 1
    have h1' : errVec J Q 1 = false := by simp [errVec, h1]
    have hd : decide (s ≤ 1) = false := by simp; omega
    rw [h1', hd] at this
    simp only [errVec] at this
    revert this
    cases repairStep J Q 1 <;> cases trueMask J 1 <;> simp
  · -- the new switch set is the old one minus `s`
    have hset : (Finset.Icc 2 n).filter
          (fun i => errVec J (repairStep J Q) i ≠ errVec J (repairStep J Q) (i - 1)) =
        ((Finset.Icc 2 n).filter (fun i => errVec J Q i ≠ errVec J Q (i - 1))).erase s := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_erase, hnew]
      rcases lt_trichotomy i s with h | h | h
      · have ha : ¬ s ≤ i := by omega
        have hb : ¬ s ≤ i - 1 := by omega
        simp only [ha, hb, decide_false, Bool.xor_false]
        constructor
        · rintro ⟨hh, hsw⟩; exact ⟨by omega, hh, hsw⟩
        · rintro ⟨_, hh, hsw⟩; exact ⟨hh, hsw⟩
      · rw [h, hes, hes']
        have hb : ¬ s ≤ s - 1 := by omega
        simp [hb]
      · have ha : s ≤ i := by omega
        have hb : s ≤ i - 1 := by omega
        simp only [ha, hb, decide_true]
        constructor
        · rintro ⟨hh, hsw⟩
          refine ⟨by omega, hh, ?_⟩
          intro heq; apply hsw; rw [heq]
        · rintro ⟨_, hh, hsw⟩
          refine ⟨hh, ?_⟩
          intro heq; apply hsw
          revert heq
          cases errVec J Q i <;> cases errVec J Q (i - 1) <;> simp
    have hmem : s ∈ (Finset.Icc 2 n).filter (fun i => errVec J Q i ≠ errVec J Q (i - 1)) := by
      simp only [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨hs2, hs.2.1⟩, ?_⟩
      rw [hes, hes']
      simp
    rw [switchCount, switchCount, hset, Finset.card_erase_of_mem hmem]
    have := Finset.card_pos.2 ⟨s, hmem⟩
    omega

/-- Iterating the repair map: a mask with first bit correct and `k` switches is repaired after
exactly `k` rounds. -/
lemma repair_iterate (J : ParentArray) (n : ℕ) :
    ∀ k (Q : ℕ → Bool), Q 1 = trueMask J 1 → switchCount n (errVec J Q) = k →
      AgreeUpTo n ((repairStep J)^[k] Q) (trueMask J) ∧
        ∀ t < k, ¬ AgreeUpTo n ((repairStep J)^[t] Q) (trueMask J) := by
  intro k
  induction k with
  | zero =>
    intro Q h1 h0
    exact ⟨agree_of_switch_zero J n Q h1 h0, fun t ht => absurd ht (Nat.not_lt_zero _)⟩
  | succ k ih =>
    intro Q h1 hk
    have hne : ¬ AgreeUpTo n Q (trueMask J) := by
      intro hag
      -- an error that vanishes on `1..n` has no switch
      have : switchCount n (errVec J Q) = 0 := by
        rw [switchCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro i hi
        simp only [Finset.mem_Icc] at hi
        simp [errVec, hag i (by omega) hi.2, hag (i - 1) (by omega) (by omega)]
      omega
    obtain ⟨h1', hsw⟩ := repairStep_switch J n Q h1 hne
    obtain ⟨hgood, hbad⟩ := ih (repairStep J Q) h1' (by omega)
    refine ⟨by rw [Function.iterate_succ_apply]; exact hgood, ?_⟩
    intro t ht
    rcases t with _ | t
    · simpa using hne
    · rw [Function.iterate_succ_apply]
      exact hbad t (by omega)

/-- **Theorem 3.6 (greedy phase repair).** Let `Q⁽⁰⁾ = P` if `P₁ = 1` and `Q⁽⁰⁾ = ¬P` otherwise.
If the error `P ⊕ R⋆` has `k` switches on `1, …, n`, then `Q⁽ᵏ⁾ = T_j^k(Q⁽⁰⁾)` equals `R⋆` on
`1, …, n`, and `Q⁽ᵗ⁾` differs from `R⋆` on `1, …, n` for every `t < k`. -/
theorem greedy_phase_repair (J : ParentArray) (n : ℕ) (P : ℕ → Bool) :
    AgreeUpTo n ((repairStep J)^[switchCount n (fun i => xor (P i) (trueMask J i))]
        (if P 1 then P else fun i => !P i)) (trueMask J) ∧
      ∀ t < switchCount n (fun i => xor (P i) (trueMask J i)),
        ¬ AgreeUpTo n ((repairStep J)^[t] (if P 1 then P else fun i => !P i)) (trueMask J) := by
  set Q0 : ℕ → Bool := if P 1 then P else fun i => !P i with hQ0
  have h1 : Q0 1 = trueMask J 1 := by
    rw [trueMask_one, hQ0]
    by_cases hp : P 1 <;> simp [hp]
  have hsw : switchCount n (errVec J Q0) =
      switchCount n (fun i => xor (P i) (trueMask J i)) := by
    rw [hQ0]
    by_cases hp : P 1
    · simp only [hp, ite_true]; rfl
    · simp only [hp, switchCount, errVec]
      congr 1
      apply Finset.filter_congr
      intro i _
      simp only [Bool.false_eq_true, ite_false]
      generalize P i = a
      generalize P (i - 1) = b
      generalize trueMask J i = c
      generalize trueMask J (i - 1) = d
      cases a <;> cases b <;> cases c <;> cases d <;> simp
  exact repair_iterate J n _ Q0 h1 hsw

end GC.StructuralCompilers
