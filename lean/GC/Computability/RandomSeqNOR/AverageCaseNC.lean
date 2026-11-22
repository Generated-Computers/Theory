import GC.Computability.RandomSeqNOR.Newton
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# A P-complete problem in average-case NC (manuscript 001a): deterministic results

* Proposition 3.1 (Newton–Strahler bound): `newton_strahler`, `exactRounds_le_strahler`.
* Lemma 5.2 (i) (pathwise witnesses): `source_witness`.
* Proposition 8.1 (Newton's worst case is exactly `⌊(n-1)/2⌋`): `worst_case_upper`,
  `worstInst_front`, `exactRounds_worstInst`, `newton_worst_case`.
* Corollary 8.5 (greedy MIS): `lexFirstMIS_eq_ones`.
* Theorem 8.3, final algebraic step (golden-ratio density): `golden_density_fixed_point`.
-/

namespace GC.RandomSeqNOR

/-! ### Horton–Strahler rank and Proposition 3.1 -/

/-- The Horton–Strahler rank: `ρ(0) = 0`, `ρ(i) = ρ(i-1)` at a NOT gate, and at a binary gate
with parent ranks `r₁ ≥ r₂`, `ρ(i) = r₁` if `r₁ > r₂` and `r₁ + 1` if `r₁ = r₂`. -/
def strahler (P : Inst) : ℕ → ℕ
  | 0 => 0
  | i + 1 =>
    if P.j (i + 1) = i then strahler P i
    else if strahler P i = strahler P (P.j (i + 1)) then strahler P i + 1
    else max (strahler P i) (strahler P (P.j (i + 1)))
termination_by i => i
decreasing_by
  all_goals first
    | omega
    | exact P.j_lt (i + 1) (Nat.succ_pos i)

theorem strahler_succ (P : Inst) (i : ℕ) :
    strahler P (i + 1) =
      if P.j (i + 1) = i then strahler P i
      else if strahler P i = strahler P (P.j (i + 1)) then strahler P i + 1
      else max (strahler P i) (strahler P (P.j (i + 1))) := by
  rw [strahler]

theorem strahler_pred_le (P : Inst) (i : ℕ) : strahler P i ≤ strahler P (i + 1) := by
  rw [strahler_succ]; split_ifs <;> omega

theorem strahler_ptr_le (P : Inst) (i : ℕ) :
    strahler P (P.j (i + 1)) ≤ strahler P (i + 1) := by
  rw [strahler_succ]; split_ifs with h1 h2
  · rw [h1]
  · omega
  · omega

theorem strahler_mono (P : Inst) : Monotone (strahler P) :=
  monotone_nat_of_le_succ (strahler_pred_le P)

/-- **Proposition 3.1 (Newton–Strahler bound).** For any start, after `t` Newton rounds every gate
`i` with `ρ(i) < t` is exact. -/
theorem newton_strahler (P : Inst) (x0 : ℕ → ZMod 2) :
    ∀ t i, strahler P i < t → newtonIter P x0 t i = trace P i := by
  intro t
  induction t with
  | zero => intro i h; omega
  | succ t iht =>
    -- every gate of rank `≤ t` is exact after `t + 1` rounds
    have key : ∀ i, strahler P i ≤ t → err P (newtonIter P x0 (t + 1)) i = 0 := by
      intro i
      induction i using Nat.strong_induction_on with
      | _ i ih =>
        intro hi
        rw [newtonIter_succ]
        rw [newtonIter_succ] at ih
        cases i with
        | zero => exact err_newton_zero P _
        | succ i =>
          have hlt := P.j_lt (i + 1) (Nat.succ_pos i)
          have hp1 := strahler_pred_le P i
          have hp2 := strahler_ptr_le P i
          by_cases h : IsNot P (i + 1)
          · rw [err_newton_of_isNot P _ i h]
            exact ih i (by omega) (by omega)
          · rw [err_newton_of_not_isNot P _ i h, ih i (by omega) (by omega),
              ih _ hlt (by omega)]
            have hsrc : err P (newtonIter P x0 t) i * err P (newtonIter P x0 t) (P.j (i + 1))
                = 0 := by
              have hne : ¬ P.j (i + 1) = i := fun h' => h ((isNot_succ_iff P i).2 h')
              have hrank : strahler P i < t ∨ strahler P (P.j (i + 1)) < t := by
                by_contra hc
                push Not at hc
                rw [strahler_succ] at hi
                simp only [hne, ↓reduceIte] at hi
                split_ifs at hi with h3 <;> omega
              rcases hrank with hr | hr
              · rw [(err_eq_zero_iff _ _ _).2 (iht i hr)]; ring
              · rw [(err_eq_zero_iff _ _ _).2 (iht _ hr)]; ring
            rw [hsrc]; ring
    intro i hi
    exact (err_eq_zero_iff _ _ _).1 (key i (by omega))

/-- **Proposition 3.1, consequence:** `T_n ≤ ρ(n) + 1`, for every start. -/
theorem exactRounds_le_strahler (P : Inst) (x0 : ℕ → ZMod 2) (n : ℕ) :
    exactRounds P x0 n ≤ strahler P n + 1 :=
  exactRounds_le P x0 n _ fun i hi =>
    newton_strahler P x0 _ i (Nat.lt_succ_of_le (strahler_mono P hi))

/-! ### Lemma 5.2 (i): the pathwise witness property -/

/-- **Lemma 5.2 (i) (pathwise witnesses).** Every source `s` of round `r - 1` satisfies `s ∈ E_r`,
or `s - 1 ∈ E_r`, or `j_s ∈ E_r`. -/
theorem source_witness (P : Inst) (x : ℕ → ZMod 2) {s : ℕ} (hs : IsSource P x s) :
    err P (newton P x) s = 1 ∨ err P (newton P x) (s - 1) = 1 ∨
      err P (newton P x) (P.j s) = 1 := by
  obtain ⟨hpos, hnot, h1, h2⟩ := hs
  obtain ⟨i, rfl⟩ : ∃ i, s = i + 1 := ⟨s - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h1 ⊢
  rw [err_newton_of_not_isNot P x i hnot, h1, h2]
  generalize err P (newton P x) i = a
  generalize err P (newton P x) (P.j (i + 1)) = b
  generalize x i = c
  generalize x (P.j (i + 1)) = d
  revert a b c d; decide

/-! ### Proposition 8.1 (a): the upper bound `⌊(n-1)/2⌋` from the standard start -/

theorem err_stdStart (P : Inst) {k : ℕ} (hk : 0 < k) : err P stdStart k = trace P k := by
  simp [err, stdStart, Nat.pos_iff_ne_zero.1 hk]

theorem err_stdStart_lt_two (P : Inst) : ∀ k < 2, err P stdStart k = 0 := by
  intro k hk
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · simp [err, stdStart, trace_zero]; decide
  · rw [err_stdStart P one_pos, trace_one]

/-- From the standard start, every source of round `0` is at a position `≥ 5`. -/
theorem source_stdStart_ge_five (P : Inst) {k : ℕ} (h : IsSource P stdStart k) : 5 ≤ k := by
  obtain ⟨hpos, hnot, h1, h2⟩ := h
  have hlt := P.j_lt k hpos
  have hne : P.j k + 1 ≠ k := hnot
  have hA : 2 ≤ k - 1 := by
    by_contra hc
    rw [err_stdStart_lt_two P _ (by omega)] at h1; exact absurd h1 (by decide)
  have hB : 2 ≤ P.j k := by
    by_contra hc
    rw [err_stdStart_lt_two P _ (by omega)] at h2; exact absurd h2 (by decide)
  rw [err_stdStart P (by omega)] at h1 h2
  by_contra hc
  -- then `j k = k - 2`, so two adjacent ones
  have hjk : P.j k + 2 = k := by omega
  have := trace_succ_eq_zero_of_eq_one P h2
  rw [show P.j k + 1 = k - 1 by omega, h1] at this
  exact absurd this (by decide)

/-- From the standard start, `f₁ ≥ 5`. -/
theorem front_one_stdStart (P : Inst) : ∀ k < 5, err P (newtonIter P stdStart 1) k = 0 := by
  intro k hk
  rw [newtonIter_succ, newtonIter_zero]
  exact err_newton_eq_zero_of_no_source P _ k fun m hm hs => by
    have := source_stdStart_ge_five P hs; omega

/-- From the standard start, `f_t ≥ 2t + 3` for `t ≥ 1`. -/
theorem front_stdStart (P : Inst) (t : ℕ) (ht : 1 ≤ t) :
    ∀ k < 2 * t + 3, err P (newtonIter P stdStart t) k = 0 := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  intro k hk
  have h1 := front_one_stdStart P
  rw [newtonIter_succ, newtonIter_zero] at h1
  rw [newtonIter_succ']
  exact front_growth_iter P _ 5 h1 s k (by omega)

/-- **Proposition 8.1 (a).** From the standard start, `T_n ≤ ⌊(n-1)/2⌋` for every `n ≥ 3`. -/
theorem worst_case_upper (P : Inst) (n : ℕ) (hn : 3 ≤ n) :
    exactRounds P stdStart n ≤ (n - 1) / 2 :=
  exactRounds_le P stdStart n _ fun i hi =>
    (err_eq_zero_iff _ _ _).1 (front_stdStart P _ (by omega) i (by omega))

/-! ### Proposition 8.1 (b): the instance `W` attaining the bound -/

/-- The pointers of the worst-case family `W`: `(j₁, …, j₅) = (0, 1, 0, 1, 2)`, `jᵢ = 1` for even
`i ≥ 6`, and `jᵢ = i - 2` for odd `i ≥ 7`. (`W_n` is its restriction to `1, …, n`.) -/
def worstPtr (i : ℕ) : ℕ :=
  if i ≤ 1 then 0 else if i = 3 then 0 else if i = 5 then 2
  else if i % 2 = 0 then 1 else i - 2

theorem worstPtr_lt : ∀ i, 0 < i → worstPtr i < i := by
  intro i hi; unfold worstPtr; split_ifs <;> omega

/-- The worst-case instance `W_∞`. -/
def worstInst : Inst := ⟨worstPtr, worstPtr_lt⟩

theorem worstInst_j_even {i : ℕ} (h2 : 2 ≤ i) (he : i % 2 = 0) : worstInst.j i = 1 := by
  show worstPtr i = 1
  unfold worstPtr; split_ifs <;> omega

theorem worstInst_j_odd {i : ℕ} (h7 : 7 ≤ i) (ho : i % 2 = 1) : worstInst.j i = i - 2 := by
  show worstPtr i = i - 2
  unfold worstPtr; split_ifs <;> omega

theorem worstInst_j_five : worstInst.j 5 = 2 := rfl

/-- The trace of `W` alternates: `x*ᵢ = 1` exactly for even `i`. -/
theorem trace_worstInst (i : ℕ) : trace worstInst i = if i % 2 = 0 then 1 else 0 := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    cases i with
    | zero => rw [trace_zero]; rfl
    | succ i =>
      rw [trace_succ, ih i (by omega)]
      by_cases he : (i + 1) % 2 = 0
      · have h2 : 2 ≤ i + 1 := by
          rcases Nat.lt_or_ge i 1 with h | h
          · omega
          · omega
        rw [worstInst_j_even h2 he, trace_one, if_neg (by omega), if_pos he]; decide
      · rw [if_pos (by omega), if_neg he]
        generalize trace worstInst (worstInst.j (i + 1)) = b
        revert b; decide

theorem trace_worstInst_even {i : ℕ} (h : i % 2 = 0) : trace worstInst i = 1 := by
  rw [trace_worstInst, if_pos h]

theorem trace_worstInst_odd {i : ℕ} (h : i % 2 = 1) : trace worstInst i = 0 := by
  rw [trace_worstInst, if_neg (by omega)]

/-- Error of the `t`-th iterate of `W` from the standard start. -/
private abbrev E (t i : ℕ) : ZMod 2 := err worstInst (newtonIter worstInst stdStart t) i

private theorem E_low (t : ℕ) : ∀ k < 2, E t k = 0 := by
  intro k hk
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · exact err_stdStart_lt_two worstInst k hk
  · exact front_stdStart worstInst t ht k (by omega)

private theorem X_one (t : ℕ) : newtonIter worstInst stdStart t 1 = 0 := by
  rw [(err_eq_zero_iff _ _ _).1 (E_low t 1 one_lt_two), trace_one]

/-- Copy rule: at even `i ≥ 2`, `e⁽ᵗ⁺¹⁾ᵢ = e⁽ᵗ⁺¹⁾ᵢ₋₁`. -/
private theorem copy_rule (t i : ℕ) (h2 : 2 ≤ i) (he : i % 2 = 0) :
    E (t + 1) i = E (t + 1) (i - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  simp only [E, newtonIter_succ, Nat.add_sub_cancel]
  have hj := worstInst_j_even h2 he
  by_cases hm : m = 1
  · subst hm
    exact err_newton_of_isNot worstInst _ 1 (by unfold IsNot; rw [hj])
  · have hnot : ¬ IsNot worstInst (m + 1) := by unfold IsNot; rw [hj]; omega
    rw [err_newton_of_not_isNot worstInst _ m hnot, hj, X_one t]
    have h1 := E_low t 1 one_lt_two
    have h1' := E_low (t + 1) 1 one_lt_two
    simp only [E, newtonIter_succ] at h1 h1'
    rw [h1, h1']; ring

/-- Odd rule: for `t ≥ 1` and odd `i ≥ 7`, `e⁽ᵗ⁺¹⁾ᵢ = e⁽ᵗ⁺¹⁾ᵢ₋₂ + e⁽ᵗ⁾ᵢ₋₂`. -/
private theorem odd_rule (t i : ℕ) (ht : 1 ≤ t) (h7 : 7 ≤ i) (ho : i % 2 = 1) :
    E (t + 1) i = E (t + 1) (i - 2) + E t (i - 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  have hj := worstInst_j_odd h7 ho
  have hnot : ¬ IsNot worstInst (m + 1) := by unfold IsNot; rw [hj]; omega
  have hc1 : E (t + 1) m = E (t + 1) (m - 1) := by
    have := copy_rule t m (by omega) (by omega); simpa using this
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  have hc0 : E (s + 1) m = E (s + 1) (m - 1) := by
    have := copy_rule s m (by omega) (by omega); simpa using this
  have hm2 : m + 1 - 2 = m - 1 := by omega
  rw [hm2]
  simp only [E] at hc1 hc0 ⊢
  rw [newtonIter_succ worstInst stdStart (s + 1)] at hc1 ⊢
  rw [err_newton_of_not_isNot worstInst _ m hnot, hj, hm2, hc1, hc0]
  -- values of the iterate at `m - 1` (odd) and `m` (even) in terms of the error
  have hxm : newtonIter worstInst stdStart (s + 1) m
      = err worstInst (newtonIter worstInst stdStart (s + 1)) (m - 1) + 1 := by
    rw [← hc0, err, trace_worstInst_even (by omega)]
    generalize newtonIter worstInst stdStart (s + 1) m = a; revert a; decide
  have hxm1 : newtonIter worstInst stdStart (s + 1) (m - 1)
      = err worstInst (newtonIter worstInst stdStart (s + 1)) (m - 1) := by
    rw [err, trace_worstInst_odd (by omega), add_zero]
  rw [hxm, hxm1]
  generalize err worstInst (newtonIter worstInst stdStart (s + 1)) (m - 1) = e
  generalize err worstInst (newton worstInst (newtonIter worstInst stdStart (s + 1))) (m - 1) = e'
  revert e e'; decide

private theorem E_one_five : E 1 5 = 1 := by
  have hnot : ¬ IsNot worstInst (4 + 1) := by unfold IsNot; rw [worstInst_j_five]; omega
  simp only [E]
  rw [newtonIter_succ, err_newton_of_not_isNot worstInst _ 4 hnot, worstInst_j_five]
  have h4 : err worstInst (newton worstInst (newtonIter worstInst stdStart 0)) 4 = 0 := by
    have := front_one_stdStart worstInst 4 (by omega)
    rwa [newtonIter_succ] at this
  have h2 : err worstInst (newton worstInst (newtonIter worstInst stdStart 0)) 2 = 0 := by
    have := front_one_stdStart worstInst 2 (by omega)
    rwa [newtonIter_succ] at this
  rw [h4, h2, newtonIter_zero, err_stdStart worstInst (by omega),
    err_stdStart worstInst (by omega), trace_worstInst_even (by omega),
    trace_worstInst_even (by omega)]
  ring_nf

/-- **Proposition 8.1 (b), front of `W`.** From the standard start, the front of `W` is exactly
`f_t = 2t + 3` for every `t ≥ 1`. -/
theorem worstInst_front (t : ℕ) (ht : 1 ≤ t) :
    (∀ k < 2 * t + 3, err worstInst (newtonIter worstInst stdStart t) k = 0) ∧
      err worstInst (newtonIter worstInst stdStart t) (2 * t + 3) = 1 := by
  refine ⟨front_stdStart worstInst t ht, ?_⟩
  induction t with
  | zero => omega
  | succ t ih =>
    rcases Nat.eq_zero_or_pos t with rfl | htpos
    · exact E_one_five
    · have := odd_rule t (2 * (t + 1) + 3) htpos (by omega) (by omega)
      simp only [E] at this
      rw [this, show 2 * (t + 1) + 3 - 2 = 2 * t + 3 by omega,
        front_stdStart worstInst (t + 1) (by omega) (2 * t + 3) (by omega), ih htpos]
      ring

/-- **Proposition 8.1 (b).** `T_n(W_n) = ⌊(n-1)/2⌋` from the standard start, for `n ≥ 3`
(the paper states it for `n ≥ 5` and uses an instance with `j₂ = 1`, such as `W`, for
`n ∈ {3, 4}`). -/
theorem exactRounds_worstInst (n : ℕ) (hn : 3 ≤ n) :
    exactRounds worstInst stdStart n = (n - 1) / 2 := by
  apply exactRounds_eq
  · intro i hi
    exact (err_eq_zero_iff _ _ _).1 (front_stdStart worstInst _ (by omega) i (by omega))
  · intro t ht
    -- otherwise the iterate would be exact at round `(n-1)/2 - 1`
    by_contra hc
    push Not at hc
    have hex := newtonIter_exact_mono worstInst stdStart n (t' := (n - 1) / 2 - 1)
      (by omega) hc
    rcases Nat.eq_zero_or_pos ((n - 1) / 2 - 1) with h0 | hpos
    · have := hex 2 (by omega)
      rw [h0, newtonIter_zero, trace_worstInst_even (by omega)] at this
      exact absurd this (by decide)
    · have h1 := (worstInst_front _ hpos).2
      rw [(err_eq_zero_iff _ _ _).2 (hex _ (by omega))] at h1
      exact absurd h1 (by decide)

/-- **Proposition 8.1 (c).** For every `n ≥ 3`, the maximum of `T_n` over all instances, from the
standard start, is exactly `⌊(n-1)/2⌋`. (Instances are infinite pointer sequences; by
`newtonIter_congr` and `trace_congr` only `j₁, …, jₙ` matter.) -/
theorem newton_worst_case (n : ℕ) (hn : 3 ≤ n) :
    (∀ P : Inst, exactRounds P stdStart n ≤ (n - 1) / 2) ∧
      ∃ P : Inst, exactRounds P stdStart n = (n - 1) / 2 :=
  ⟨fun P => worst_case_upper P n hn, worstInst, exactRounds_worstInst n hn⟩

/-! ### Corollary 8.5: the lexicographically first maximal independent set -/

/-- The graph `G` on `ℕ` with edges `{i-1, i}` and `{jᵢ, i}` (a Hamiltonian path plus the
recursive tree of the pointers). -/
def norGraph (P : Inst) : SimpleGraph ℕ :=
  SimpleGraph.fromRel fun a b => a + 1 = b ∨ (0 < b ∧ a = P.j b)

theorem norGraph_adj_of_lt (P : Inst) {k i : ℕ} (hk : k < i) :
    (norGraph P).Adj k i ↔ k + 1 = i ∨ k = P.j i := by
  simp only [norGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, h | h⟩
    · rcases h with h | ⟨_, h⟩
      · exact Or.inl h
      · exact Or.inr h
    · rcases h with h | ⟨hpos, h⟩
      · omega
      · have := P.j_lt k hpos; omega
  · rintro (h | h)
    · exact ⟨by omega, Or.inl (Or.inl h)⟩
    · exact ⟨by omega, Or.inl (Or.inr ⟨by omega, h⟩)⟩

/-- **Corollary 8.5.** A set `S ⊆ ℕ` is the lexicographically first maximal independent set of
`G` in the natural order, i.e. `i ∈ S` iff no earlier neighbour of `i` lies in `S`, if and only if
`S` is the set of ones of the trace. -/
theorem lexFirstMIS_eq_ones (P : Inst) (S : Set ℕ) :
    (∀ i, i ∈ S ↔ ∀ k < i, (norGraph P).Adj k i → k ∉ S) ↔ S = {i | trace P i = 1} := by
  constructor
  · intro hS
    ext i
    simp only [Set.mem_ofPred_eq]
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      rw [hS i]
      cases i with
      | zero =>
        simp only [trace_zero, iff_true]
        intro k hk; omega
      | succ i =>
        have hlt := P.j_lt (i + 1) (Nat.succ_pos i)
        rw [trace_succ]
        have hA : (∀ k < i + 1, (norGraph P).Adj k (i + 1) → k ∉ S) ↔
            (i ∉ S ∧ P.j (i + 1) ∉ S) := by
          constructor
          · intro h
            exact ⟨h i (by omega) ((norGraph_adj_of_lt P (by omega)).2 (Or.inl rfl)),
              h _ hlt ((norGraph_adj_of_lt P hlt).2 (Or.inr rfl))⟩
          · rintro ⟨h1, h2⟩ k hk hadj
            rcases (norGraph_adj_of_lt P hk).1 hadj with h | h
            · rw [show k = i by omega]; exact h1
            · rw [h]; exact h2
        rw [hA, ih i (by omega), ih _ hlt]
        generalize trace P i = a
        generalize trace P (P.j (i + 1)) = b
        revert a b; decide
  · rintro rfl i
    simp only [Set.mem_ofPred_eq]
    cases i with
    | zero => simp only [trace_zero, true_iff]; intro k hk; omega
    | succ i =>
      have hlt := P.j_lt (i + 1) (Nat.succ_pos i)
      rw [trace_succ]
      constructor
      · intro h k hk hadj
        rcases (norGraph_adj_of_lt P hk).1 hadj with h' | h'
        · rw [show k = i by omega]
          intro hk1; rw [hk1] at h; revert h
          generalize trace P (P.j (i + 1)) = b; revert b; decide
        · rw [h']
          intro hk1; rw [hk1] at h; revert h
          generalize trace P i = b; revert b; decide
      · intro h
        have h1 := h i (by omega) ((norGraph_adj_of_lt P (by omega)).2 (Or.inl rfl))
        have h2 := h _ hlt ((norGraph_adj_of_lt P hlt).2 (Or.inr rfl))
        rw [(zmod2_ne_one_iff _).1 h1, (zmod2_ne_one_iff _).1 h2]; decide

/-! ### Theorem 8.3: the algebraic step of the golden-ratio density -/

/-- **Theorem 8.3, final step.** With `g(u) = (1-u)/(2-u)`, if `L = liminf σ_m` and
`U = limsup σ_m` lie in `[0, 1/2]` and satisfy `L ≥ g(U)` and `U ≤ g(L)`, then
`L = U = (3 - √5)/2 = φ⁻²`. -/
theorem golden_density_fixed_point {L U : ℝ} (hLU : L ≤ U) (hU : U ≤ 1 / 2)
    (h1 : (1 - U) / (2 - U) ≤ L) (h2 : U ≤ (1 - L) / (2 - L)) :
    L = U ∧ U = (3 - Real.sqrt 5) / 2 := by
  have hA : 0 < 2 - U := by linarith
  have hB : 0 < 2 - L := by linarith
  rw [div_le_iff₀ hA] at h1
  rw [le_div_iff₀ hB] at h2
  have hLeq : L = U := by
    by_contra hne
    have hlt : L < U := lt_of_le_of_ne hLU hne
    nlinarith [mul_pos (sub_pos.2 hlt) hA, mul_pos hA hB]
  subst hLeq
  refine ⟨rfl, ?_⟩
  have hq : L ^ 2 - 3 * L + 1 = 0 := by nlinarith
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hfac : (L - (3 - Real.sqrt 5) / 2) * (L - (3 + Real.sqrt 5) / 2) = 0 := by
    nlinarith
  rcases mul_eq_zero.1 hfac with h | h
  · linarith
  · nlinarith

end GC.RandomSeqNOR
