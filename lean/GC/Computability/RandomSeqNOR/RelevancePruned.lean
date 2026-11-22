import GC.Computability.RandomSeqNOR.SmallNoise

/-!
# The relevance-pruned iteration (manuscript 001d, Section 3.2; also 001c, Section 3.5)

* Definition 3.3: `kprStep`, `kprIter`; the depth `D`: `relDepth`.
* Lemma 3.4 (a): `kpr_rounds_eq_relDepth`; Lemma 3.4 (b): `relDepth_le_depth`,
  `kp_known_subset_kpr_known`.
* Lemma 3.5 (a), (b) for `D`: `relDepth_one`, `relDepth_succ_*`, `relDepth_switch`.
* Lemma 4.2 for `D`: `zones_relDepth`, `zones_relDepth_of_trace_one`, and the over-approximation
  step of Theorem 4.3 (a): `overapprox_relDepth`.
-/

namespace GC.RandomSeqNOR

/-- Gate `k ≥ 1` is *relevant* if `x*_{k-1} = 0`. -/
def IsRelevant (P : Inst) (k : ℕ) : Prop := 0 < k ∧ trace P (k - 1) = 0

instance (P : Inst) (k : ℕ) : Decidable (IsRelevant P k) := by unfold IsRelevant; infer_instance

/-- `ϱ'(i)`: the largest `r ≤ i` that is `0` or a reset at a relevant gate. -/
def lastRelReset (P : Inst) (i : ℕ) : ℕ :=
  Nat.findGreatest (fun r => r = 0 ∨ (IsReset P r ∧ IsRelevant P r)) i

/-- The anchors of `i`: the resets in `[ϱ'(i), i]`, together with `0` if `ϱ'(i) = 0`. -/
def anchors (P : Inst) (i : ℕ) : Finset ℕ :=
  (Finset.Icc (lastRelReset P i) i).filter (fun r => r = 0 ∨ IsReset P r)

theorem lastRelReset_le (P : Inst) (i : ℕ) : lastRelReset P i ≤ i := Nat.findGreatest_le i

theorem lastRelReset_spec (P : Inst) (i : ℕ) :
    lastRelReset P i = 0 ∨ (IsReset P (lastRelReset P i) ∧ IsRelevant P (lastRelReset P i)) :=
  Nat.findGreatest_spec (P := fun r => r = 0 ∨ (IsReset P r ∧ IsRelevant P r))
    (Nat.zero_le i) (Or.inl rfl)

theorem not_relReset_of_lastRelReset_lt (P : Inst) {i k : ℕ} (hk : lastRelReset P i < k)
    (hki : k ≤ i) : ¬ (IsReset P k ∧ IsRelevant P k) := fun h =>
  Nat.findGreatest_is_greatest (P := fun r => r = 0 ∨ (IsReset P r ∧ IsRelevant P r)) hk hki
    (Or.inr h)

theorem le_lastRelReset (P : Inst) {i k : ℕ} (hki : k ≤ i) (hk : IsReset P k ∧ IsRelevant P k) :
    k ≤ lastRelReset P i :=
  Nat.le_findGreatest (P := fun r => r = 0 ∨ (IsReset P r ∧ IsRelevant P r)) hki (Or.inr hk)

theorem mem_anchors (P : Inst) {i r : ℕ} :
    r ∈ anchors P i ↔ lastRelReset P i ≤ r ∧ r ≤ i ∧ (r = 0 ∨ IsReset P r) := by
  simp only [anchors, Finset.mem_filter, Finset.mem_Icc, and_assoc]

theorem lastRelReset_mem_anchors (P : Inst) (i : ℕ) : lastRelReset P i ∈ anchors P i := by
  rw [mem_anchors]
  refine ⟨le_rfl, lastRelReset_le P i, ?_⟩
  rcases lastRelReset_spec P i with h | h
  · exact Or.inl h
  · exact Or.inr h.1

/-- The relevance-pruned depth: `D(0) = 0` and, for `i ≥ 1`,
`D(i) = 1 + min_r max({D(j_r) : r ≥ 1} ∪ {D(jₖ) : r < k ≤ i, k relevant and not a NOT gate})`,
the minimum over the anchors `r` of `i`, with `max ∅ = 0`. -/
def relDepth (P : Inst) : ℕ → ℕ
  | 0 => 0
  | i + 1 => 1 + (anchors P (i + 1)).attach.inf'
      (show (anchors P (i + 1)).attach.Nonempty from
        ⟨⟨_, lastRelReset_mem_anchors P (i + 1)⟩, Finset.mem_attach _ _⟩)
      (fun r => max (if h : r.1 = 0 then 0 else relDepth P (P.j r.1))
        (((Finset.Ioc r.1 (i + 1)).filter (fun k => IsRelevant P k ∧ ¬ IsNot P k)).attach.sup
          (fun k => relDepth P (P.j k.1))))
termination_by i => i
decreasing_by
  · have hr := r.2
    rw [mem_anchors] at hr
    have := P.j_lt r.1 (by omega)
    omega
  · have hk := k.2
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hk
    have := P.j_lt k.1 (by omega)
    omega

theorem relDepth_zero (P : Inst) : relDepth P 0 = 0 := by rw [relDepth]

theorem lastRelReset_zero (P : Inst) : lastRelReset P 0 = 0 := Nat.findGreatest_zero

/-- The defining property of `D`: `D(i) ≤ t + 1` iff some anchor `r` of `i` has `D(j_r) ≤ t` (if
`r ≥ 1`) and `D(jₖ) ≤ t` for every relevant non-NOT gate `k ∈ (r, i]`. -/
theorem relDepth_le_succ_iff (P : Inst) (i t : ℕ) :
    relDepth P i ≤ t + 1 ↔ ∃ r ∈ anchors P i, (r ≠ 0 → relDepth P (P.j r) ≤ t) ∧
      ∀ k, r < k → k ≤ i → IsRelevant P k → ¬ IsNot P k → relDepth P (P.j k) ≤ t := by
  cases i with
  | zero =>
    rw [relDepth_zero]
    simp only [zero_le, true_iff]
    refine ⟨0, ?_, fun h => absurd rfl h, fun k hk1 hk2 => by omega⟩
    rw [mem_anchors, lastRelReset_zero]; exact ⟨le_rfl, le_rfl, Or.inl rfl⟩
  | succ i =>
    rw [relDepth, add_comm, Nat.add_le_add_iff_right, Finset.inf'_le_iff]
    constructor
    · rintro ⟨⟨r, hr⟩, -, h⟩
      rw [max_le_iff, Finset.sup_le_iff] at h
      refine ⟨r, hr, fun h0 => ?_, fun k hk1 hk2 hk3 hk4 => ?_⟩
      · have := h.1; simp only [h0, ↓reduceDIte] at this; exact this
      · exact h.2 ⟨k, by simp only [Finset.mem_filter, Finset.mem_Ioc]; exact ⟨⟨hk1, hk2⟩, hk3, hk4⟩⟩
          (Finset.mem_attach _ _)
    · rintro ⟨r, hr, h1, h2⟩
      refine ⟨⟨r, hr⟩, Finset.mem_attach _ _, ?_⟩
      rw [max_le_iff, Finset.sup_le_iff]
      refine ⟨?_, ?_⟩
      · by_cases h0 : r = 0
        · simp only [h0, ↓reduceDIte]; exact Nat.zero_le _
        · simp only [h0, ↓reduceDIte]; exact h1 h0
      · rintro ⟨k, hk⟩ -
        simp only [Finset.mem_filter, Finset.mem_Ioc] at hk
        exact h2 k hk.1.1 hk.1.2 hk.2.1 hk.2.2

theorem relDepth_pos (P : Inst) {i : ℕ} (hi : 0 < i) : 0 < relDepth P i := by
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  rw [relDepth]; omega

theorem relDepth_eq_zero_iff (P : Inst) (i : ℕ) : relDepth P i = 0 ↔ i = 0 := by
  constructor
  · intro h; by_contra hi; have := relDepth_pos P (Nat.pos_of_ne_zero hi); omega
  · rintro rfl; exact relDepth_zero P

/-! ### Lemma 3.4 (b): `D ≤ d` -/

theorem lastRelReset_le_lastReset (P : Inst) (i : ℕ) : lastRelReset P i ≤ lastReset P i := by
  unfold lastRelReset lastReset
  exact Nat.findGreatest_mono_left (fun n hn => hn.elim Or.inl (fun h => Or.inr h.1)) i

/-- `D(i) ≤ d(i)`: the relevance-pruned depth never exceeds the Kleene–prefix depth. -/
theorem relDepth_le_depth (P : Inst) (i : ℕ) : relDepth P i ≤ depth P i := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [relDepth_zero]; exact Nat.zero_le _
    · have hd := depth_pos P hi
      have hle := (depth_le_succ_iff P i (depth P i - 1)).1 (by omega)
      have : relDepth P i ≤ (depth P i - 1) + 1 := by
        rw [relDepth_le_succ_iff]
        refine ⟨lastReset P i, ?_, fun h0 => ?_, fun k hk1 hk2 hk3 hk4 => ?_⟩
        · rw [mem_anchors]
          refine ⟨lastRelReset_le_lastReset P i, lastReset_le P i, lastReset_spec P i⟩
        · have hr := (lastReset_spec P i).resolve_left h0
          have hlt := P.j_lt _ hr.1
          have := hle _ (max_le le_rfl hr.1) (lastReset_le P i) hr.2.1
          have := ih (P.j (lastReset P i)) (by have := lastReset_le P i; omega)
          omega
        · have hlt := P.j_lt k hk3.1
          have := hle k (max_le hk1.le hk3.1) hk2 hk4
          have := ih (P.j k) (by omega)
          omega
      omega

/-! ### Definition 3.3 and Lemma 3.4 (a) -/

/-- One round of the relevance-pruned iteration: with `rᵢ` as in the Kleene–prefix iteration and
`a_p = v_{rᵢ} ⊕ ((p - rᵢ) mod 2)`, `i ∈ K_{t+1}` iff every gate `k ∈ (rᵢ, i]` with `a_{k-1} = 0` is
resolved, and then `vᵢ = aᵢ`. -/
noncomputable def kprStep (P : Inst) (S : KPState) : KPState where
  known := {i | ∀ k, kpAnchor P S i < k → k ≤ i →
    (if kpAnchor P S i = 0 then 1 else 0) + ((k - 1 - kpAnchor P S i : ℕ) : ZMod 2) = 0 →
      KPResolved P S k}
  val i := (if kpAnchor P S i = 0 then 1 else 0) + ((i - kpAnchor P S i : ℕ) : ZMod 2)

/-- The state of the relevance-pruned iteration after `t` rounds. -/
noncomputable def kprIter (P : Inst) (t : ℕ) : KPState := (kprStep P)^[t] kpStart

theorem kprIter_succ (P : Inst) (t : ℕ) : kprIter P (t + 1) = kprStep P (kprIter P t) := by
  unfold kprIter; rw [Function.iterate_succ_apply']

private theorem cast_succ_sub {p r : ℕ} (h : r ≤ p) :
    ((p + 1 - r : ℕ) : ZMod 2) = ((p - r : ℕ) : ZMod 2) + 1 := by
  rw [Nat.succ_sub h]; push_cast; ring

/-- On an interval with no reset at a relevant gate, the trace alternates. -/
theorem trace_alternates (P : Inst) {r i : ℕ} (hri : r ≤ i)
    (h : ∀ k, r < k → k ≤ i → ¬ (IsReset P k ∧ IsRelevant P k)) :
    trace P i = trace P r + ((i - r : ℕ) : ZMod 2) := by
  induction i, hri using Nat.le_induction with
  | base => simp
  | succ i hri ih =>
    have ih' := ih (fun k hk hki => h k hk (by omega))
    rw [cast_succ_sub hri]
    by_cases hrel : trace P i = 0
    · have hnr : ¬ IsReset P (i + 1) := fun hr =>
        h (i + 1) (by omega) le_rfl ⟨hr, Nat.succ_pos i, by simpa using hrel⟩
      rw [trace_succ_of_not_isReset P i hnr, ih']; ring
    · have h1 : trace P i = 1 := by
        rcases zmod2_cases (trace P i) with h' | h'
        · exact absurd h' hrel
        · exact h'
      rw [trace_succ_eq_zero_of_eq_one P h1]
      rw [h1] at ih'
      rw [← add_assoc, ← ih']; decide

/-- **Lemma 3.4 (a).** For every `t ≥ 0`, the relevance-pruned iteration has
`K_t = {i : D(i) ≤ t}`, and `vᵢ = x*ᵢ` for every `i ∈ K_t`. -/
theorem kpr_rounds_eq_relDepth (P : Inst) (t : ℕ) :
    (kprIter P t).known = {i | relDepth P i ≤ t} ∧
      ∀ i ∈ (kprIter P t).known, (kprIter P t).val i = trace P i := by
  induction t with
  | zero =>
    refine ⟨?_, ?_⟩
    · ext i
      simp only [kprIter, Function.iterate_zero, id, kpStart, Set.mem_singleton_iff,
        Set.mem_ofPred_eq, Nat.le_zero, relDepth_eq_zero_iff]
    · intro i hi
      simp only [kprIter, Function.iterate_zero, id, kpStart, Set.mem_singleton_iff] at hi
      subst hi; rw [trace_zero]; rfl
  | succ t ih =>
    obtain ⟨hK, hV⟩ := ih
    set S := kprIter P t with hS
    rw [kprIter_succ]
    have hres : ∀ k, KPResolved P S k ↔ IsNot P k ∨ relDepth P (P.j k) ≤ t := by
      intro k; simp only [KPResolved, hK, Set.mem_ofPred_eq]
    have hrr : ∀ k, KPResolvedReset P S k → IsReset P k := by
      rintro k ⟨h0, h1, h2, h3⟩
      exact ⟨h0, h1, (hV _ h2) ▸ h3⟩
    have hrr' : ∀ k, IsReset P k → P.j k ∈ S.known → KPResolvedReset P S k := by
      rintro k ⟨h0, h1, h2⟩ hk
      exact ⟨h0, h1, hk, (hV _ hk).trans h2⟩
    have hanchor_le : ∀ i, kpAnchor P S i ≤ lastReset P i := by
      intro i
      classical
      unfold kpAnchor lastReset
      exact Nat.findGreatest_mono_left (fun n hn => hn.elim Or.inl (fun h => Or.inr (hrr n h))) i
    have hanchor_spec : ∀ i, kpAnchor P S i = 0 ∨ KPResolvedReset P S (kpAnchor P S i) := by
      intro i; classical
      exact Nat.findGreatest_spec (P := fun r => r = 0 ∨ KPResolvedReset P S r)
        (Nat.zero_le i) (Or.inl rfl)
    have hanchor_great : ∀ i k, kpAnchor P S i < k → k ≤ i → ¬ KPResolvedReset P S k := by
      intro i k hk hki h; classical
      exact Nat.findGreatest_is_greatest (P := fun r => r = 0 ∨ KPResolvedReset P S r)
        hk hki (Or.inr h)
    have hanchor_ge : ∀ i k, k ≤ i → KPResolvedReset P S k → k ≤ kpAnchor P S i := by
      intro i k hki h; classical
      exact Nat.le_findGreatest (P := fun r => r = 0 ∨ KPResolvedReset P S r) hki (Or.inr h)
    have hanchor_i : ∀ i, kpAnchor P S i ≤ i := fun i =>
      le_trans (hanchor_le i) (lastReset_le P i)
    -- the value at the anchor is correct
    have htr_anchor : ∀ i, trace P (kpAnchor P S i) = if kpAnchor P S i = 0 then 1 else 0 := by
      intro i
      rcases hanchor_spec i with h0 | h0
      · rw [if_pos h0, h0, trace_zero]
      · rw [if_neg (fun h' => h0.1.ne' h'), trace_of_isReset P (hrr _ h0)]
    -- the prediction `a_p`
    set a : ℕ → ℕ → ZMod 2 := fun i p =>
      (if kpAnchor P S i = 0 then 1 else 0) + ((p - kpAnchor P S i : ℕ) : ZMod 2) with ha
    have ha_succ : ∀ i p, kpAnchor P S i ≤ p → a i (p + 1) = a i p + 1 := by
      intro i p hp; simp only [ha]; rw [cast_succ_sub hp]; ring
    -- values: on `[rᵢ, i]` the trace equals the prediction, for `i ∈ K_{t+1}`
    have hvalues : ∀ i, i ∈ (kprStep P S).known →
        ∀ p, kpAnchor P S i ≤ p → p ≤ i → trace P p = a i p := by
      intro i hi p hp1 hp2
      have hi' : ∀ k, kpAnchor P S i < k → k ≤ i → a i (k - 1) = 0 → KPResolved P S k := by
        intro k hk1 hk2 hk3
        exact hi k hk1 hk2 (by simpa [ha] using hk3)
      induction p, hp1 using Nat.le_induction with
      | base => simp only [ha, Nat.sub_self, Nat.cast_zero, add_zero]; exact htr_anchor i
      | succ p hp ihp =>
        have ihp := ihp (by omega)
        rw [ha_succ i p hp]
        rcases zmod2_cases (a i p) with h0 | h1
        · -- gate `p + 1` is resolved
          have hres' := hi' (p + 1) (by omega) hp2 (by simpa using h0)
          rw [h0]
          by_cases hn : IsNot P (p + 1)
          · rw [trace_succ_of_isNot P p hn, ihp, h0]; ring
          · have hj := hres'.resolve_left hn
            have htj : trace P (P.j (p + 1)) = 0 := by
              rcases zmod2_cases (trace P (P.j (p + 1))) with h' | h'
              · exact h'
              · exact absurd (hrr' (p + 1) ⟨Nat.succ_pos p, hn, h'⟩ hj)
                  (hanchor_great i (p + 1) (by omega) hp2)
            rw [trace_succ, ihp, h0, htj]; ring
        · rw [trace_succ_eq_zero_of_eq_one P (ihp.trans h1), h1]; decide
    have hknown : ∀ i, i ∈ (kprStep P S).known ↔ relDepth P i ≤ t + 1 := by
      intro i
      constructor
      · intro hi
        have hval := hvalues i hi
        have hi' : ∀ k, kpAnchor P S i < k → k ≤ i → a i (k - 1) = 0 → KPResolved P S k := by
          intro k hk1 hk2 hk3
          exact hi k hk1 hk2 (by simpa [ha] using hk3)
        -- relevant gates after `rᵢ` are resolved
        have hrelres : ∀ k, kpAnchor P S i < k → k ≤ i → IsRelevant P k → KPResolved P S k := by
          intro k hk1 hk2 hk3
          apply hi' k hk1 hk2
          rw [← hval (k - 1) (by omega) (by omega)]; exact hk3.2
        -- no reset at a relevant gate after `rᵢ`
        have hnorel : ∀ k, kpAnchor P S i < k → k ≤ i → ¬ (IsReset P k ∧ IsRelevant P k) := by
          rintro k hk1 hk2 ⟨hr, hrel⟩
          exact hanchor_great i k hk1 hk2
            (hrr' k hr ((hrelres k hk1 hk2 hrel).resolve_left hr.2.1))
        have hρ : lastRelReset P i ≤ kpAnchor P S i := by
          by_contra hc; push Not at hc
          rcases lastRelReset_spec P i with h0 | h0
          · omega
          · exact hnorel _ hc (lastRelReset_le P i) h0
        rw [relDepth_le_succ_iff]
        refine ⟨kpAnchor P S i, ?_, fun h0 => ?_, fun k hk1 hk2 hk3 hk4 => ?_⟩
        · rw [mem_anchors]
          refine ⟨hρ, hanchor_i i, ?_⟩
          rcases hanchor_spec i with h0 | h0
          · exact Or.inl h0
          · exact Or.inr (hrr _ h0)
        · have := ((hanchor_spec i).resolve_left h0).2.2.1
          rw [hK] at this; exact this
        · exact ((hres k).1 (hrelres k hk1 hk2 hk3)).resolve_left hk4
      · intro hD
        rw [relDepth_le_succ_iff] at hD
        obtain ⟨r0, hr0, h1, h2⟩ := hD
        rw [mem_anchors] at hr0
        obtain ⟨hr01, hr02, hr03⟩ := hr0
        -- `r0 ≤ rᵢ`
        have hr0le : r0 ≤ kpAnchor P S i := by
          rcases hr03 with h0 | h0
          · omega
          · apply hanchor_ge i r0 hr02
            apply hrr' r0 h0
            rw [hK]; exact h1 h0.1.ne'
        have hnorel : ∀ k, kpAnchor P S i < k → k ≤ i → ¬ (IsReset P k ∧ IsRelevant P k) :=
          fun k hk1 hk2 => not_relReset_of_lastRelReset_lt P (by omega) hk2
        have halt : ∀ p, kpAnchor P S i ≤ p → p ≤ i → trace P p = a i p := by
          intro p hp1 hp2
          rw [trace_alternates P hp1 (fun k hk1 hk2 => hnorel k hk1 (by omega)), htr_anchor]
        intro k hk1 hk2 hk3
        rw [hres]
        by_cases hn : IsNot P k
        · exact Or.inl hn
        · right
          apply h2 k (by omega) hk2 _ hn
          refine ⟨by omega, ?_⟩
          rw [halt (k - 1) (by omega) (by omega)]
          simpa [ha] using hk3
    refine ⟨Set.ext hknown, fun i hi => ?_⟩
    show a i i = trace P i
    exact (hvalues i hi i (hanchor_i i) le_rfl).symm

/-- **Lemma 3.4 (b).** After every round, every position known to the Kleene–prefix iteration is
known to the relevance-pruned iteration. -/
theorem kp_known_subset_kpr_known (P : Inst) (t : ℕ) :
    (kpIter P t).known ⊆ (kprIter P t).known := by
  rw [(kp_rounds_eq_depth P t).1, (kpr_rounds_eq_relDepth P t).1]
  intro i hi
  exact le_trans (relDepth_le_depth P i) hi

/-! ### Lemma 3.5 (a) for `D` -/

private theorem eq_of_le_succ_iff' {x y : ℕ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (h : ∀ t, x ≤ t + 1 ↔ y ≤ t + 1) : x = y := by
  apply le_antisymm
  · have := (h (y - 1)).2 (by omega); omega
  · have := (h (x - 1)).1 (by omega); omega

theorem lastRelReset_succ_of_relReset (P : Inst) {i : ℕ}
    (h : IsReset P (i + 1) ∧ IsRelevant P (i + 1)) : lastRelReset P (i + 1) = i + 1 :=
  Nat.findGreatest_eq (P := fun r => r = 0 ∨ (IsReset P r ∧ IsRelevant P r)) (Or.inr h)

theorem lastRelReset_succ_of_not_relReset (P : Inst) {i : ℕ}
    (h : ¬ (IsReset P (i + 1) ∧ IsRelevant P (i + 1))) :
    lastRelReset P (i + 1) = lastRelReset P i :=
  Nat.findGreatest_of_not (P := fun r => r = 0 ∨ (IsReset P r ∧ IsRelevant P r)) (by simp [h])

/-- After a reset the next gate is relevant. -/
theorem isRelevant_succ_of_isReset (P : Inst) {u : ℕ} (h : IsReset P u) :
    IsRelevant P (u + 1) :=
  ⟨Nat.succ_pos u, by simpa using trace_of_isReset P h⟩

/-- Of two consecutive gates `g, g + 1` (with `g ≥ 1`), one is relevant. -/
theorem isRelevant_or_succ (P : Inst) {g : ℕ} (hg : 1 ≤ g) :
    IsRelevant P g ∨ IsRelevant P (g + 1) := by
  by_cases h : trace P (g - 1) = 0
  · exact Or.inl ⟨by omega, h⟩
  · right
    have h1 : trace P (g - 1) = 1 := by
      rcases zmod2_cases (trace P (g - 1)) with h' | h'
      · exact absurd h' h
      · exact h'
    have := trace_succ_eq_zero_of_eq_one P h1
    rw [show g - 1 + 1 = g by omega] at this
    exact ⟨Nat.succ_pos g, by simpa using this⟩

/-- A gate `k` with `x*_k = 1` is relevant (for `k ≥ 1`). -/
theorem isRelevant_of_trace_one (P : Inst) {k : ℕ} (hk : 1 ≤ k) (h : trace P k = 1) :
    IsRelevant P k := by
  refine ⟨by omega, ?_⟩
  by_contra hc
  have h1 : trace P (k - 1) = 1 := by
    rcases zmod2_cases (trace P (k - 1)) with h' | h'
    · exact absurd h' hc
    · exact h'
  have := trace_succ_eq_zero_of_eq_one P h1
  rw [show k - 1 + 1 = k by omega, h] at this
  exact absurd this (by decide)

/-- The condition of an anchor `r` in the definition of `D(i) ≤ t + 1`. -/
private def AnchorCond (P : Inst) (r i t : ℕ) : Prop :=
  (r ≠ 0 → relDepth P (P.j r) ≤ t) ∧
    ∀ k, r < k → k ≤ i → IsRelevant P k → ¬ IsNot P k → relDepth P (P.j k) ≤ t

private theorem anchorCond_succ (P : Inst) {r i t : ℕ} (hr : r ≤ i) :
    AnchorCond P r (i + 1) t ↔ AnchorCond P r i t ∧
      (IsRelevant P (i + 1) → ¬ IsNot P (i + 1) → relDepth P (P.j (i + 1)) ≤ t) := by
  unfold AnchorCond
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, fun k hk1 hk2 => h2 k hk1 (by omega)⟩, h2 (i + 1) (by omega) le_rfl⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h1, fun k hk1 hk2 hk3 hk4 => ?_⟩
    rcases Nat.lt_or_ge k (i + 1) with hlt | hge
    · exact h2 k hk1 (by omega) hk3 hk4
    · rw [show k = i + 1 by omega] at hk3 hk4 ⊢; exact h3 hk3 hk4

private theorem anchorCond_self (P : Inst) {i t : ℕ} :
    AnchorCond P (i + 1) (i + 1) t ↔ relDepth P (P.j (i + 1)) ≤ t := by
  unfold AnchorCond
  constructor
  · rintro ⟨h1, -⟩; exact h1 (by omega)
  · intro h; exact ⟨fun _ => h, fun k hk1 hk2 => by omega⟩

private theorem relDepth_le_succ_iff' (P : Inst) (i t : ℕ) :
    relDepth P i ≤ t + 1 ↔ ∃ r ∈ anchors P i, AnchorCond P r i t :=
  relDepth_le_succ_iff P i t

/-- When gate `i + 1` is not a relevant reset, its anchors below `i + 1` are those of `i`. -/
private theorem mem_anchors_succ (P : Inst) {i r : ℕ}
    (h : ¬ (IsReset P (i + 1) ∧ IsRelevant P (i + 1))) :
    r ∈ anchors P (i + 1) ↔ r ∈ anchors P i ∨ (r = i + 1 ∧ IsReset P (i + 1)) := by
  rw [mem_anchors, mem_anchors, lastRelReset_succ_of_not_relReset P h]
  have := lastRelReset_le P i
  constructor
  · rintro ⟨h1, h2, h3⟩
    rcases Nat.lt_or_ge r (i + 1) with hlt | hge
    · exact Or.inl ⟨h1, by omega, h3⟩
    · right; refine ⟨by omega, ?_⟩
      rcases h3 with h3 | h3
      · omega
      · rwa [show r = i + 1 by omega] at h3
  · rintro (⟨h1, h2, h3⟩ | ⟨rfl, h3⟩)
    · exact ⟨h1, by omega, h3⟩
    · exact ⟨by omega, le_rfl, Or.inr h3⟩

/-- **Lemma 3.5 (a), for `D`:** `D(1) = 1`. -/
theorem relDepth_one (P : Inst) : relDepth P 1 = 1 := by
  have h2 := relDepth_pos P one_pos
  have : relDepth P 1 ≤ 0 + 1 := by
    rw [relDepth_le_succ_iff]
    refine ⟨0, ?_, fun h => absurd rfl h, fun k hk1 hk2 _ hk4 => ?_⟩
    · have h0 : lastRelReset P 1 = 0 :=
        (lastRelReset_succ_of_not_relReset P (i := 0)
          (fun h => not_isReset_of_isNot P (isNot_one P) h.1)).trans (lastRelReset_zero P)
      rw [mem_anchors, h0]; exact ⟨le_rfl, by omega, Or.inl rfl⟩
    · exact absurd (show k = 1 by omega ▸ isNot_one P) hk4
  omega

/-- **Lemma 3.5 (a), for `D`:** at a relevant reset `i ≥ 2`, `D(i) = 1 + D(jᵢ)`. -/
theorem relDepth_succ_of_relReset (P : Inst) {i : ℕ}
    (h : IsReset P (i + 1) ∧ IsRelevant P (i + 1)) :
    relDepth P (i + 1) = 1 + relDepth P (P.j (i + 1)) := by
  apply eq_of_le_succ_iff' (relDepth_pos P (Nat.succ_pos i)) (by omega)
  intro t
  rw [relDepth_le_succ_iff']
  constructor
  · rintro ⟨r, hr, hc⟩
    rw [mem_anchors, lastRelReset_succ_of_relReset P h] at hr
    rw [show r = i + 1 by omega, anchorCond_self] at hc
    omega
  · intro ht
    refine ⟨i + 1, ?_, (anchorCond_self P).2 (by omega)⟩
    rw [mem_anchors, lastRelReset_succ_of_relReset P h]
    exact ⟨le_rfl, le_rfl, Or.inr h.1⟩

/-- **Lemma 3.5 (a), for `D`:** at an irrelevant reset `i ≥ 2`,
`D(i) = min(D(i-1), 1 + D(jᵢ))`. -/
theorem relDepth_succ_of_irrelReset (P : Inst) {i : ℕ} (hi : 1 ≤ i) (hr : IsReset P (i + 1))
    (hrel : ¬ IsRelevant P (i + 1)) :
    relDepth P (i + 1) = min (relDepth P i) (1 + relDepth P (P.j (i + 1))) := by
  have hnr : ¬ (IsReset P (i + 1) ∧ IsRelevant P (i + 1)) := fun h => hrel h.2
  apply eq_of_le_succ_iff' (relDepth_pos P (Nat.succ_pos i))
    (le_min (relDepth_pos P hi) (by omega))
  intro t
  rw [relDepth_le_succ_iff', min_le_iff, relDepth_le_succ_iff']
  constructor
  · rintro ⟨r, hr', hc⟩
    rcases (mem_anchors_succ P hnr).1 hr' with hr'' | ⟨rfl, -⟩
    · have hri : r ≤ i := ((mem_anchors P).1 hr'').2.1
      exact Or.inl ⟨r, hr'', ((anchorCond_succ P hri).1 hc).1⟩
    · right; have := (anchorCond_self P).1 hc; omega
  · rintro (⟨r, hr', hc⟩ | ht)
    · have hri : r ≤ i := ((mem_anchors P).1 hr').2.1
      exact ⟨r, (mem_anchors_succ P hnr).2 (Or.inl hr'),
        (anchorCond_succ P hri).2 ⟨hc, fun h => absurd h hrel⟩⟩
    · exact ⟨i + 1, (mem_anchors_succ P hnr).2 (Or.inr ⟨rfl, hr⟩),
        (anchorCond_self P).2 (by omega)⟩

/-- **Lemma 3.5 (a), for `D`:** at a relevant gate `i ≥ 2` that is neither a reset nor a NOT
gate, `D(i) = max(D(i-1), 1 + D(jᵢ))`. -/
theorem relDepth_succ_of_relOther (P : Inst) {i : ℕ} (hr : ¬ IsReset P (i + 1))
    (hrel : IsRelevant P (i + 1)) (hn : ¬ IsNot P (i + 1)) :
    relDepth P (i + 1) = max (relDepth P i) (1 + relDepth P (P.j (i + 1))) := by
  have hnr : ¬ (IsReset P (i + 1) ∧ IsRelevant P (i + 1)) := fun h => hr h.1
  apply eq_of_le_succ_iff' (relDepth_pos P (Nat.succ_pos i)) (by omega)
  intro t
  rw [relDepth_le_succ_iff', max_le_iff, relDepth_le_succ_iff']
  constructor
  · rintro ⟨r, hr', hc⟩
    rcases (mem_anchors_succ P hnr).1 hr' with hr'' | ⟨rfl, h'⟩
    · have hri : r ≤ i := ((mem_anchors P).1 hr'').2.1
      have := (anchorCond_succ P hri).1 hc
      exact ⟨⟨r, hr'', this.1⟩, by have := this.2 hrel hn; omega⟩
    · exact absurd h' hr
  · rintro ⟨⟨r, hr', hc⟩, ht⟩
    have hri : r ≤ i := ((mem_anchors P).1 hr').2.1
    exact ⟨r, (mem_anchors_succ P hnr).2 (Or.inl hr'),
      (anchorCond_succ P hri).2 ⟨hc, fun _ _ => by omega⟩⟩

/-- **Lemma 3.5 (a), for `D`:** at every other gate `i ≥ 2` (a NOT gate, or an irrelevant gate
that is not a reset), `D(i) = D(i-1)`. -/
theorem relDepth_succ_of_other (P : Inst) {i : ℕ} (hi : 1 ≤ i) (hr : ¬ IsReset P (i + 1))
    (h : IsNot P (i + 1) ∨ ¬ IsRelevant P (i + 1)) :
    relDepth P (i + 1) = relDepth P i := by
  have hnr : ¬ (IsReset P (i + 1) ∧ IsRelevant P (i + 1)) := fun h => hr h.1
  apply eq_of_le_succ_iff' (relDepth_pos P (Nat.succ_pos i)) (relDepth_pos P hi)
  intro t
  rw [relDepth_le_succ_iff', relDepth_le_succ_iff']
  constructor
  · rintro ⟨r, hr', hc⟩
    rcases (mem_anchors_succ P hnr).1 hr' with hr'' | ⟨rfl, h'⟩
    · have hri : r ≤ i := ((mem_anchors P).1 hr'').2.1
      exact ⟨r, hr'', ((anchorCond_succ P hri).1 hc).1⟩
    · exact absurd h' hr
  · rintro ⟨r, hr', hc⟩
    have hri : r ≤ i := ((mem_anchors P).1 hr').2.1
    refine ⟨r, (mem_anchors_succ P hnr).2 (Or.inl hr'), (anchorCond_succ P hri).2 ⟨hc, ?_⟩⟩
    intro h1 h2
    rcases h with h | h
    · exact absurd h h2
    · exact absurd h1 h

/-! ### Lemma 3.5 (b) for `D` -/

/-- **Lemma 3.5 (b), for `D`.** Let `t ≥ 1` and `i ≥ 1`. Then `D(i) ≥ t + 1` iff there is a
relevant gate `a ≤ i`, not a NOT gate, with `D(j_a) ≥ t` and with `D(j_g) ≥ t` for every reset
`g ∈ (a, i]`. -/
theorem relDepth_switch (P : Inst) {t : ℕ} (ht : 1 ≤ t) :
    ∀ i, 1 ≤ i → (t + 1 ≤ relDepth P i ↔
      ∃ a, 1 ≤ a ∧ a ≤ i ∧ IsRelevant P a ∧ ¬ IsNot P a ∧ t ≤ relDepth P (P.j a) ∧
        ∀ g, a < g → g ≤ i → IsReset P g → t ≤ relDepth P (P.j g)) := by
  intro i hi
  induction i, hi using Nat.le_induction with
  | base =>
    rw [relDepth_one]
    constructor
    · intro h; omega
    · rintro ⟨a, ha1, ha2, -, ha3, -⟩
      exact absurd (show a = 1 by omega ▸ isNot_one P) ha3
  | succ i hi ih =>
    -- the statement for `i` (with `a ≤ i`) and the new gate `i + 1`
    have restrict : ∀ a, a ≤ i → ¬ IsReset P (i + 1) →
        ((∀ g, a < g → g ≤ i + 1 → IsReset P g → t ≤ relDepth P (P.j g)) ↔
          (∀ g, a < g → g ≤ i → IsReset P g → t ≤ relDepth P (P.j g))) := by
      intro a ha hnr
      constructor
      · intro h g hg1 hg2 hg3; exact h g hg1 (by omega) hg3
      · intro h g hg1 hg2 hg3
        rcases Nat.lt_or_ge g (i + 1) with hlt | hge
        · exact h g hg1 (by omega) hg3
        · exact absurd (show g = i + 1 by omega ▸ hg3) hnr
    by_cases hr : IsReset P (i + 1)
    · by_cases hrel : IsRelevant P (i + 1)
      · rw [relDepth_succ_of_relReset P ⟨hr, hrel⟩]
        constructor
        · intro h
          exact ⟨i + 1, by omega, le_rfl, hrel, hr.2.1, by omega, fun g hg1 hg2 _ => by omega⟩
        · rintro ⟨a, ha1, ha2, ha3, ha4, ha5, ha6⟩
          rcases Nat.lt_or_ge a (i + 1) with hlt | hge
          · have := ha6 (i + 1) hlt le_rfl hr; omega
          · rw [show a = i + 1 by omega] at ha5; omega
      · rw [relDepth_succ_of_irrelReset P hi hr hrel, le_min_iff, ih]
        constructor
        · rintro ⟨⟨a, ha1, ha2, ha3, ha4, ha5, ha6⟩, hj⟩
          refine ⟨a, ha1, by omega, ha3, ha4, ha5, fun g hg1 hg2 hg3 => ?_⟩
          rcases Nat.lt_or_ge g (i + 1) with hlt | hge
          · exact ha6 g hg1 (by omega) hg3
          · rw [show g = i + 1 by omega]; omega
        · rintro ⟨a, ha1, ha2, ha3, ha4, ha5, ha6⟩
          have hai : a ≤ i := by
            rcases Nat.lt_or_ge a (i + 1) with hlt | hge
            · omega
            · exact absurd (show a = i + 1 by omega ▸ ha3) hrel
          refine ⟨⟨a, ha1, hai, ha3, ha4, ha5, fun g hg1 hg2 hg3 => ha6 g hg1 (by omega) hg3⟩, ?_⟩
          have := ha6 (i + 1) (by omega) le_rfl hr; omega
    · by_cases hcase : IsRelevant P (i + 1) ∧ ¬ IsNot P (i + 1)
      · rw [relDepth_succ_of_relOther P hr hcase.1 hcase.2, le_max_iff, ih]
        constructor
        · rintro (⟨a, ha1, ha2, ha3, ha4, ha5, ha6⟩ | hj)
          · exact ⟨a, ha1, by omega, ha3, ha4, ha5, (restrict a ha2 hr).2 ha6⟩
          · exact ⟨i + 1, by omega, le_rfl, hcase.1, hcase.2, by omega,
              fun g hg1 hg2 _ => by omega⟩
        · rintro ⟨a, ha1, ha2, ha3, ha4, ha5, ha6⟩
          rcases Nat.lt_or_ge a (i + 1) with hlt | hge
          · exact Or.inl ⟨a, ha1, by omega, ha3, ha4, ha5, (restrict a (by omega) hr).1 ha6⟩
          · rw [show a = i + 1 by omega] at ha5; right; omega
      · have hother : IsNot P (i + 1) ∨ ¬ IsRelevant P (i + 1) := by
          by_cases h1 : IsRelevant P (i + 1)
          · exact Or.inl (by by_contra h2; exact hcase ⟨h1, h2⟩)
          · exact Or.inr h1
        rw [relDepth_succ_of_other P hi hr hother, ih]
        constructor
        · rintro ⟨a, ha1, ha2, ha3, ha4, ha5, ha6⟩
          exact ⟨a, ha1, by omega, ha3, ha4, ha5, (restrict a ha2 hr).2 ha6⟩
        · rintro ⟨a, ha1, ha2, ha3, ha4, ha5, ha6⟩
          have hai : a ≤ i := by
            rcases Nat.lt_or_ge a (i + 1) with hlt | hge
            · omega
            · exact absurd ⟨show a = i + 1 by omega ▸ ha3, show a = i + 1 by omega ▸ ha4⟩ hcase
          exact ⟨a, ha1, hai, ha3, ha4, ha5, (restrict a hai hr).1 ha6⟩

/-! ### Lemma 4.2 for `D`: non-deep positions -/

/-- Gate `g` is *clean* for `D` (threshold `t`): not a NOT gate and `D(j_g) ≥ t`. -/
def IsCleanD (P : Inst) (t g : ℕ) : Prop := ¬ IsNot P g ∧ t ≤ relDepth P (P.j g)

/-- Gate `g` is a *killer* for `D` (threshold `t`): a reset with `D(j_g) < t`. -/
def IsKillerD (P : Inst) (t g : ℕ) : Prop := IsReset P g ∧ relDepth P (P.j g) < t

/-- **Lemma 4.2 (non-deep positions).** Let `t ≥ 1` and `1 ≤ s ≤ p`. If `D(p) ≤ t`, then
(A) some killer `u ∈ [s, p]` is such that no relevant gate in `(u, p]` is clean, or (B) no
relevant gate in `[s, p]` is clean. -/
theorem zones_relDepth (P : Inst) {t s p : ℕ} (ht : 1 ≤ t) (hs : 1 ≤ s)
    (hd : relDepth P p ≤ t) :
    (∃ u, s ≤ u ∧ u ≤ p ∧ IsKillerD P t u ∧
        ∀ g, u < g → g ≤ p → IsRelevant P g → ¬ IsCleanD P t g) ∨
      (∀ g, s ≤ g → g ≤ p → IsRelevant P g → ¬ IsCleanD P t g) := by
  classical
  by_cases hB : ∀ g, s ≤ g → g ≤ p → IsRelevant P g → ¬ IsCleanD P t g
  · exact Or.inr hB
  · left
    push Not at hB
    obtain ⟨g₀, hg₀1, hg₀2, hg₀3, hg₀4⟩ := hB
    set a := Nat.findGreatest (fun g => s ≤ g ∧ IsRelevant P g ∧ IsCleanD P t g) p with ha
    have haspec : s ≤ a ∧ IsRelevant P a ∧ IsCleanD P t a :=
      Nat.findGreatest_spec (P := fun g => s ≤ g ∧ IsRelevant P g ∧ IsCleanD P t g) hg₀2
        ⟨hg₀1, hg₀3, hg₀4⟩
    have hap : a ≤ p := Nat.findGreatest_le p
    have hagreat : ∀ g, a < g → g ≤ p → IsRelevant P g → ¬ IsCleanD P t g :=
      fun g h1 h2 hrel hc =>
        Nat.findGreatest_is_greatest (P := fun g => s ≤ g ∧ IsRelevant P g ∧ IsCleanD P t g)
          h1 h2 ⟨by omega, hrel, hc⟩
    have hk : ∃ g, a < g ∧ g ≤ p ∧ IsKillerD P t g := by
      by_contra hc
      push Not at hc
      have := (relDepth_switch P ht p (by omega)).2
        ⟨a, by omega, hap, haspec.2.1, haspec.2.2.1, haspec.2.2.2, fun g hg1 hg2 hg3 => by
          by_contra hlt; push Not at hlt
          exact hc g hg1 hg2 ⟨hg3, hlt⟩⟩
      omega
    obtain ⟨g₁, hg₁1, hg₁2, hg₁3⟩ := hk
    set u := Nat.findGreatest (fun g => a < g ∧ IsKillerD P t g) p with hu
    have huspec : a < u ∧ IsKillerD P t u :=
      Nat.findGreatest_spec (P := fun g => a < g ∧ IsKillerD P t g) hg₁2 ⟨hg₁1, hg₁3⟩
    have hup : u ≤ p := Nat.findGreatest_le p
    exact ⟨u, by omega, hup, huspec.2, fun g hg1 hg2 => hagreat g (by omega) hg2⟩

/-- **Lemma 4.2, further claims.** In case (A), gate `u + 1` is relevant. If `x*_p = 1` (and
`D(p) ≤ t`, `p ≥ 1`), then gate `p` is relevant and not clean, and `p` is not a killer (so
`u < p` in case (A)). -/
theorem zones_relDepth_of_trace_one (P : Inst) {t p : ℕ} (ht : 1 ≤ t) (hp : 1 ≤ p)
    (hd : relDepth P p ≤ t) (h1 : trace P p = 1) :
    IsRelevant P p ∧ ¬ IsCleanD P t p ∧ ¬ IsKillerD P t p := by
  have hrel := isRelevant_of_trace_one P hp h1
  refine ⟨hrel, fun hc => ?_, fun hk => ?_⟩
  · have := (relDepth_switch P ht p hp).2
      ⟨p, hp, le_rfl, hrel, hc.1, hc.2, fun g hg1 hg2 _ => by omega⟩
    omega
  · rw [trace_of_isReset P hk.1] at h1; exact absurd h1 (by decide)

/-- **The over-approximation step of Theorem 4.3 (a).** Let `t ≥ 1`, `1 ≤ s ≤ p`, `D(p) ≤ t`, and
let `U`, `K` be predicates on gates such that every gate `g ∈ [s, p]` with `¬ U g` is clean and
every killer `g ∈ [s, p]` has `K g`. Then (A′) some `u ∈ [s, p]` has `K u`, has `U (u+1)` if
`u < p`, and no two consecutive gates in `(u, p]` fail `U`; or (B′) no two consecutive gates in
`[s, p]` fail `U`. If moreover `x*_p = 1`, then `U p`, and in (A′) one can take `u < p`. -/
theorem overapprox_relDepth (P : Inst) {t s p : ℕ} (ht : 1 ≤ t) (hs : 1 ≤ s) (hsp : s ≤ p)
    (hd : relDepth P p ≤ t) (U K : ℕ → Prop)
    (hU : ∀ g, s ≤ g → g ≤ p → ¬ U g → IsCleanD P t g)
    (hK : ∀ g, s ≤ g → g ≤ p → IsKillerD P t g → K g) :
    ((∃ u, s ≤ u ∧ u ≤ p ∧ K u ∧ (u < p → U (u + 1)) ∧
        ∀ g, u < g → g + 1 ≤ p → U g ∨ U (g + 1)) ∨
      (∀ g, s ≤ g → g + 1 ≤ p → U g ∨ U (g + 1))) ∧
    (trace P p = 1 → U p ∧
      ((∃ u, s ≤ u ∧ u < p ∧ K u ∧ U (u + 1) ∧
          ∀ g, u < g → g + 1 ≤ p → U g ∨ U (g + 1)) ∨
        (∀ g, s ≤ g → g + 1 ≤ p → U g ∨ U (g + 1)))) := by
  -- a relevant gate in the clean-free range has `U`
  have hUc : ∀ g, s ≤ g → g ≤ p → ¬ IsCleanD P t g → U g := fun g h1 h2 h3 => by
    by_contra hc; exact h3 (hU g h1 h2 hc)
  have pair : ∀ lo, 1 ≤ lo → s ≤ lo →
      (∀ g, lo ≤ g → g ≤ p → IsRelevant P g → ¬ IsCleanD P t g) →
      ∀ g, lo ≤ g → g + 1 ≤ p → U g ∨ U (g + 1) := by
    intro lo hlo hslo hfree g hg1 hg2
    rcases isRelevant_or_succ P (show 1 ≤ g by omega) with h | h
    · exact Or.inl (hUc g (by omega) (by omega) (hfree g hg1 (by omega) h))
    · exact Or.inr (hUc (g + 1) (by omega) hg2 (hfree (g + 1) (by omega) hg2 h))
  have main := zones_relDepth P ht hs hd
  have partA : ∀ u, s ≤ u → u ≤ p → IsKillerD P t u →
      (∀ g, u < g → g ≤ p → IsRelevant P g → ¬ IsCleanD P t g) →
      K u ∧ (u < p → U (u + 1)) ∧ ∀ g, u < g → g + 1 ≤ p → U g ∨ U (g + 1) := by
    intro u hu1 hu2 hu3 hu4
    refine ⟨hK u hu1 hu2 hu3, fun hlt => ?_, fun g hg1 hg2 => ?_⟩
    · exact hUc (u + 1) (by omega) hlt
        (hu4 (u + 1) (by omega) hlt (isRelevant_succ_of_isReset P hu3.1))
    · exact pair (u + 1) (by omega) (by omega) (fun g' h1 h2 h3 => hu4 g' (by omega) h2 h3) g
        (by omega) hg2
  refine ⟨?_, fun h1 => ?_⟩
  · rcases main with ⟨u, hu1, hu2, hu3, hu4⟩ | hB
    · exact Or.inl ⟨u, hu1, hu2, partA u hu1 hu2 hu3 hu4⟩
    · exact Or.inr (pair s hs le_rfl hB)
  · obtain ⟨hrel, hnc, hnk⟩ := zones_relDepth_of_trace_one P ht (by omega) hd h1
    refine ⟨hUc p hsp le_rfl hnc, ?_⟩
    rcases main with ⟨u, hu1, hu2, hu3, hu4⟩ | hB
    · have hup : u ≠ p := fun h => hnk (h ▸ hu3)
      obtain ⟨k1, k2, k3⟩ := partA u hu1 hu2 hu3 hu4
      exact Or.inl ⟨u, hu1, by omega, k1, k2 (by omega), k3⟩
    · exact Or.inr (pair s hs le_rfl hB)

end GC.RandomSeqNOR
