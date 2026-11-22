import GC.Computability.RandomSeqNOR.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Logic.Function.Iterate

/-!
# The Kleene–prefix iteration (manuscripts 001c and 001d, Section 3)

Resets, the reset decomposition of the trace, the Kleene–prefix iteration (Definition 3.1) as an
explicit function, the dependency depth `d`, and Lemma 3.2 ("rounds equal dependency depth").
-/

namespace GC.RandomSeqNOR

/-- Gate `k` is a *reset* if it is not a NOT gate and `x*_{jₖ} = 1` (then `x*ₖ = 0`). -/
def IsReset (P : Inst) (k : ℕ) : Prop := 0 < k ∧ ¬ IsNot P k ∧ trace P (P.j k) = 1

instance (P : Inst) (k : ℕ) : Decidable (IsReset P k) := by unfold IsReset; infer_instance

/-- `ϱ(i)`: the largest `r ≤ i` that is `0` or a reset. -/
def lastReset (P : Inst) (i : ℕ) : ℕ := Nat.findGreatest (fun r => r = 0 ∨ IsReset P r) i

theorem lastReset_le (P : Inst) (i : ℕ) : lastReset P i ≤ i := Nat.findGreatest_le i

theorem lastReset_spec (P : Inst) (i : ℕ) : lastReset P i = 0 ∨ IsReset P (lastReset P i) :=
  Nat.findGreatest_spec (P := fun r => r = 0 ∨ IsReset P r) (Nat.zero_le i) (Or.inl rfl)

theorem not_isReset_of_lastReset_lt (P : Inst) {i k : ℕ} (hk : lastReset P i < k) (hki : k ≤ i) :
    ¬ IsReset P k := fun h =>
  Nat.findGreatest_is_greatest (P := fun r => r = 0 ∨ IsReset P r) hk hki (Or.inr h)

theorem le_lastReset (P : Inst) {i k : ℕ} (hki : k ≤ i) (hk : IsReset P k) : k ≤ lastReset P i :=
  Nat.le_findGreatest (P := fun r => r = 0 ∨ IsReset P r) hki (Or.inr hk)

theorem trace_of_isReset (P : Inst) {k : ℕ} (h : IsReset P k) : trace P k = 0 := by
  obtain ⟨hpos, -, h1⟩ := h
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [trace_succ, h1]
  generalize trace P m = a; revert a; decide

/-- A gate that is not a reset complements its predecessor. -/
theorem trace_succ_of_not_isReset (P : Inst) (i : ℕ) (h : ¬ IsReset P (i + 1)) :
    trace P (i + 1) = 1 + trace P i := by
  by_cases hn : IsNot P (i + 1)
  · exact trace_succ_of_isNot P i hn
  · have h0 : trace P (P.j (i + 1)) = 0 :=
      (zmod2_ne_one_iff _).1 fun h1 => h ⟨Nat.succ_pos i, hn, h1⟩
    rw [trace_succ, h0]; ring

/-- Between resets the trace alternates: if no gate in `(r, i]` is a reset, then
`x*ᵢ = x*ᵣ ⊕ ((i - r) mod 2)`. -/
theorem trace_eq_of_no_reset (P : Inst) {r i : ℕ} (hri : r ≤ i)
    (h : ∀ k, r < k → k ≤ i → ¬ IsReset P k) :
    trace P i = trace P r + ((i - r : ℕ) : ZMod 2) := by
  induction i, hri using Nat.le_induction with
  | base => simp
  | succ i hri ih =>
    rw [trace_succ_of_not_isReset P i (h (i + 1) (by omega) le_rfl),
      ih (fun k hk hki => h k hk (by omega)), Nat.succ_sub hri]
    push_cast; ring

/-- The reset decomposition: `x*ᵢ = x*_{ϱ(i)} ⊕ ((i - ϱ(i)) mod 2)`, where `x*₀ = 1` and
`x*ᵣ = 0` at a reset. -/
theorem trace_eq_lastReset (P : Inst) (i : ℕ) :
    trace P i = (if lastReset P i = 0 then 1 else 0) + ((i - lastReset P i : ℕ) : ZMod 2) := by
  rw [trace_eq_of_no_reset P (lastReset_le P i) fun k hk hki => not_isReset_of_lastReset_lt P hk hki]
  congr 1
  rcases lastReset_spec P i with h | h
  · rw [if_pos h, h, trace_zero]
  · rw [if_neg (fun h' => h.1.ne' h'), trace_of_isReset P h]

/-! ### Definition 3.1: the Kleene–prefix iteration -/

/-- A state of the Kleene–prefix iteration: the set `K` of known positions and values `v`. -/
structure KPState where
  /-- The set `K_t` of known positions. -/
  known : Set ℕ
  /-- The values `v_p` (meaningful for `p ∈ K_t`). -/
  val : ℕ → ZMod 2

/-- Gate `k` is resolved in the next round: it is a NOT gate or `jₖ ∈ K_t`. -/
def KPResolved (P : Inst) (S : KPState) (k : ℕ) : Prop := IsNot P k ∨ P.j k ∈ S.known

/-- A resolved reset: a resolved gate `k ≥ 1`, not a NOT gate, with `v_{jₖ} = 1`. -/
def KPResolvedReset (P : Inst) (S : KPState) (k : ℕ) : Prop :=
  0 < k ∧ ¬ IsNot P k ∧ P.j k ∈ S.known ∧ S.val (P.j k) = 1

open Classical in
/-- `rᵢ`: the largest `r ≤ i` that is `0` or a resolved reset. -/
noncomputable def kpAnchor (P : Inst) (S : KPState) (i : ℕ) : ℕ :=
  Nat.findGreatest (fun r => r = 0 ∨ KPResolvedReset P S r) i

/-- One round of the Kleene–prefix iteration: `i ∈ K_{t+1}` iff every gate in `(rᵢ, i]` is
resolved, and then `vᵢ = v_{rᵢ} ⊕ ((i - rᵢ) mod 2)` with `v₀ = 1` and `vᵣ = 0` at a resolved reset. -/
noncomputable def kpStep (P : Inst) (S : KPState) : KPState where
  known := {i | ∀ k, kpAnchor P S i < k → k ≤ i → KPResolved P S k}
  val i := (if kpAnchor P S i = 0 then 1 else 0) + ((i - kpAnchor P S i : ℕ) : ZMod 2)

/-- The initial state: `K₀ = {0}`, `v₀ = 1`. -/
def kpStart : KPState := ⟨{0}, fun _ => 1⟩

/-- The state after `t` rounds. -/
noncomputable def kpIter (P : Inst) (t : ℕ) : KPState := (kpStep P)^[t] kpStart

/-! ### The dependency depth -/

/-- The dependency depth: `d(0) = 0` and, for `i ≥ 1`,
`d(i) = 1 + max {d(jₖ) : k not a NOT gate, max(ϱ(i), 1) ≤ k ≤ i}` (with `max ∅ = 0`). -/
def depth (P : Inst) : ℕ → ℕ
  | 0 => 0
  | i + 1 => 1 + ((Finset.Icc (max (lastReset P (i + 1)) 1) (i + 1)).filter
      (fun k => ¬ IsNot P k)).attach.sup (fun k => depth P (P.j k.1))
termination_by i => i
decreasing_by
  have hk := k.2
  simp only [Finset.mem_filter, Finset.mem_Icc] at hk
  have := P.j_lt k.1 (by omega)
  omega

theorem depth_zero (P : Inst) : depth P 0 = 0 := by rw [depth]

/-- The defining property of the depth, in the form used by Lemma 3.2:
`d(i) ≤ t + 1` iff every non-NOT gate `k ∈ [max(ϱ(i), 1), i]` has `d(jₖ) ≤ t`. -/
theorem depth_le_succ_iff (P : Inst) (i t : ℕ) :
    depth P i ≤ t + 1 ↔
      ∀ k, max (lastReset P i) 1 ≤ k → k ≤ i → ¬ IsNot P k → depth P (P.j k) ≤ t := by
  cases i with
  | zero =>
    rw [depth_zero]
    simp only [zero_le, true_iff]
    intro k hk hk0; omega
  | succ i =>
    rw [depth, add_comm, Nat.add_le_add_iff_right, Finset.sup_le_iff]
    constructor
    · intro h k hk1 hk2 hk3
      exact h ⟨k, by simp only [Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨hk1, hk2⟩, hk3⟩⟩
        (Finset.mem_attach _ _)
    · rintro h ⟨k, hk⟩ -
      simp only [Finset.mem_filter, Finset.mem_Icc] at hk
      exact h k hk.1.1 hk.1.2 hk.2

theorem depth_pos (P : Inst) {i : ℕ} (hi : 0 < i) : 0 < depth P i := by
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  rw [depth]; omega

theorem depth_eq_zero_iff (P : Inst) (i : ℕ) : depth P i = 0 ↔ i = 0 := by
  constructor
  · intro h; by_contra hi; have := depth_pos P (Nat.pos_of_ne_zero hi); omega
  · rintro rfl; exact depth_zero P

/-- `d(i) ≤ i`. -/
theorem depth_le_self (P : Inst) (i : ℕ) : depth P i ≤ i := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    cases i with
    | zero => rw [depth_zero]
    | succ i =>
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · -- gate `1` is a NOT gate, so the maximum is over the empty set
        have : depth P 1 ≤ 0 + 1 := by
          rw [depth_le_succ_iff]
          intro k hk1 hk2 hk3
          exact absurd (show IsNot P k by
            unfold IsNot; rw [show k = 1 by omega, j_one]) hk3
        simpa using this
      · obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
        rw [depth_le_succ_iff]
        intro k hk1 hk2 hk3
        have hlt := P.j_lt k (by omega)
        have hne : P.j k + 1 ≠ k := hk3
        have := ih (P.j k) (by omega)
        omega

/-! ### Lemma 3.2: rounds equal dependency depth -/

theorem kpIter_zero (P : Inst) : kpIter P 0 = kpStart := rfl

theorem kpIter_succ (P : Inst) (t : ℕ) : kpIter P (t + 1) = kpStep P (kpIter P t) := by
  unfold kpIter; rw [Function.iterate_succ_apply']

/-- **Lemma 3.2 (rounds equal dependency depth).** For every `t ≥ 0`,
`K_t = {i : d(i) ≤ t}`, and `vᵢ = x*ᵢ` for every `i ∈ K_t`. -/
theorem kp_rounds_eq_depth (P : Inst) (t : ℕ) :
    (kpIter P t).known = {i | depth P i ≤ t} ∧
      ∀ i ∈ (kpIter P t).known, (kpIter P t).val i = trace P i := by
  induction t with
  | zero =>
    refine ⟨?_, ?_⟩
    · ext i
      simp only [kpIter_zero, kpStart, Set.mem_singleton_iff, Set.mem_ofPred_eq, Nat.le_zero,
        depth_eq_zero_iff]
    · intro i hi
      simp only [kpIter_zero, kpStart, Set.mem_singleton_iff] at hi
      subst hi; rw [trace_zero]; rfl
  | succ t ih =>
    obtain ⟨hK, hV⟩ := ih
    set S := kpIter P t with hS
    rw [kpIter_succ]
    -- resolution in terms of the depth
    have hres : ∀ k, KPResolved P S k ↔ IsNot P k ∨ depth P (P.j k) ≤ t := by
      intro k; simp only [KPResolved, hK, Set.mem_ofPred_eq]
    -- resolved resets are resets
    have hrr : ∀ k, KPResolvedReset P S k → IsReset P k := by
      rintro k ⟨h0, h1, h2, h3⟩
      exact ⟨h0, h1, (hV _ h2) ▸ h3⟩
    -- a non-NOT gate whose pointer is known and which is a reset is a resolved reset
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
    have hknown : ∀ i, i ∈ (kpStep P S).known ↔ depth P i ≤ t + 1 := by
      intro i
      show (∀ k, kpAnchor P S i < k → k ≤ i → KPResolved P S k) ↔ _
      rw [depth_le_succ_iff]
      constructor
      · intro h k hk1 hk2 hk3
        by_cases hlt : kpAnchor P S i < k
        · exact ((hres k).1 (h k hlt hk2)).resolve_left hk3
        · -- then `k = rᵢ = ϱ(i) ≥ 1`, a resolved reset
          have h1 := hanchor_le i
          have hk : k = kpAnchor P S i := by omega
          rcases hanchor_spec i with h0 | h0
          · omega
          · rw [hk]
            have := h0.2.2.1
            rw [hK] at this
            exact this
      · intro h k hk1 hk2
        rw [hres]
        by_cases hn : IsNot P k
        · exact Or.inl hn
        · right
          apply h k _ hk2 hn
          refine max_le ?_ (by omega)
          -- `ϱ(i) ≤ rᵢ`
          rcases lastReset_spec P i with h0 | h0
          · omega
          · have hρ : lastReset P i ≤ kpAnchor P S i := by
              apply hanchor_ge i _ (lastReset_le P i)
              apply hrr' _ h0
              rw [hK]
              exact h _ (max_le le_rfl h0.1) (lastReset_le P i) h0.2.1
            omega
    refine ⟨Set.ext hknown, ?_⟩
    intro i hi
    have hi' : ∀ k, kpAnchor P S i < k → k ≤ i → KPResolved P S k := hi
    -- no gate in `(rᵢ, i]` is a reset
    have hnr : ∀ k, kpAnchor P S i < k → k ≤ i → ¬ IsReset P k := by
      intro k hk1 hk2 hreset
      apply hanchor_great i k hk1 hk2
      apply hrr' k hreset
      exact (hi' k hk1 hk2).resolve_left hreset.2.1
    show (if kpAnchor P S i = 0 then 1 else 0) + ((i - kpAnchor P S i : ℕ) : ZMod 2) = trace P i
    have hle : kpAnchor P S i ≤ i := le_trans (hanchor_le i) (lastReset_le P i)
    rw [trace_eq_of_no_reset P (r := kpAnchor P S i) hle hnr]
    congr 1
    rcases hanchor_spec i with h0 | h0
    · rw [if_pos h0, h0, trace_zero]
    · rw [if_neg (fun h' => h0.1.ne' h'), trace_of_isReset P (hrr _ h0)]

/-- Consequence of Lemma 3.2: after `R` rounds the iteration knows all of `[0, n]` (and then its
values are the trace) iff `max_{i ≤ n} d(i) ≤ R`. -/
theorem kp_success_iff (P : Inst) (R n : ℕ) :
    (∀ i ≤ n, i ∈ (kpIter P R).known) ↔ ∀ i ≤ n, depth P i ≤ R := by
  rw [(kp_rounds_eq_depth P R).1]; rfl

end GC.RandomSeqNOR
