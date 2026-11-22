import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Logic.Function.Iterate
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Comparator challenge for manuscript 001d (Small Noise Defeats Two Natural Parallel Iterations). Definitions are copied verbatim from
the solution files; theorems are stated with `sorry`. -/

namespace GC.RandomSeqNOR

/-- A Sequential NOR instance (infinite pointer sequence): gate `i ≥ 1` reads `i - 1` and `j i`,
with `j i < i`. The value `j 0` is irrelevant. -/
structure Inst where
  /-- The pointer of gate `i`. -/
  j : ℕ → ℕ
  /-- Pointers go strictly backwards. -/
  j_lt : ∀ i, 0 < i → j i < i

/-- The trace `x*` of an instance: `x*₀ = 1`, `x*ᵢ = (1 + x*ᵢ₋₁)(1 + x*_{jᵢ})`. -/
def trace (P : Inst) : ℕ → ZMod 2
  | 0 => 1
  | i + 1 => (1 + trace P i) * (1 + trace P (P.j (i + 1)))
termination_by i => i
decreasing_by
  · omega
  · exact P.j_lt (i + 1) (Nat.succ_pos i)

/-- Gate `i ≥ 1` is a NOT gate when `jᵢ = i - 1`. -/
def IsNot (P : Inst) (i : ℕ) : Prop := P.j i + 1 = i

instance (P : Inst) (i : ℕ) : Decidable (IsNot P i) := by unfold IsNot; infer_instance

/-- Gate `k` is a *reset* if it is not a NOT gate and `x*_{jₖ} = 1` (then `x*ₖ = 0`). -/
def IsReset (P : Inst) (k : ℕ) : Prop := 0 < k ∧ ¬ IsNot P k ∧ trace P (P.j k) = 1

instance (P : Inst) (k : ℕ) : Decidable (IsReset P k) := by unfold IsReset; infer_instance

/-- `ϱ(i)`: the largest `r ≤ i` that is `0` or a reset. -/
def lastReset (P : Inst) (i : ℕ) : ℕ := Nat.findGreatest (fun r => r = 0 ∨ IsReset P r) i

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

/-- Gate `k ≥ 1` is *relevant* if `x*_{k-1} = 0`. -/
def IsRelevant (P : Inst) (k : ℕ) : Prop := 0 < k ∧ trace P (k - 1) = 0

instance (P : Inst) (k : ℕ) : Decidable (IsRelevant P k) := by unfold IsRelevant; infer_instance

/-- `ϱ'(i)`: the largest `r ≤ i` that is `0` or a reset at a relevant gate. -/
def lastRelReset (P : Inst) (i : ℕ) : ℕ :=
  Nat.findGreatest (fun r => r = 0 ∨ (IsReset P r ∧ IsRelevant P r)) i

/-- The anchors of `i`: the resets in `[ϱ'(i), i]`, together with `0` if `ϱ'(i) = 0`. -/
def anchors (P : Inst) (i : ℕ) : Finset ℕ :=
  (Finset.Icc (lastRelReset P i) i).filter (fun r => r = 0 ∨ IsReset P r)

theorem mem_anchors (P : Inst) {i r : ℕ} :
    r ∈ anchors P i ↔ lastRelReset P i ≤ r ∧ r ≤ i ∧ (r = 0 ∨ IsReset P r) := by
  sorry

theorem lastRelReset_mem_anchors (P : Inst) (i : ℕ) : lastRelReset P i ∈ anchors P i := by
  sorry

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

/-- Gate `g` is *clean* (for the threshold `t`): not a NOT gate and `d(j_g) ≥ t`. -/
def IsClean (P : Inst) (t g : ℕ) : Prop := ¬ IsNot P g ∧ t ≤ depth P (P.j g)

/-- Gate `g` is a *killer* (for the threshold `t`): a reset with `d(j_g) < t`. -/
def IsKiller (P : Inst) (t g : ℕ) : Prop := IsReset P g ∧ depth P (P.j g) < t

/-- Gate `g` is *clean* for `D` (threshold `t`): not a NOT gate and `D(j_g) ≥ t`. -/
def IsCleanD (P : Inst) (t g : ℕ) : Prop := ¬ IsNot P g ∧ t ≤ relDepth P (P.j g)

/-- Gate `g` is a *killer* for `D` (threshold `t`): a reset with `D(j_g) < t`. -/
def IsKillerD (P : Inst) (t g : ℕ) : Prop := IsReset P g ∧ relDepth P (P.j g) < t

/-- The recursion `a₀ = 1`, `b₀ = 0`, `a_{r+1} = u(a_r + b_r)`, `b_{r+1} = (1-u) a_r` of the
proof of Theorem 4.3 (probabilities that `r` gates have no two consecutive `Û = 0` and that the
last one has `Û = 1`, resp. `Û = 0`). -/
def noTwoZeros (u : ℝ) : ℕ → ℝ × ℝ
  | 0 => (1, 0)
  | r + 1 => (u * ((noTwoZeros u r).1 + (noTwoZeros u r).2), (1 - u) * (noTwoZeros u r).1)

/-- **Lemma 3.2 (rounds equal dependency depth).** For every `t ≥ 0`,
`K_t = {i : d(i) ≤ t}`, and `vᵢ = x*ᵢ` for every `i ∈ K_t`. -/
theorem kp_rounds_eq_depth (P : Inst) (t : ℕ) :
    (kpIter P t).known = {i | depth P i ≤ t} ∧
      ∀ i ∈ (kpIter P t).known, (kpIter P t).val i = trace P i := by
  sorry

/-- **Lemma 3.4 (a).** For every `t ≥ 0`, the relevance-pruned iteration has
`K_t = {i : D(i) ≤ t}`, and `vᵢ = x*ᵢ` for every `i ∈ K_t`. -/
theorem kpr_rounds_eq_relDepth (P : Inst) (t : ℕ) :
    (kprIter P t).known = {i | relDepth P i ≤ t} ∧
      ∀ i ∈ (kprIter P t).known, (kprIter P t).val i = trace P i := by
  sorry

/-- `D(i) ≤ d(i)`: the relevance-pruned depth never exceeds the Kleene–prefix depth. -/
theorem relDepth_le_depth (P : Inst) (i : ℕ) : relDepth P i ≤ depth P i := by
  sorry

/-- **Lemma 3.4 (b).** After every round, every position known to the Kleene–prefix iteration is
known to the relevance-pruned iteration. -/
theorem kp_known_subset_kpr_known (P : Inst) (t : ℕ) :
    (kpIter P t).known ⊆ (kprIter P t).known := by
  sorry

/-- **Lemma 3.5 (a), for `d`:** `d(1) = 1`. -/
theorem depth_one (P : Inst) : depth P 1 = 1 := by
  sorry

/-- **Lemma 3.5 (a), for `d`:** at a reset `i ≥ 2`, `d(i) = 1 + d(jᵢ)`. -/
theorem depth_succ_of_isReset (P : Inst) {i : ℕ} (h : IsReset P (i + 1)) :
    depth P (i + 1) = 1 + depth P (P.j (i + 1)) := by
  sorry

/-- **Lemma 3.5 (a), for `d`:** at a NOT gate `i ≥ 2`, `d(i) = d(i-1)`. -/
theorem depth_succ_of_isNot (P : Inst) {i : ℕ} (hi : 1 ≤ i) (h : IsNot P (i + 1)) :
    depth P (i + 1) = depth P i := by
  sorry

/-- **Lemma 3.5 (a), for `d`:** at a gate `i ≥ 2` that is neither a reset nor a NOT gate,
`d(i) = max(d(i-1), 1 + d(jᵢ))`. -/
theorem depth_succ_of_other (P : Inst) {i : ℕ} (hi : 1 ≤ i) (hr : ¬ IsReset P (i + 1))
    (hn : ¬ IsNot P (i + 1)) :
    depth P (i + 1) = max (depth P i) (1 + depth P (P.j (i + 1))) := by
  sorry

/-- **Lemma 3.5 (b), for `d`.** Let `t ≥ 1` and `i ≥ 1`. Then `d(i) ≥ t + 1` iff there is a gate
`a ≤ i`, not a NOT gate, with `d(j_a) ≥ t` and with `d(j_g) ≥ t` for every reset `g ∈ (a, i]`. -/
theorem depth_switch (P : Inst) {t : ℕ} (ht : 1 ≤ t) :
    ∀ i, 1 ≤ i → (t + 1 ≤ depth P i ↔
      ∃ a, 1 ≤ a ∧ a ≤ i ∧ ¬ IsNot P a ∧ t ≤ depth P (P.j a) ∧
        ∀ g, a < g → g ≤ i → IsReset P g → t ≤ depth P (P.j g)) := by
  sorry

/-- **Lemma 3.5 (a), for `D`:** `D(1) = 1`. -/
theorem relDepth_one (P : Inst) : relDepth P 1 = 1 := by
  sorry

/-- **Lemma 3.5 (a), for `D`:** at a relevant reset `i ≥ 2`, `D(i) = 1 + D(jᵢ)`. -/
theorem relDepth_succ_of_relReset (P : Inst) {i : ℕ}
    (h : IsReset P (i + 1) ∧ IsRelevant P (i + 1)) :
    relDepth P (i + 1) = 1 + relDepth P (P.j (i + 1)) := by
  sorry

/-- **Lemma 3.5 (a), for `D`:** at an irrelevant reset `i ≥ 2`,
`D(i) = min(D(i-1), 1 + D(jᵢ))`. -/
theorem relDepth_succ_of_irrelReset (P : Inst) {i : ℕ} (hi : 1 ≤ i) (hr : IsReset P (i + 1))
    (hrel : ¬ IsRelevant P (i + 1)) :
    relDepth P (i + 1) = min (relDepth P i) (1 + relDepth P (P.j (i + 1))) := by
  sorry

/-- **Lemma 3.5 (a), for `D`:** at a relevant gate `i ≥ 2` that is neither a reset nor a NOT
gate, `D(i) = max(D(i-1), 1 + D(jᵢ))`. -/
theorem relDepth_succ_of_relOther (P : Inst) {i : ℕ} (hr : ¬ IsReset P (i + 1))
    (hrel : IsRelevant P (i + 1)) (hn : ¬ IsNot P (i + 1)) :
    relDepth P (i + 1) = max (relDepth P i) (1 + relDepth P (P.j (i + 1))) := by
  sorry

/-- **Lemma 3.5 (a), for `D`:** at every other gate `i ≥ 2` (a NOT gate, or an irrelevant gate
that is not a reset), `D(i) = D(i-1)`. -/
theorem relDepth_succ_of_other (P : Inst) {i : ℕ} (hi : 1 ≤ i) (hr : ¬ IsReset P (i + 1))
    (h : IsNot P (i + 1) ∨ ¬ IsRelevant P (i + 1)) :
    relDepth P (i + 1) = relDepth P i := by
  sorry

/-- **Lemma 3.5 (b), for `D`.** Let `t ≥ 1` and `i ≥ 1`. Then `D(i) ≥ t + 1` iff there is a
relevant gate `a ≤ i`, not a NOT gate, with `D(j_a) ≥ t` and with `D(j_g) ≥ t` for every reset
`g ∈ (a, i]`. -/
theorem relDepth_switch (P : Inst) {t : ℕ} (ht : 1 ≤ t) :
    ∀ i, 1 ≤ i → (t + 1 ≤ relDepth P i ↔
      ∃ a, 1 ≤ a ∧ a ≤ i ∧ IsRelevant P a ∧ ¬ IsNot P a ∧ t ≤ relDepth P (P.j a) ∧
        ∀ g, a < g → g ≤ i → IsReset P g → t ≤ relDepth P (P.j g)) := by
  sorry

/-- **Lemma 4.2 for `d` (non-deep positions).** Let `t ≥ 1` and `1 ≤ s ≤ p`. If `d(p) ≤ t`, then
(A) some killer `u ∈ [s, p]` is such that no gate in `(u, p]` is clean, or (B) no gate in
`[s, p]` is clean. -/
theorem zones_depth (P : Inst) {t s p : ℕ} (ht : 1 ≤ t) (hs : 1 ≤ s)
    (hd : depth P p ≤ t) :
    (∃ u, s ≤ u ∧ u ≤ p ∧ IsKiller P t u ∧ ∀ g, u < g → g ≤ p → ¬ IsClean P t g) ∨
      (∀ g, s ≤ g → g ≤ p → ¬ IsClean P t g) := by
  sorry

/-- **Lemma 4.2 for `d`, last claim.** If moreover `x*_p = 1`, then `p` is not clean, and `p` is
not a killer (so `u < p` in case (A)). -/
theorem zones_depth_of_trace_one (P : Inst) {t p : ℕ} (ht : 1 ≤ t) (hp : 1 ≤ p)
    (hd : depth P p ≤ t) (h1 : trace P p = 1) :
    ¬ IsClean P t p ∧ ¬ IsKiller P t p := by
  sorry

/-- **The over-approximation step of Theorem 4.3 (b).** Let `t ≥ 1`, `1 ≤ s ≤ p`, `d(p) ≤ t`, and
let `U`, `K` be predicates on gates such that every gate `g ∈ [s, p]` with `¬ U g` is clean and
every killer `g ∈ [s, p]` has `K g`. Then (A′) some `u ∈ [s, p]` has `K u` and `U g` for every
`g ∈ (u, p]`, or (B′) `U g` for every `g ∈ [s, p]`. If moreover `x*_p = 1`, then `U p`, and in
(A′) one can take `u < p`. -/
theorem overapprox_depth (P : Inst) {t s p : ℕ} (ht : 1 ≤ t) (hs : 1 ≤ s) (hsp : s ≤ p)
    (hd : depth P p ≤ t) (U K : ℕ → Prop)
    (hU : ∀ g, s ≤ g → g ≤ p → ¬ U g → IsClean P t g)
    (hK : ∀ g, s ≤ g → g ≤ p → IsKiller P t g → K g) :
    ((∃ u, s ≤ u ∧ u ≤ p ∧ K u ∧ ∀ g, u < g → g ≤ p → U g) ∨ (∀ g, s ≤ g → g ≤ p → U g)) ∧
      (trace P p = 1 → U p ∧
        ((∃ u, s ≤ u ∧ u < p ∧ K u ∧ ∀ g, u < g → g ≤ p → U g) ∨
          (∀ g, s ≤ g → g ≤ p → U g))) := by
  sorry

/-- **Lemma 4.2 (non-deep positions).** Let `t ≥ 1` and `1 ≤ s ≤ p`. If `D(p) ≤ t`, then
(A) some killer `u ∈ [s, p]` is such that no relevant gate in `(u, p]` is clean, or (B) no
relevant gate in `[s, p]` is clean. -/
theorem zones_relDepth (P : Inst) {t s p : ℕ} (ht : 1 ≤ t) (hs : 1 ≤ s)
    (hd : relDepth P p ≤ t) :
    (∃ u, s ≤ u ∧ u ≤ p ∧ IsKillerD P t u ∧
        ∀ g, u < g → g ≤ p → IsRelevant P g → ¬ IsCleanD P t g) ∨
      (∀ g, s ≤ g → g ≤ p → IsRelevant P g → ¬ IsCleanD P t g) := by
  sorry

/-- **Lemma 4.2, further claims.** In case (A), gate `u + 1` is relevant. If `x*_p = 1` (and
`D(p) ≤ t`, `p ≥ 1`), then gate `p` is relevant and not clean, and `p` is not a killer (so
`u < p` in case (A)). -/
theorem zones_relDepth_of_trace_one (P : Inst) {t p : ℕ} (ht : 1 ≤ t) (hp : 1 ≤ p)
    (hd : relDepth P p ≤ t) (h1 : trace P p = 1) :
    IsRelevant P p ∧ ¬ IsCleanD P t p ∧ ¬ IsKillerD P t p := by
  sorry

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
  sorry

/-- **Theorem 4.3, the sum `∑ N(r)`.** For `0 ≤ u < 1` the partial sums satisfy
`∑_{r<R} a_r ≤ (1-u)^{-2}`, `∑_{r<R} b_r ≤ (1-u)^{-1}`, hence
`∑_{r<R} N(r) ≤ (2-u)/(1-u)²` with `N(r) = a_r + b_r`. -/
theorem noTwoZeros_sum_le {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (R : ℕ) :
    (∑ r ∈ Finset.range R, (noTwoZeros u r).1) ≤ 1 / (1 - u) ^ 2 ∧
      (∑ r ∈ Finset.range R, (noTwoZeros u r).2) ≤ 1 / (1 - u) ∧
      (∑ r ∈ Finset.range R, ((noTwoZeros u r).1 + (noTwoZeros u r).2)) ≤
        (2 - u) / (1 - u) ^ 2 := by
  sorry

/-- **Theorem 4.3 (a), the constants.** With `ε₁ = 1/10`, `σ* = 1/6`, `σ¹* = 1/22`, `η = 1/250`
and `δ ≤ 10⁻³`: `u* = 1/4`, `k* = 1/11 + δ/10`, and
`μ = k*(1 + u* ∑N) = 16/99 + 8δ/45 ≤ σ* - η`, `μ₁ = k*u*(1 + u* ∑N) = 4/99 + 2δ/45 ≤ σ¹* - η`,
where `∑N = (2 - u*)/(1 - u*)²`. -/
theorem kp_lower_constants_a {δ : ℝ} (hδ : δ ≤ 1 / 1000) :
    let ε₁ : ℝ := 1 / 10
    let σs : ℝ := 1 / 6
    let σ1s : ℝ := 1 / 22
    let η : ℝ := 1 / 250
    let us := ε₁ + (1 - ε₁) * σs
    let ks := ε₁ * (1 / 2 + δ) + (1 - ε₁) * σ1s
    let SN := (2 - us) / (1 - us) ^ 2
    us = 1 / 4 ∧ ks = 1 / 11 + δ / 10 ∧
      ks * (1 + us * SN) = 16 / 99 + 8 * δ / 45 ∧ ks * (1 + us * SN) ≤ σs - η ∧
      ks * us * (1 + us * SN) = 4 / 99 + 2 * δ / 45 ∧ ks * us * (1 + us * SN) ≤ σ1s - η := by
  sorry

/-- **Theorem 4.3 (b), the constants.** With `ε₁ = 3/20`, `σ* = 4/17`, `σ¹* = 1/12`, `η = 1/250`
and `δ ≤ 10⁻³`: `u* = 7/20`, `k* = 7/48 + 3δ/20`, and
`μ = k*/(1-u*) = 35/156 + 3δ/13 ≤ σ* - η`, `μ₁ = k*u*/(1-u*) = 49/624 + 21δ/260 ≤ σ¹* - η`. -/
theorem kp_lower_constants_b {δ : ℝ} (hδ : δ ≤ 1 / 1000) :
    let ε₁ : ℝ := 3 / 20
    let σs : ℝ := 4 / 17
    let σ1s : ℝ := 1 / 12
    let η : ℝ := 1 / 250
    let us := ε₁ + (1 - ε₁) * σs
    let ks := ε₁ * (1 / 2 + δ) + (1 - ε₁) * σ1s
    us = 7 / 20 ∧ ks = 7 / 48 + 3 * δ / 20 ∧
      ks / (1 - us) = 35 / 156 + 3 * δ / 13 ∧ ks / (1 - us) ≤ σs - η ∧
      ks * us / (1 - us) = 49 / 624 + 21 * δ / 260 ∧ ks * us / (1 - us) ≤ σ1s - η := by
  sorry

/-- **Theorem 4.3, short zones.** `u*(2 - u*)` equals `7/16` in (a) and `231/400` in (b), and in
both cases `6 ln(1/(u*(2-u*))) ≥ 3`. Also `2η²m ≥ 6 ln n` for `η = 1/250` and
`m ≥ 187500 ln n`. -/
theorem kp_lower_short_zones :
    (1 / 4 : ℝ) * (2 - 1 / 4) = 7 / 16 ∧ (7 / 20 : ℝ) * (2 - 7 / 20) = 231 / 400 ∧
      3 ≤ 6 * Real.log (16 / 7) ∧ 3 ≤ 6 * Real.log (400 / 231) ∧
      ∀ L m : ℝ, 187500 * L ≤ m → 6 * L ≤ 2 * (1 / 250) ^ 2 * m := by
  sorry

end GC.RandomSeqNOR
