import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Logic.Function.Iterate
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Comparator challenge for manuscript 001c (A P-Complete Problem in Average-Case AC1 and SC2). Definitions are copied verbatim from
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

/-- A dependency step from `p` to `q`: some non-NOT gate `k` with `max(ϱ(p), 1) ≤ k ≤ p` and
`q = jₖ`. -/
def DepStep (P : Inst) (p q : ℕ) : Prop :=
  ∃ k, max (lastReset P p) 1 ≤ k ∧ k ≤ p ∧ ¬ IsNot P k ∧ P.j k = q

/-- `pos 0, pos 1, …, pos L` is a dependency chain of length `L`. -/
def IsDepChain (P : Inst) (L : ℕ) (pos : ℕ → ℕ) : Prop :=
  ∀ s < L, DepStep P (pos s) (pos (s + 1))

/-- The reset decomposition: `x*ᵢ = x*_{ϱ(i)} ⊕ ((i - ϱ(i)) mod 2)`, where `x*₀ = 1` and
`x*ᵣ = 0` at a reset. -/
theorem trace_eq_lastReset (P : Inst) (i : ℕ) :
    trace P i = (if lastReset P i = 0 then 1 else 0) + ((i - lastReset P i : ℕ) : ZMod 2) := by
  sorry

/-- **Lemma 3.2 (rounds equal dependency depth).** For every `t ≥ 0`,
`K_t = {i : d(i) ≤ t}`, and `vᵢ = x*ᵢ` for every `i ∈ K_t`. -/
theorem kp_rounds_eq_depth (P : Inst) (t : ℕ) :
    (kpIter P t).known = {i | depth P i ≤ t} ∧
      ∀ i ∈ (kpIter P t).known, (kpIter P t).val i = trace P i := by
  sorry

/-- Consequence of Lemma 3.2: after `R` rounds the iteration knows all of `[0, n]` (and then its
values are the trace) iff `max_{i ≤ n} d(i) ≤ R`. -/
theorem kp_success_iff (P : Inst) (R n : ℕ) :
    (∀ i ≤ n, i ∈ (kpIter P R).known) ↔ ∀ i ≤ n, depth P i ≤ R := by
  sorry

/-- If `d(p) ≥ L + 1`, there is a dependency chain of length `L` from `p` with
`d(P_s) = d(p) - s`. -/
theorem exists_depChain (P : Inst) (p : ℕ) :
    ∀ L, L + 1 ≤ depth P p → ∃ pos : ℕ → ℕ, pos 0 = p ∧ IsDepChain P L pos ∧
      ∀ s ≤ L, depth P (pos s) = depth P p - s := by
  sorry

/-- **Theorem 3.4, deterministic first step.** Let `g₀ ≥ 1`. If no dependency chain of length `L`
has all its positions at least `g₀` (the event `Γ`), then `max_i d(i) < L + g₀`, and hence, by
Lemma 3.2, the Kleene–prefix iteration knows every position after `L + g₀ - 1` rounds. -/
theorem kp_finishes_of_no_long_chain (P : Inst) {L g₀ : ℕ} (hg₀ : 1 ≤ g₀)
    (hΓ : ¬ ∃ pos : ℕ → ℕ, IsDepChain P L pos ∧ ∀ s ≤ L, g₀ ≤ pos s) :
    (∀ i, depth P i < L + g₀) ∧ ∀ i, i ∈ (kpIter P (L + g₀ - 1)).known := by
  sorry

/-- **Theorem 3.4, the threshold `ε_K`.** For `0 < ε ≤ 1`, there are `η ∈ (0, ε/(2+ε))` and
`λ > 0` with `θ = (ε/(λ+1) + 1 - ε)/(ε c) < 1`, `c = ε/(2+ε) - η`, if and only if
`ε > ε_K = (√17 - 1)/4`. -/
theorem epsK_threshold {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (∃ η lam : ℝ, 0 < η ∧ η < ε / (2 + ε) ∧ 0 < lam ∧
        (ε / (lam + 1) + 1 - ε) / (ε * (ε / (2 + ε) - η)) < 1) ↔
      (Real.sqrt 17 - 1) / 4 < ε := by
  sorry

/-- **Lemma 3.5, the limit equation.** Let `0 ≤ ε ≤ 1`, `L(μ) = ε(1-μ)/(1+ε(1-μ))` and
`U(ℓ) = (1-εℓ)/(2-εℓ)`. If `ℓ = L(μ)`, `μ = U(ℓ)` and `0 ≤ ℓ ≤ 1`, then
`εℓ = (2 + ε - √(4 + 4ε - 3ε²))/2`. -/
theorem fixed_point_density {ε ℓ μ : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hℓ0 : 0 ≤ ℓ) (hℓ1 : ℓ ≤ 1)
    (hL : ℓ = ε * (1 - μ) / (1 + ε * (1 - μ))) (hU : μ = (1 - ε * ℓ) / (2 - ε * ℓ)) :
    ε * ℓ = (2 + ε - Real.sqrt (4 + 4 * ε - 3 * ε ^ 2)) / 2 := by
  sorry

/-- **Theorem 3.6, the threshold `ε_B`.** For `0 ≤ ε ≤ 1`, `f(ε) = εℓ*(ε) - (1-ε) > 0` with
`εℓ* = (2 + ε - √(4 + 4ε - 3ε²))/2` iff `ε > ε_B = (1 + √13)/6`. -/
theorem epsB_threshold {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    1 - ε < (2 + ε - Real.sqrt (4 + 4 * ε - 3 * ε ^ 2)) / 2 ↔ (1 + Real.sqrt 13) / 6 < ε := by
  sorry

/-- **Theorem 3.9, the threshold `3/4`.** With `ϖ(ε) = (2ε + 1 - √(4ε + 1))/(2ε)` the root in
`(0, 1/2)` of `ϖ = ε(1 - ϖ)²`: for `0 < ε`, `εϖ(ε) > 1 - ε` iff `ε > 3/4`; and
`ϖ(3/4) = 1/3`. -/
theorem varpi_threshold {ε : ℝ} (hε0 : 0 < ε) :
    (1 - ε < ε * ((2 * ε + 1 - Real.sqrt (4 * ε + 1)) / (2 * ε)) ↔ 3 / 4 < ε) ∧
      (2 * (3 / 4 : ℝ) + 1 - Real.sqrt (4 * (3 / 4) + 1)) / (2 * (3 / 4)) = 1 / 3 := by
  sorry

end GC.RandomSeqNOR
