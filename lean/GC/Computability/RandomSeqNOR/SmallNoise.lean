import GC.Computability.RandomSeqNOR.KleenePrefix
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Small noise defeats the Kleene–prefix iteration (manuscript 001d): deterministic core

* Lemma 3.5 for the depth `d` (switch characterisation): `depth_one`,
  `depth_succ_of_isReset`, `depth_succ_of_isNot`, `depth_succ_of_other`, `depth_switch`.
* Lemma 4.2 for `d` (non-deep positions): `zones_depth`, `zones_depth_of_trace_one`.
* The over-approximation step of Theorem 4.3(b): `overapprox_depth`.
* The exact numbers of Theorem 4.3: `noTwoZeros_sum_le`, `kp_lower_constants_a`,
  `kp_lower_constants_b`, `kp_lower_short_zones`.
-/

namespace GC.RandomSeqNOR

/-! ### Lemma 3.5 (a) for `d` -/

theorem lastReset_succ_of_isReset (P : Inst) {i : ℕ} (h : IsReset P (i + 1)) :
    lastReset P (i + 1) = i + 1 :=
  Nat.findGreatest_eq (P := fun r => r = 0 ∨ IsReset P r) (Or.inr h)

theorem lastReset_succ_of_not_isReset (P : Inst) {i : ℕ} (h : ¬ IsReset P (i + 1)) :
    lastReset P (i + 1) = lastReset P i :=
  Nat.findGreatest_of_not (P := fun r => r = 0 ∨ IsReset P r) (by simp [h])

private theorem eq_of_le_succ_iff {x y : ℕ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (h : ∀ t, x ≤ t + 1 ↔ y ≤ t + 1) : x = y := by
  apply le_antisymm
  · have := (h (y - 1)).2 (by omega); omega
  · have := (h (x - 1)).1 (by omega); omega

theorem isNot_one (P : Inst) : IsNot P 1 := by unfold IsNot; rw [j_one]

theorem not_isReset_of_isNot (P : Inst) {k : ℕ} (h : IsNot P k) : ¬ IsReset P k :=
  fun h' => h'.2.1 h

/-- **Lemma 3.5 (a), for `d`:** `d(1) = 1`. -/
theorem depth_one (P : Inst) : depth P 1 = 1 := by
  have h1 := depth_le_self P 1
  have h2 := depth_pos P one_pos
  omega

/-- **Lemma 3.5 (a), for `d`:** at a reset `i ≥ 2`, `d(i) = 1 + d(jᵢ)`. -/
theorem depth_succ_of_isReset (P : Inst) {i : ℕ} (h : IsReset P (i + 1)) :
    depth P (i + 1) = 1 + depth P (P.j (i + 1)) := by
  apply eq_of_le_succ_iff (depth_pos P (Nat.succ_pos i)) (by omega)
  intro t
  rw [depth_le_succ_iff, lastReset_succ_of_isReset P h]
  constructor
  · intro hk
    have := hk (i + 1) (by omega) le_rfl h.2.1
    omega
  · intro hk k hk1 hk2 _
    rw [show k = i + 1 by omega]; omega

/-- **Lemma 3.5 (a), for `d`:** at a NOT gate `i ≥ 2`, `d(i) = d(i-1)`. -/
theorem depth_succ_of_isNot (P : Inst) {i : ℕ} (hi : 1 ≤ i) (h : IsNot P (i + 1)) :
    depth P (i + 1) = depth P i := by
  apply eq_of_le_succ_iff (depth_pos P (Nat.succ_pos i)) (depth_pos P hi)
  intro t
  rw [depth_le_succ_iff, depth_le_succ_iff,
    lastReset_succ_of_not_isReset P (not_isReset_of_isNot P h)]
  constructor
  · intro hk k hk1 hk2 hk3; exact hk k hk1 (by omega) hk3
  · intro hk k hk1 hk2 hk3
    rcases Nat.lt_or_ge k (i + 1) with hlt | hge
    · exact hk k hk1 (by omega) hk3
    · exact absurd (show k = i + 1 by omega ▸ h) hk3

/-- **Lemma 3.5 (a), for `d`:** at a gate `i ≥ 2` that is neither a reset nor a NOT gate,
`d(i) = max(d(i-1), 1 + d(jᵢ))`. -/
theorem depth_succ_of_other (P : Inst) {i : ℕ} (hi : 1 ≤ i) (hr : ¬ IsReset P (i + 1))
    (hn : ¬ IsNot P (i + 1)) :
    depth P (i + 1) = max (depth P i) (1 + depth P (P.j (i + 1))) := by
  apply eq_of_le_succ_iff (depth_pos P (Nat.succ_pos i)) (by omega)
  intro t
  rw [depth_le_succ_iff, max_le_iff, depth_le_succ_iff, lastReset_succ_of_not_isReset P hr]
  have hρ := lastReset_le P i
  constructor
  · intro hk
    exact ⟨fun k hk1 hk2 hk3 => hk k hk1 (by omega) hk3,
      by have := hk (i + 1) (by omega) le_rfl hn; omega⟩
  · rintro ⟨hk, hj⟩ k hk1 hk2 hk3
    rcases Nat.lt_or_ge k (i + 1) with hlt | hge
    · exact hk k hk1 (by omega) hk3
    · rw [show k = i + 1 by omega]; omega

/-! ### Lemma 3.5 (b), for `d` -/

/-- **Lemma 3.5 (b), for `d`.** Let `t ≥ 1` and `i ≥ 1`. Then `d(i) ≥ t + 1` iff there is a gate
`a ≤ i`, not a NOT gate, with `d(j_a) ≥ t` and with `d(j_g) ≥ t` for every reset `g ∈ (a, i]`. -/
theorem depth_switch (P : Inst) {t : ℕ} (ht : 1 ≤ t) :
    ∀ i, 1 ≤ i → (t + 1 ≤ depth P i ↔
      ∃ a, 1 ≤ a ∧ a ≤ i ∧ ¬ IsNot P a ∧ t ≤ depth P (P.j a) ∧
        ∀ g, a < g → g ≤ i → IsReset P g → t ≤ depth P (P.j g)) := by
  intro i hi
  induction i, hi using Nat.le_induction with
  | base =>
    rw [depth_one]
    constructor
    · intro h; omega
    · rintro ⟨a, ha1, ha2, ha3, -⟩
      exact absurd (show a = 1 by omega ▸ isNot_one P) ha3
  | succ i hi ih =>
    by_cases hr : IsReset P (i + 1)
    · rw [depth_succ_of_isReset P hr]
      constructor
      · intro h
        exact ⟨i + 1, by omega, le_rfl, hr.2.1, by omega, fun g hg1 hg2 _ => by omega⟩
      · rintro ⟨a, ha1, ha2, ha3, ha4, ha5⟩
        rcases Nat.lt_or_ge a (i + 1) with hlt | hge
        · have := ha5 (i + 1) hlt le_rfl hr; omega
        · rw [show a = i + 1 by omega] at ha4; omega
    · by_cases hn : IsNot P (i + 1)
      · rw [depth_succ_of_isNot P hi hn, ih]
        constructor
        · rintro ⟨a, ha1, ha2, ha3, ha4, ha5⟩
          exact ⟨a, ha1, by omega, ha3, ha4, fun g hg1 hg2 hg3 => by
            rcases Nat.lt_or_ge g (i + 1) with hlt | hge
            · exact ha5 g hg1 (by omega) hg3
            · exact absurd (show g = i + 1 by omega ▸ hg3) hr⟩
        · rintro ⟨a, ha1, ha2, ha3, ha4, ha5⟩
          rcases Nat.lt_or_ge a (i + 1) with hlt | hge
          · exact ⟨a, ha1, by omega, ha3, ha4, fun g hg1 hg2 hg3 => ha5 g hg1 (by omega) hg3⟩
          · exact absurd (show a = i + 1 by omega ▸ hn) ha3
      · rw [depth_succ_of_other P hi hr hn, le_max_iff, ih]
        constructor
        · rintro (⟨a, ha1, ha2, ha3, ha4, ha5⟩ | h)
          · exact ⟨a, ha1, by omega, ha3, ha4, fun g hg1 hg2 hg3 => by
              rcases Nat.lt_or_ge g (i + 1) with hlt | hge
              · exact ha5 g hg1 (by omega) hg3
              · exact absurd (show g = i + 1 by omega ▸ hg3) hr⟩
          · exact ⟨i + 1, by omega, le_rfl, hn, by omega, fun g hg1 hg2 _ => by omega⟩
        · rintro ⟨a, ha1, ha2, ha3, ha4, ha5⟩
          rcases Nat.lt_or_ge a (i + 1) with hlt | hge
          · exact Or.inl ⟨a, ha1, by omega, ha3, ha4, fun g hg1 hg2 hg3 => ha5 g hg1 (by omega) hg3⟩
          · rw [show a = i + 1 by omega] at ha4; right; omega

/-! ### Lemma 4.2 for `d`: non-deep positions -/

/-- Gate `g` is *clean* (for the threshold `t`): not a NOT gate and `d(j_g) ≥ t`. -/
def IsClean (P : Inst) (t g : ℕ) : Prop := ¬ IsNot P g ∧ t ≤ depth P (P.j g)

/-- Gate `g` is a *killer* (for the threshold `t`): a reset with `d(j_g) < t`. -/
def IsKiller (P : Inst) (t g : ℕ) : Prop := IsReset P g ∧ depth P (P.j g) < t

/-- **Lemma 4.2 for `d` (non-deep positions).** Let `t ≥ 1` and `1 ≤ s ≤ p`. If `d(p) ≤ t`, then
(A) some killer `u ∈ [s, p]` is such that no gate in `(u, p]` is clean, or (B) no gate in
`[s, p]` is clean. -/
theorem zones_depth (P : Inst) {t s p : ℕ} (ht : 1 ≤ t) (hs : 1 ≤ s)
    (hd : depth P p ≤ t) :
    (∃ u, s ≤ u ∧ u ≤ p ∧ IsKiller P t u ∧ ∀ g, u < g → g ≤ p → ¬ IsClean P t g) ∨
      (∀ g, s ≤ g → g ≤ p → ¬ IsClean P t g) := by
  classical
  by_cases hB : ∀ g, s ≤ g → g ≤ p → ¬ IsClean P t g
  · exact Or.inr hB
  · left
    push Not at hB
    obtain ⟨g₀, hg₀1, hg₀2, hg₀3⟩ := hB
    -- `a`: the last clean gate in `[s, p]`
    set a := Nat.findGreatest (fun g => s ≤ g ∧ IsClean P t g) p with ha
    have haspec : s ≤ a ∧ IsClean P t a :=
      Nat.findGreatest_spec (P := fun g => s ≤ g ∧ IsClean P t g) hg₀2 ⟨hg₀1, hg₀3⟩
    have hap : a ≤ p := Nat.findGreatest_le p
    have hagreat : ∀ g, a < g → g ≤ p → ¬ IsClean P t g := fun g h1 h2 hc =>
      Nat.findGreatest_is_greatest (P := fun g => s ≤ g ∧ IsClean P t g) h1 h2
        ⟨by omega, hc⟩
    -- some killer lies in `(a, p]`, otherwise `d(p) ≥ t + 1`
    have hk : ∃ g, a < g ∧ g ≤ p ∧ IsKiller P t g := by
      by_contra hc
      push Not at hc
      have := (depth_switch P ht p (by omega)).2
        ⟨a, by omega, hap, haspec.2.1, haspec.2.2, fun g hg1 hg2 hg3 => by
          by_contra hlt; push Not at hlt
          exact hc g hg1 hg2 ⟨hg3, hlt⟩⟩
      omega
    obtain ⟨g₁, hg₁1, hg₁2, hg₁3⟩ := hk
    -- `u`: the last killer in `(a, p]`
    set u := Nat.findGreatest (fun g => a < g ∧ IsKiller P t g) p with hu
    have huspec : a < u ∧ IsKiller P t u :=
      Nat.findGreatest_spec (P := fun g => a < g ∧ IsKiller P t g) hg₁2 ⟨hg₁1, hg₁3⟩
    have hup : u ≤ p := Nat.findGreatest_le p
    exact ⟨u, by omega, hup, huspec.2, fun g hg1 hg2 => hagreat g (by omega) hg2⟩

/-- **Lemma 4.2 for `d`, last claim.** If moreover `x*_p = 1`, then `p` is not clean, and `p` is
not a killer (so `u < p` in case (A)). -/
theorem zones_depth_of_trace_one (P : Inst) {t p : ℕ} (ht : 1 ≤ t) (hp : 1 ≤ p)
    (hd : depth P p ≤ t) (h1 : trace P p = 1) :
    ¬ IsClean P t p ∧ ¬ IsKiller P t p := by
  refine ⟨fun hc => ?_, fun hk => ?_⟩
  · have := (depth_switch P ht p hp).2
      ⟨p, hp, le_rfl, hc.1, hc.2, fun g hg1 hg2 _ => by omega⟩
    omega
  · rw [trace_of_isReset P hk.1] at h1; exact absurd h1 (by decide)

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
  have hUc : ∀ g, s ≤ g → g ≤ p → ¬ IsClean P t g → U g := fun g h1 h2 h3 => by
    by_contra hc; exact h3 (hU g h1 h2 hc)
  have main := zones_depth P ht hs hd
  refine ⟨?_, fun h1 => ?_⟩
  · rcases main with ⟨u, hu1, hu2, hu3, hu4⟩ | hB
    · exact Or.inl ⟨u, hu1, hu2, hK u hu1 hu2 hu3, fun g hg1 hg2 =>
        hUc g (by omega) hg2 (hu4 g hg1 hg2)⟩
    · exact Or.inr fun g hg1 hg2 => hUc g hg1 hg2 (hB g hg1 hg2)
  · obtain ⟨hnc, hnk⟩ := zones_depth_of_trace_one P ht (by omega) hd h1
    refine ⟨hUc p hsp le_rfl hnc, ?_⟩
    rcases main with ⟨u, hu1, hu2, hu3, hu4⟩ | hB
    · have hup : u ≠ p := fun h => hnk (h ▸ hu3)
      exact Or.inl ⟨u, hu1, by omega, hK u hu1 hu2 hu3, fun g hg1 hg2 =>
        hUc g (by omega) hg2 (hu4 g hg1 hg2)⟩
    · exact Or.inr fun g hg1 hg2 => hUc g hg1 hg2 (hB g hg1 hg2)

/-! ### The numbers of Theorem 4.3 -/

/-- The recursion `a₀ = 1`, `b₀ = 0`, `a_{r+1} = u(a_r + b_r)`, `b_{r+1} = (1-u) a_r` of the
proof of Theorem 4.3 (probabilities that `r` gates have no two consecutive `Û = 0` and that the
last one has `Û = 1`, resp. `Û = 0`). -/
def noTwoZeros (u : ℝ) : ℕ → ℝ × ℝ
  | 0 => (1, 0)
  | r + 1 => (u * ((noTwoZeros u r).1 + (noTwoZeros u r).2), (1 - u) * (noTwoZeros u r).1)

/-- **Theorem 4.3, the sum `∑ N(r)`.** For `0 ≤ u < 1` the partial sums satisfy
`∑_{r<R} a_r ≤ (1-u)^{-2}`, `∑_{r<R} b_r ≤ (1-u)^{-1}`, hence
`∑_{r<R} N(r) ≤ (2-u)/(1-u)²` with `N(r) = a_r + b_r`. -/
theorem noTwoZeros_sum_le {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (R : ℕ) :
    (∑ r ∈ Finset.range R, (noTwoZeros u r).1) ≤ 1 / (1 - u) ^ 2 ∧
      (∑ r ∈ Finset.range R, (noTwoZeros u r).2) ≤ 1 / (1 - u) ∧
      (∑ r ∈ Finset.range R, ((noTwoZeros u r).1 + (noTwoZeros u r).2)) ≤
        (2 - u) / (1 - u) ^ 2 := by
  have h1u : 0 < 1 - u := by linarith
  have key : ∀ R, (∑ r ∈ Finset.range R, (noTwoZeros u r).1) ≤ 1 / (1 - u) ^ 2 ∧
      (∑ r ∈ Finset.range R, (noTwoZeros u r).2) ≤ 1 / (1 - u) := by
    intro R
    induction R with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      exact ⟨by positivity, by positivity⟩
    | succ R ih =>
      rw [Finset.sum_range_succ', Finset.sum_range_succ']
      simp only [noTwoZeros]
      rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib]
      obtain ⟨hA, hB⟩ := ih
      constructor
      · have : u * ((∑ r ∈ Finset.range R, (noTwoZeros u r).1) +
            ∑ r ∈ Finset.range R, (noTwoZeros u r).2) ≤ u * (1 / (1 - u) ^ 2 + 1 / (1 - u)) :=
          mul_le_mul_of_nonneg_left (add_le_add hA hB) hu0
        have e : 1 + u * (1 / (1 - u) ^ 2 + 1 / (1 - u)) = 1 / (1 - u) ^ 2 := by
          field_simp; ring
        linarith
      · have : (1 - u) * ∑ r ∈ Finset.range R, (noTwoZeros u r).1 ≤
            (1 - u) * (1 / (1 - u) ^ 2) := mul_le_mul_of_nonneg_left hA h1u.le
        have e : (1 - u) * (1 / (1 - u) ^ 2) = 1 / (1 - u) := by field_simp
        linarith
  obtain ⟨hA, hB⟩ := key R
  refine ⟨hA, hB, ?_⟩
  rw [Finset.sum_add_distrib]
  have e : 1 / (1 - u) ^ 2 + 1 / (1 - u) = (2 - u) / (1 - u) ^ 2 := by field_simp; ring
  linarith

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
  intro ε₁ σs σ1s η us ks SN
  have hus : us = 1 / 4 := by norm_num [us, ε₁, σs]
  have hks : ks = 1 / 11 + δ / 10 := by simp only [ks, ε₁, σ1s]; ring
  have hSN : SN = 28 / 9 := by simp only [SN]; rw [hus]; norm_num
  refine ⟨hus, hks, ?_, ?_, ?_, ?_⟩
  · rw [hks, hus, hSN]; ring
  · rw [hks, hus, hSN]; simp only [σs, η]; nlinarith
  · rw [hks, hus, hSN]; ring
  · rw [hks, hus, hSN]; simp only [σ1s, η]; nlinarith

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
  intro ε₁ σs σ1s η us ks
  have hus : us = 7 / 20 := by norm_num [us, ε₁, σs]
  have hks : ks = 7 / 48 + 3 * δ / 20 := by simp only [ks, ε₁, σ1s]; ring
  have e1 : ks / (1 - us) = 35 / 156 + 3 * δ / 13 := by rw [hks, hus]; ring
  have e2 : ks * us / (1 - us) = 49 / 624 + 21 * δ / 260 := by rw [hks, hus]; ring
  refine ⟨hus, hks, e1, ?_, e2, ?_⟩
  · rw [e1]; simp only [σs, η]; linarith
  · rw [e2]; simp only [σ1s, η]; linarith

/-- **Theorem 4.3, short zones.** `u*(2 - u*)` equals `7/16` in (a) and `231/400` in (b), and in
both cases `6 ln(1/(u*(2-u*))) ≥ 3`. Also `2η²m ≥ 6 ln n` for `η = 1/250` and
`m ≥ 187500 ln n`. -/
theorem kp_lower_short_zones :
    (1 / 4 : ℝ) * (2 - 1 / 4) = 7 / 16 ∧ (7 / 20 : ℝ) * (2 - 7 / 20) = 231 / 400 ∧
      3 ≤ 6 * Real.log (16 / 7) ∧ 3 ≤ 6 * Real.log (400 / 231) ∧
      ∀ L m : ℝ, 187500 * L ≤ m → 6 * L ≤ 2 * (1 / 250) ^ 2 * m := by
  have hexp : Real.exp (1 / 2) < 1.6488 := by
    have h := Real.exp_one_lt_d9
    have h2 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
      rw [← Real.exp_nat_mul]; norm_num
    nlinarith [Real.exp_pos (1 / 2)]
  have hlog : ∀ x : ℝ, 1.6488 ≤ x → 1 / 2 ≤ Real.log x := by
    intro x hx
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_⟩
  · have := hlog (16 / 7) (by norm_num); linarith
  · have := hlog (400 / 231) (by norm_num); linarith
  · intro L m h; nlinarith

end GC.RandomSeqNOR
