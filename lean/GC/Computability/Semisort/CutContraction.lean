import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Nat

/-!
# Exact cut contraction for binary-table sequential circuits

Manuscript 011b ("Exact Cut Contraction for P-Complete Sequential Circuits"), Theorem 4.1
(exact cut externalization), parts (a)–(c), with the reconstruction formula.

A binary-table sequential circuit with `n` gates has a bit `x_0`, a parent array `π` with
`π_i < i`, and two-input Boolean tables `G_i`; its values are `x_i = G_i(x_{i-1}, x_{π_i})`.
For a cut `b`, a gate `i > b` is internal if `π_i > b` and external otherwise. The contracted
circuit `C/b` has one gate per internal gate; its tables absorb the unary maps of the external
gates, which only read values at positions `≤ b`.
-/

namespace GC.Semisort

open Finset

/-! ### Binary-table sequential circuits -/

/-- The values of a binary-table sequential circuit (Definition 2.2): `x_0` is given and
`x_{i+1} = G_{i+1}(x_i, x_{π_{i+1}})`. (Under `IsShape` the parent is always earlier; an
out-of-range parent, which `IsShape` excludes, would be read as `false`.) -/
def circuitValue (x0 : Bool) (π : ℕ → ℕ) (G : ℕ → Bool → Bool → Bool) : ℕ → Bool
  | 0 => x0
  | i + 1 => G (i + 1) (circuitValue x0 π G i)
      (if h : π (i + 1) ≤ i then circuitValue x0 π G (π (i + 1)) else false)
termination_by i => i
decreasing_by all_goals omega

/-- `π` is the shape of a circuit with `n` gates: `π_i < i` for `1 ≤ i ≤ n`. -/
def IsShape (n : ℕ) (π : ℕ → ℕ) : Prop := ∀ i, 1 ≤ i → i ≤ n → π i < i

theorem circuitValue_zero (x0 : Bool) (π : ℕ → ℕ) (G : ℕ → Bool → Bool → Bool) :
    circuitValue x0 π G 0 = x0 := by
  rw [circuitValue]

theorem circuitValue_succ (x0 : Bool) (π : ℕ → ℕ) (G : ℕ → Bool → Bool → Bool) {i : ℕ}
    (h : π (i + 1) < i + 1) :
    circuitValue x0 π G (i + 1) =
      G (i + 1) (circuitValue x0 π G i) (circuitValue x0 π G (π (i + 1))) := by
  rw [circuitValue, dite_eq_left (by omega)]

/-! ### Internal gates, the rank `ρ`, and the maps `Φ_i` -/

section Cut

variable (π : ℕ → ℕ) (b : ℕ)

/-- `ρ(i)`: the number of internal gates `h` with `b < h ≤ i` (`π_h > b`). -/
def cutRank : ℕ → ℕ
  | 0 => 0
  | i + 1 => cutRank i + if b < i + 1 ∧ b < π (i + 1) then 1 else 0

/-- `h_r`: the `r`-th internal gate (`h_0 = b`), found as the internal gate `i ≤ n` with
`ρ(i) = r`. -/
def internalGate (n r : ℕ) : ℕ :=
  ((List.range (n + 1)).find? fun i => decide (b < i ∧ b < π i ∧ cutRank π b i = r)).getD b

/-- The last internal gate at or before `i` (or `b` if there is none), i.e. `h_{ρ(i)}`. -/
def lastInternal : ℕ → ℕ
  | 0 => b
  | i + 1 => if b < i + 1 ∧ b < π (i + 1) then i + 1 else lastInternal i

/-- The maps `Φ_i` (unary Boolean maps): `Φ_i = ψ_i ∘ ⋯ ∘ ψ_{h_{ρ(i)}+1}`, where
`ψ_j(z) = G_j(z, x_{π_j})` for an external gate `j`. It uses only the prefix values `xp`, and
only at positions `π_j ≤ b`. -/
def suffixMap (G : ℕ → Bool → Bool → Bool) (xp : ℕ → Bool) : ℕ → Bool → Bool
  | 0 => id
  | i + 1 =>
    if b < i + 1 ∧ π (i + 1) ≤ b then fun z => G (i + 1) (suffixMap G xp i z) (xp (π (i + 1)))
    else id

/-- Parent array of the contracted circuit: `π'_r = ρ(π_{h_r})` (Theorem 4.1(c)). -/
def residualParent (n r : ℕ) : ℕ := cutRank π b (π (internalGate π b n r))

/-- Tables of the contracted circuit: `G'_r(u,v) = G_{h_r}(Φ_{h_r - 1}(u), Φ_{π_{h_r}}(v))`. -/
def residualGate (G : ℕ → Bool → Bool → Bool) (xp : ℕ → Bool) (n r : ℕ) (u v : Bool) : Bool :=
  G (internalGate π b n r) (suffixMap π b G xp (internalGate π b n r - 1) u)
    (suffixMap π b G xp (π (internalGate π b n r)) v)

/-- The values `y_0 = x_b, y_1, …, y_q` of the contracted circuit `C/b`. -/
def residualValue (G : ℕ → Bool → Bool → Bool) (xp : ℕ → Bool) (n : ℕ) : ℕ → Bool :=
  circuitValue (xp b) (residualParent π b n) (residualGate π b G xp n)

end Cut

section CutLemmas

variable {π : ℕ → ℕ} {b : ℕ}

theorem cutRank_succ (i : ℕ) :
    cutRank π b (i + 1) = cutRank π b i + if b < i + 1 ∧ b < π (i + 1) then 1 else 0 := rfl

theorem cutRank_of_le {i : ℕ} (h : i ≤ b) : cutRank π b i = 0 := by
  induction i with
  | zero => rfl
  | succ i ih => rw [cutRank_succ, ih (by omega)]; simp; omega

theorem cutRank_mono {i j : ℕ} (h : i ≤ j) : cutRank π b i ≤ cutRank π b j := by
  induction j, h using Nat.le_induction with
  | base => exact le_rfl
  | succ m _ ih => rw [cutRank_succ]; omega

theorem cutRank_internal {i : ℕ} (hi : b < i) (hπ : b < π i) :
    cutRank π b i = cutRank π b (i - 1) + 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  rw [cutRank_succ, ite_eq_left ⟨hi, hπ⟩]; rfl

theorem cutRank_pos_of_internal {i : ℕ} (hi : b < i) (hπ : b < π i) : 1 ≤ cutRank π b i := by
  rw [cutRank_internal hi hπ]; omega

/-- `ρ` is strictly increasing on internal gates. -/
theorem cutRank_lt_of_internal {i j : ℕ} (hij : i < j) (hj : b < j) (hπ : b < π j) :
    cutRank π b i < cutRank π b j := by
  rw [cutRank_internal hj hπ]
  have := cutRank_mono (π := π) (b := b) (show i ≤ j - 1 by omega)
  omega

theorem lastInternal_of_le {i : ℕ} (h : i ≤ b) : lastInternal π b i = b := by
  induction i with
  | zero => rfl
  | succ i ih => simp only [lastInternal]; rw [ite_eq_right (by omega), ih (by omega)]

theorem suffixMap_of_le (G : ℕ → Bool → Bool → Bool) (xp : ℕ → Bool) {i : ℕ} (h : i ≤ b) :
    suffixMap π b G xp i = id := by
  induction i with
  | zero => rfl
  | succ i _ => simp only [suffixMap]; rw [ite_eq_right (by omega)]

/-- `lastInternal i` is `b` (and then `ρ(i) = 0`) or an internal gate with the same rank as
`i`. -/
theorem lastInternal_spec {i : ℕ} :
    (lastInternal π b i = b ∧ cutRank π b i = 0) ∨
      (b < lastInternal π b i ∧ b < π (lastInternal π b i) ∧ lastInternal π b i ≤ i ∧
        cutRank π b (lastInternal π b i) = cutRank π b i) := by
  induction i with
  | zero => exact Or.inl ⟨rfl, rfl⟩
  | succ i ih =>
    simp only [lastInternal]
    by_cases h : b < i + 1 ∧ b < π (i + 1)
    · rw [ite_eq_left h]; exact Or.inr ⟨h.1, h.2, le_rfl, rfl⟩
    · rw [ite_eq_right h, cutRank_succ, ite_eq_right h, Nat.add_zero]
      rcases ih with ih | ih
      · exact Or.inl ih
      · exact Or.inr ⟨ih.1, ih.2.1, by omega, ih.2.2.2⟩

theorem internalGate_zero (n : ℕ) : internalGate π b n 0 = b := by
  unfold internalGate
  rw [show ((List.range (n + 1)).find? fun i =>
      decide (b < i ∧ b < π i ∧ cutRank π b i = 0)) = none from ?_]
  · rfl
  rw [List.find?_eq_none]
  intro i _ hi
  simp only [decide_eq_true_eq] at hi
  have := cutRank_pos_of_internal (π := π) hi.1 hi.2.1
  omega

/-- `h_{ρ(j)} = j` for every internal gate `j ≤ n`. -/
theorem internalGate_cutRank {n j : ℕ} (hjn : j ≤ n) (hj : b < j) (hπ : b < π j) :
    internalGate π b n (cutRank π b j) = j := by
  unfold internalGate
  have hex : ((List.range (n + 1)).find? fun i =>
      decide (b < i ∧ b < π i ∧ cutRank π b i = cutRank π b j)).isSome := by
    rw [List.find?_isSome]
    exact ⟨j, List.mem_range.2 (by omega), by simp [hj, hπ]⟩
  obtain ⟨j', hj'⟩ := Option.isSome_iff_exists.1 hex
  rw [hj', Option.getD_some]
  have hp := List.find?_some hj'
  simp only [decide_eq_true_eq] at hp
  obtain ⟨h1, h2, h3⟩ := hp
  rcases lt_trichotomy j' j with h | h | h
  · have := cutRank_lt_of_internal (π := π) h hj hπ; omega
  · exact h
  · have := cutRank_lt_of_internal (π := π) h h1 h2; omega

/-- `h_{ρ(i)}` is the last internal gate at or before `i`. -/
theorem internalGate_cutRank_eq_lastInternal {n i : ℕ} (hin : i ≤ n) :
    internalGate π b n (cutRank π b i) = lastInternal π b i := by
  rcases lastInternal_spec (π := π) (b := b) (i := i) with h | h
  · rw [h.2, h.1, internalGate_zero]
  · rw [← h.2.2.2, internalGate_cutRank (by omega) h.1 h.2.1]

/-- Every rank `r ∈ [1, ρ(m)]` is the rank of an internal gate `≤ m`. -/
theorem exists_internal_of_le_cutRank {m r : ℕ} (hr1 : 1 ≤ r) (hr : r ≤ cutRank π b m) :
    ∃ j ≤ m, b < j ∧ b < π j ∧ cutRank π b j = r := by
  induction m with
  | zero => simp [cutRank] at hr; omega
  | succ m ih =>
    rw [cutRank_succ] at hr
    by_cases h : b < m + 1 ∧ b < π (m + 1)
    · rw [ite_eq_left h] at hr
      rcases Nat.lt_or_ge r (cutRank π b m + 1) with h' | h'
      · obtain ⟨j, hj, hj'⟩ := ih (by omega); exact ⟨j, by omega, hj'⟩
      · exact ⟨m + 1, le_rfl, h.1, h.2, by rw [cutRank_succ, ite_eq_left h]; omega⟩
    · rw [ite_eq_right h] at hr
      obtain ⟨j, hj, hj'⟩ := ih (by omega); exact ⟨j, by omega, hj'⟩

/-- **The internal gates.** For `1 ≤ r ≤ q = ρ(n)`, `h_r` is an internal gate `≤ n` of rank
`r`. (Also `h_0 = b`, `internalGate_zero`, and `r ↦ h_r` is strictly increasing,
`internalGate_strictMono`.) -/
theorem internalGate_spec {n r : ℕ} (hr1 : 1 ≤ r) (hr : r ≤ cutRank π b n) :
    b < internalGate π b n r ∧ internalGate π b n r ≤ n ∧ b < π (internalGate π b n r) ∧
      cutRank π b (internalGate π b n r) = r := by
  obtain ⟨j, hjn, hj, hπj, rfl⟩ := exists_internal_of_le_cutRank hr1 hr
  rw [internalGate_cutRank hjn hj hπj]
  exact ⟨hj, hjn, hπj, rfl⟩

/-- The internal gates are enumerated in increasing order. -/
theorem internalGate_strictMono {n r s : ℕ} (hr1 : 1 ≤ r) (hrs : r < s)
    (hs : s ≤ cutRank π b n) : internalGate π b n r < internalGate π b n s := by
  obtain ⟨h1, h2, h3, h4⟩ := internalGate_spec (π := π) hr1 (by omega : r ≤ cutRank π b n)
  obtain ⟨h1', h2', h3', h4'⟩ := internalGate_spec (π := π) (by omega : 1 ≤ s) hs
  by_contra hne
  have := cutRank_mono (π := π) (b := b) (show internalGate π b n s ≤ internalGate π b n r by
    omega)
  omega

/-- The number `q(b)` of gates of `C/b` is `|{i ∈ (b, n] : π_i > b}|`. -/
theorem cutRank_eq_card (n : ℕ) :
    cutRank π b n = #((Ioc b n).filter fun i => b < π i) := by
  induction n with
  | zero => simp [cutRank]
  | succ n ih =>
    rw [cutRank_succ, ih]
    by_cases hb : b < n + 1
    · have hI : Ioc b (n + 1) = insert (n + 1) (Ioc b n) := by
        ext x; simp only [mem_Ioc, mem_insert]; omega
      rw [hI, filter_insert]
      by_cases hπ : b < π (n + 1)
      · rw [ite_eq_left ⟨hb, hπ⟩, ite_eq_left hπ, card_insert_of_notMem (by simp)]
      · rw [ite_eq_right (fun h => hπ h.2), ite_eq_right hπ, Nat.add_zero]
    · rw [ite_eq_right (fun h => hb h.1)]
      rw [Finset.Ioc_eq_empty (by omega), Finset.Ioc_eq_empty (by omega)]
      simp

end CutLemmas

/-! ### Theorem 4.1 -/

section Main

variable {x0 : Bool} {π : ℕ → ℕ} {G : ℕ → Bool → Bool → Bool} {n b : ℕ} {xp : ℕ → Bool}

/-- Along a segment of external gates, `x_i = Φ_i(x_{h_{ρ(i)}})`. -/
theorem value_eq_suffixMap_lastInternal (hπ : IsShape n π)
    (hxp : ∀ j ≤ b, xp j = circuitValue x0 π G j) {i : ℕ} (hbi : b ≤ i) (hin : i ≤ n) :
    circuitValue x0 π G i =
      suffixMap π b G xp i (circuitValue x0 π G (lastInternal π b i)) := by
  induction i, hbi using Nat.le_induction with
  | base => rw [lastInternal_of_le le_rfl, suffixMap_of_le G xp le_rfl]; rfl
  | succ m hm ih =>
    have hpar := hπ (m + 1) (by omega) hin
    simp only [suffixMap, lastInternal]
    by_cases h : b < m + 1 ∧ b < π (m + 1)
    · rw [ite_eq_left h, ite_eq_right (by omega)]; rfl
    · rw [ite_eq_right h, ite_eq_left ⟨by omega, by omega⟩, circuitValue_succ x0 π G hpar,
        ih (by omega), hxp _ (by omega)]

/-- **Theorem 4.1 (exact cut externalization).** Let `C` be a binary-table sequential circuit
with `n` gates (shape `π`, tables `G`, values `x`), let `b` be a cut (the paper takes
`b ∈ [0, n-1]`; the statement holds for every `b`) and let `xp` agree with
`x` on `[0, b]` (the given prefix values). Let `q = ρ(n)` be the number of internal gates. Then
the contracted circuit `C/b` (start value `x_b`, parents `π'`, tables `G'`, values `y`) has a
valid shape on `q` gates and
* (a) `y_r = x_{h_r}` for `r = 0, …, q`;
* (b) `x_i = Φ_i(y_{ρ(i)})` for every `i ∈ [b, n]` (reconstruction of the suffix values);
* (c) `π'_r = ρ(π_{h_r})` for `r = 1, …, q`.
The circuit `C/b` and the maps `Φ_i` are built from `π`, `G`, `b` and `xp` only. -/
theorem exact_cut_externalization (hπ : IsShape n π)
    (hxp : ∀ j ≤ b, xp j = circuitValue x0 π G j) :
    IsShape (cutRank π b n) (residualParent π b n) ∧
    (∀ r ≤ cutRank π b n,
      residualValue π b G xp n r = circuitValue x0 π G (internalGate π b n r)) ∧
    (∀ i, b ≤ i → i ≤ n →
      circuitValue x0 π G i = suffixMap π b G xp i (residualValue π b G xp n (cutRank π b i))) ∧
    (∀ r, 1 ≤ r → r ≤ cutRank π b n →
      residualParent π b n r = cutRank π b (π (internalGate π b n r))) := by
  set q := cutRank π b n
  set x := circuitValue x0 π G
  set y := residualValue π b G xp n
  -- shape of `C/b`
  have hshape : IsShape q (residualParent π b n) := by
    intro r hr1 hrq
    obtain ⟨h1, h2, h3, h4⟩ := internalGate_spec (π := π) hr1 hrq
    have hpar := hπ _ (by omega) h2
    unfold residualParent
    have := cutRank_mono (π := π) (b := b)
      (show π (internalGate π b n r) ≤ internalGate π b n r - 1 by omega)
    rw [cutRank_internal h1 h3] at h4
    omega
  -- reconstruction through `lastInternal`
  have hrec : ∀ i, b ≤ i → i ≤ n →
      suffixMap π b G xp i (x (internalGate π b n (cutRank π b i))) = x i := by
    intro i hbi hin
    rw [internalGate_cutRank_eq_lastInternal hin]
    exact (value_eq_suffixMap_lastInternal hπ hxp hbi hin).symm
  -- part (a)
  have ha : ∀ r ≤ q, y r = x (internalGate π b n r) := by
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
      intro hrq
      rcases Nat.eq_zero_or_pos r with rfl | hr
      · show circuitValue (xp b) _ _ 0 = _
        rw [circuitValue_zero, internalGate_zero, hxp b le_rfl]
      obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
      have hps := hshape (s + 1) (by omega) hrq
      obtain ⟨h1, h2, h3, h4⟩ := internalGate_spec (π := π) (by omega : 1 ≤ s + 1) hrq
      set h := internalGate π b n (s + 1) with hh
      have hpar := hπ h (by omega) h2
      show circuitValue (xp b) _ _ (s + 1) = _
      rw [circuitValue_succ _ _ _ hps]
      change residualGate π b G xp n (s + 1) (y s) (y (residualParent π b n (s + 1))) = _
      rw [ih s (by omega) (by omega), ih _ hps (by omega)]
      unfold residualGate residualParent
      rw [← hh]
      have hrk : cutRank π b (h - 1) = s := by rw [cutRank_internal h1 h3] at h4; omega
      have e1 := hrec (h - 1) (by omega) (by omega)
      rw [hrk] at e1
      rw [e1, hrec (π h) (by omega) (by omega)]
      obtain ⟨k, hk⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
      rw [hk] at hpar ⊢
      rw [Nat.add_sub_cancel]
      exact (circuitValue_succ x0 π G hpar).symm
  refine ⟨hshape, ha, ?_, fun r _ _ => rfl⟩
  -- part (b)
  intro i hbi hin
  rw [ha _ (cutRank_mono hin), hrec i hbi hin]

end Main

end GC.Semisort
