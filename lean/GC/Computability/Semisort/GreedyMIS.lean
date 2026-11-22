import GC.Computability.Semisort.Span

/-!
# Sequential NOR as lexicographically-first greedy maximal independent set

Manuscript 011b, Proposition 3.1. For a parent array `π` with `n` gates, `H_π` is the graph on
`{0, …, n}` with edges `{i-1, i}` and `{π_i, i}` (`1 ≤ i ≤ n`). The lexicographically-first
greedy maximal independent set selects vertex `i` (in the order `0, 1, …, n`) iff no neighbour
`j < i` was selected; a set `S` is the output of this process iff it satisfies the recursion
`IsLexFirstGreedyMIS`, which determines it uniquely.
-/

namespace GC.Semisort

/-- Adjacency in `H_π`: `u` and `v` are joined by an edge `{i-1, i}` or `{π_i, i}`,
`1 ≤ i ≤ n`. -/
def misAdj (π : ℕ → ℕ) (n u v : ℕ) : Prop :=
  (1 ≤ v ∧ v ≤ n ∧ (u + 1 = v ∨ u = π v)) ∨ (1 ≤ u ∧ u ≤ n ∧ (v + 1 = u ∨ v = π u))

/-- `S` is the lexicographically-first greedy maximal independent set of `H_π`: vertex
`i ≤ n` is selected iff none of its neighbours `j < i` is selected. -/
def IsLexFirstGreedyMIS (π : ℕ → ℕ) (n : ℕ) (S : ℕ → Prop) : Prop :=
  ∀ i ≤ n, (S i ↔ ∀ j < i, misAdj π n j i → ¬ S j)

/-- The neighbours of `i` processed before `i` are exactly `i - 1` and `π_i`. -/
theorem misAdj_lt_iff {π : ℕ → ℕ} {n i j : ℕ} (hπ : IsShape n π) (hi : 1 ≤ i) (hin : i ≤ n)
    (hj : j < i) : misAdj π n j i ↔ (j + 1 = i ∨ j = π i) := by
  unfold misAdj
  constructor
  · rintro (⟨_, _, h⟩ | ⟨h1, h2, h⟩)
    · exact h
    · have := hπ j h1 h2; omega
  · intro h; exact Or.inl ⟨hi, hin, h⟩

/-- **Proposition 3.1.** For Sequential NOR (`x_0 = 1`, all tables NOR) with shape `π`, the set
`{i : x_i = 1}` is the lexicographically-first greedy maximal independent set of `H_π`, and it
is the only set satisfying the greedy recursion. -/
theorem seqNOR_eq_greedyMIS {π : ℕ → ℕ} {n : ℕ} (hπ : IsShape n π) :
    IsLexFirstGreedyMIS π n (fun i => circuitValue true π norGate i = true) ∧
      ∀ S : ℕ → Prop, IsLexFirstGreedyMIS π n S →
        ∀ i ≤ n, (S i ↔ circuitValue true π norGate i = true) := by
  have hx : IsLexFirstGreedyMIS π n (fun i => circuitValue true π norGate i = true) := by
    intro i hin
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [circuitValue_zero]
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    have hp := hπ (k + 1) (by omega) hin
    show circuitValue true π norGate (k + 1) = true ↔ _
    rw [circuitValue_succ _ _ _ hp]
    simp only [norGate, Bool.not_eq_true', Bool.or_eq_false_iff]
    constructor
    · rintro ⟨h1, h2⟩ j hj hadj
      rcases (misAdj_lt_iff hπ (by omega) hin hj).1 hadj with h | h
      · rw [show j = k by omega, h1]; simp
      · rw [h, h2]; simp
    · intro h
      refine ⟨?_, ?_⟩
      · have := h k (by omega) ((misAdj_lt_iff hπ (by omega) hin (by omega)).2 (Or.inl rfl))
        simpa using this
      · have := h (π (k + 1)) hp ((misAdj_lt_iff hπ (by omega) hin hp).2 (Or.inr rfl))
        simpa using this
  refine ⟨hx, fun S hS i => ?_⟩
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hin
    have hxi : circuitValue true π norGate i = true ↔
        ∀ j < i, misAdj π n j i → ¬ circuitValue true π norGate j = true := hx i hin
    rw [hS i hin, hxi]
    constructor
    · intro h j hj hadj hxj
      exact h j hj hadj ((ih j hj (by omega)).2 hxj)
    · intro h j hj hadj hSj
      exact h j hj hadj ((ih j hj (by omega)).1 hSj)

/-! ### Lemma 3.3 (jump rule) -/

/-- One step of the jump rule: if `x_s = 1` and all positions strictly between `s` and `t` have
value `0`, then `x_t = 1` iff `t ≥ s + 2` and `π_t ∉ S` where `S` is the set of positions
`≤ s` with value `1`. -/
theorem jump_step {π : ℕ → ℕ} {n s t : ℕ} (hπ : IsShape n π)
    (hxs : circuitValue true π norGate s = true) (hst : s < t) (htn : t ≤ n)
    (hgap : ∀ u, s < u → u < t → circuitValue true π norGate u = false) :
    circuitValue true π norGate t = true ↔
      (s + 2 ≤ t ∧ ¬ (π t ≤ s ∧ circuitValue true π norGate (π t) = true)) := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  have hp := hπ (k + 1) (by omega) htn
  rw [circuitValue_succ _ _ _ hp]
  simp only [norGate]
  rcases Nat.eq_or_lt_of_le (show s ≤ k by omega) with rfl | hsk
  · rw [hxs]; simp
  · rw [hgap k hsk (by omega)]
    by_cases hπs : π (k + 1) ≤ s
    · simp [hπs, show s + 2 ≤ k + 1 by omega]
    · rw [hgap (π (k + 1)) (by omega) hp]
      simp [hπs, show s + 2 ≤ k + 1 by omega]

/-- **Lemma 3.3 (jump rule).** Let `x_s = 1` in Sequential NOR, let `S` be the set of positions
`≤ s` with value `1`, and `T = {t : s + 2 ≤ t ≤ n, π_t ∉ S}`. If no element of `T` lies below
`t ≤ n` (`t > s`), then every position strictly between `s` and `t` has value `0`, and `x_t = 1`
iff `t ∈ T`. Taking `t = min T` gives `s_{r+1} = min T_r`; taking `t = n` with `T = ∅` shows that
`s` is the last position with value `1`. -/
theorem jump_rule {π : ℕ → ℕ} {n s t : ℕ} (hπ : IsShape n π)
    (hxs : circuitValue true π norGate s = true) (hst : s < t) (htn : t ≤ n)
    (hmin : ∀ u, s + 2 ≤ u → u < t →
      (π u ≤ s ∧ circuitValue true π norGate (π u) = true)) :
    (∀ u, s < u → u < t → circuitValue true π norGate u = false) ∧
      (circuitValue true π norGate t = true ↔
        (s + 2 ≤ t ∧ ¬ (π t ≤ s ∧ circuitValue true π norGate (π t) = true))) := by
  have hgap : ∀ u, s < u → u < t → circuitValue true π norGate u = false := by
    intro u
    induction u using Nat.strong_induction_on with
    | _ u ih =>
      intro hsu hut
      have h := jump_step hπ hxs hsu (by omega) (fun v hv1 hv2 => ih v hv2 hv1 (by omega))
      by_contra hne
      have hne' : circuitValue true π norGate u = true := by simpa using hne
      obtain ⟨h1, h2⟩ := h.1 hne'
      exact h2 (hmin u h1 hut)
  exact ⟨hgap, jump_step hπ hxs hst htn hgap⟩

end GC.Semisort
