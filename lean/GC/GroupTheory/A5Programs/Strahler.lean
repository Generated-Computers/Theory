import GC.GroupTheory.A5Programs.Gadgets
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Log

/-!
# Barrington gadgets meet Strahler rank (manuscript 004g)

The gadget statements (Lemma 3.2, Theorem 3.3, Corollary 3.4) are `gadget_identities`,
`gadgets_correct` and `boolean_to_A5` in `Gadgets.lean`. Here:

* `strahler_unfolding`: in a circuit whose vertices list their predecessors, the Strahler rank
  `sr(v)` (with the trivial congruence and no designated constants) satisfies
  `2^{sr(v)} ≤ U(v)`, where `U(v)` counts the vertices of the unfolding of the cone of `v`
  (Corollary 6.8; `sr(v) ≤ log₂ U(v)`).
* `strahler_mono`: rank does not decrease along arcs (used in Lemmas 6.3 and 6.4).
* `quotient_val`: redirecting every operand of a straight-line program to the earliest member of
  its class under a value-respecting equivalence does not change any value (Lemma 6.1).
-/

namespace GC.A5Programs

/-! ## Strahler rank of a circuit given by predecessor lists -/

/-- The largest element of a list of naturals (`0` for the empty list). -/
def lmax (l : List ℕ) : ℕ := l.foldr max 0

theorem le_lmax {l : List ℕ} {x : ℕ} (hx : x ∈ l) : x ≤ lmax l := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    simp only [lmax, List.foldr_cons] at *
    rcases List.mem_cons.1 hx with rfl | hx
    · exact le_max_left _ _
    · exact (ih hx).trans (le_max_right _ _)

theorem lmax_mem {l : List ℕ} (hl : l ≠ []) : lmax l ∈ l := by
  induction l with
  | nil => exact absurd rfl hl
  | cons a l ih =>
    simp only [lmax, List.foldr_cons]
    by_cases hl' : l = []
    · subst hl'; simp
    · rcases le_total a (List.foldr max 0 l) with h | h
      · rw [max_eq_right h]; exact List.mem_cons_of_mem _ (ih hl')
      · rw [max_eq_left h]; exact List.mem_cons_self

/-- The Strahler rule: inputs and gates without predecessors have rank `0`; otherwise the
largest rank `r₁` among the distinct predecessors, plus one if it is attained twice. -/
def rankStep (rs : List ℕ) (ps : List ℕ) : ℕ :=
  if ps.dedup = [] then 0
  else
    let vals := ps.dedup.map (fun u => rs.getD u 0)
    if 2 ≤ vals.count (lmax vals) then lmax vals + 1 else lmax vals

/-- Ranks of all vertices; vertex `k` has predecessor list `cs[k]`. -/
def ranks (cs : List (List ℕ)) : List ℕ := cs.foldl (fun rs ps => rs ++ [rankStep rs ps]) []

/-- Size of the unfolding of the cone (over distinct predecessors). -/
def unfoldStep (us : List ℕ) (ps : List ℕ) : ℕ := 1 + (ps.dedup.map (fun u => us.getD u 0)).sum

/-- Unfolding sizes of all vertices. -/
def unfoldSizes (cs : List (List ℕ)) : List ℕ :=
  cs.foldl (fun us ps => us ++ [unfoldStep us ps]) []

/-- Every vertex lists only earlier vertices as predecessors. -/
def CircWF (cs : List (List ℕ)) : Prop := ∀ k (h : k < cs.length), ∀ u ∈ cs[k]'h, u < k

theorem ranks_snoc (cs : List (List ℕ)) (ps : List ℕ) :
    ranks (cs ++ [ps]) = ranks cs ++ [rankStep (ranks cs) ps] := by
  simp [ranks, List.foldl_append]

theorem unfoldSizes_snoc (cs : List (List ℕ)) (ps : List ℕ) :
    unfoldSizes (cs ++ [ps]) = unfoldSizes cs ++ [unfoldStep (unfoldSizes cs) ps] := by
  simp [unfoldSizes, List.foldl_append]

@[simp] theorem length_ranks (cs : List (List ℕ)) : (ranks cs).length = cs.length := by
  induction cs using List.reverseRecOn with
  | nil => rfl
  | append_singleton cs ps ih => simp [ranks_snoc, ih]

@[simp] theorem length_unfoldSizes (cs : List (List ℕ)) :
    (unfoldSizes cs).length = cs.length := by
  induction cs using List.reverseRecOn with
  | nil => rfl
  | append_singleton cs ps ih => simp [unfoldSizes_snoc, ih]

theorem circWF_snoc {cs : List (List ℕ)} {ps : List ℕ} (h : CircWF (cs ++ [ps])) :
    CircWF cs ∧ ∀ u ∈ ps, u < cs.length := by
  refine ⟨fun k hk u hu => ?_, fun u hu => ?_⟩
  · have := h k (by simp; omega) u (by rwa [List.getElem_append_left hk])
    exact this
  · have := h cs.length (by simp) u (by simpa using hu)
    exact this

theorem two_le_count_map {l : List ℕ} (hl : l.Nodup) (f : ℕ → ℕ) {r : ℕ}
    (h : 2 ≤ (l.map f).count r) : ∃ u₁ ∈ l, ∃ u₂ ∈ l, u₁ ≠ u₂ ∧ f u₁ = r ∧ f u₂ = r := by
  rw [List.count_eq_countP, List.countP_map, List.countP_eq_length_filter] at h
  have h' : 2 ≤ (l.filter fun u => (f u == r)).length := by simpa [Function.comp_def] using h
  have hnd : (l.filter fun u => (f u == r)).Nodup := hl.filter _
  obtain ⟨a, b, t, ht⟩ : ∃ a b t, l.filter (fun u => (f u == r)) = a :: b :: t := by
    rcases hfl : l.filter (fun u => (f u == r)) with _ | ⟨a, _ | ⟨b, t⟩⟩
    · rw [hfl] at h'; simp at h'
    · rw [hfl] at h'; simp at h'
    · exact ⟨a, b, t, rfl⟩
  have ha : a ∈ l.filter (fun u => (f u == r)) := by rw [ht]; simp
  have hb : b ∈ l.filter (fun u => (f u == r)) := by rw [ht]; simp
  rw [ht] at hnd
  simp only [List.mem_filter, beq_iff_eq] at ha hb
  refine ⟨a, ha.1, b, hb.1, ?_, ha.2, hb.2⟩
  intro hab; subst hab; simp at hnd

theorem sum_ge_pair {l : List ℕ} (hl : l.Nodup) (f : ℕ → ℕ) {u₁ u₂ : ℕ} (h1 : u₁ ∈ l)
    (h2 : u₂ ∈ l) (h12 : u₁ ≠ u₂) : f u₁ + f u₂ ≤ (l.map f).sum := by
  classical
  rw [← List.sum_toFinset f hl, ← Finset.sum_pair h12]
  apply Finset.sum_le_sum_of_subset
  intro x hx; simp at hx; rcases hx with rfl | rfl <;> simpa

theorem single_le_sum {l : List ℕ} (f : ℕ → ℕ) {u : ℕ} (h : u ∈ l) : f u ≤ (l.map f).sum :=
  List.le_sum_of_mem (List.mem_map_of_mem h)

/-- **Unfolding bound** (004g, Corollary 6.8): `2^{sr(v)} ≤ U(v)` for every vertex, that is,
`sr(v) ≤ log₂ U(v)`. -/
theorem strahler_unfolding (cs : List (List ℕ)) (hwf : CircWF cs) :
    ∀ k < cs.length, 2 ^ (ranks cs).getD k 0 ≤ (unfoldSizes cs).getD k 0 := by
  induction cs using List.reverseRecOn with
  | nil => intro k hk; simp at hk
  | append_singleton cs ps ih =>
    obtain ⟨hwf1, hps⟩ := circWF_snoc hwf
    have ih' := ih hwf1
    intro k hk
    simp only [List.length_append, List.length_singleton] at hk
    rw [ranks_snoc, unfoldSizes_snoc]
    rcases Nat.lt_or_ge k cs.length with hk' | hk'
    · rw [List.getD_append _ _ _ _ (by simpa using hk'),
        List.getD_append _ _ _ _ (by simpa using hk')]
      exact ih' k hk'
    · have hkk : k = cs.length := by omega
      subst hkk
      rw [List.getD_append_right _ _ _ _ (by simp), List.getD_append_right _ _ _ _ (by simp)]
      simp only [length_ranks, length_unfoldSizes, Nat.sub_self, List.getD_cons_zero]
      unfold rankStep unfoldStep
      have hd : ∀ u ∈ ps.dedup, u < cs.length := fun u hu => hps u (List.mem_dedup.1 hu)
      by_cases hemp : ps.dedup = []
      · rw [if_pos hemp]; simp
      · rw [if_neg hemp]
        simp only
        have hvne : ps.dedup.map (fun u => (ranks cs).getD u 0) ≠ [] := by simpa using hemp
        obtain ⟨u₀, hu₀, hr₀⟩ := List.mem_map.1 (lmax_mem hvne)
        have hU : ∀ u ∈ ps.dedup, 2 ^ (ranks cs).getD u 0 ≤ (unfoldSizes cs).getD u 0 :=
          fun u hu => ih' u (hd u hu)
        split_ifs with hc
        · obtain ⟨u₁, h1, u₂, h2, h12, hr1, hr2⟩ := two_le_count_map (List.nodup_dedup ps) _ hc
          have hs := sum_ge_pair (List.nodup_dedup ps) (fun u => (unfoldSizes cs).getD u 0)
            h1 h2 h12
          have e1 := hU u₁ h1
          have e2 := hU u₂ h2
          rw [hr1] at e1; rw [hr2] at e2
          rw [pow_succ]
          omega
        · have hs := single_le_sum (fun u => (unfoldSizes cs).getD u 0) hu₀
          have e0 := hU u₀ hu₀
          rw [hr₀] at e0
          omega

/-- Rank does not decrease along arcs: every predecessor has rank at most that of the vertex. -/
theorem strahler_mono (cs : List (List ℕ)) (hwf : CircWF cs) :
    ∀ k (hk : k < cs.length), ∀ u ∈ cs[k]'hk, (ranks cs).getD u 0 ≤ (ranks cs).getD k 0 := by
  induction cs using List.reverseRecOn with
  | nil => intro k hk; simp at hk
  | append_singleton cs ps ih =>
    obtain ⟨hwf1, hps⟩ := circWF_snoc hwf
    intro k hk u hu
    simp only [List.length_append, List.length_singleton] at hk
    rw [ranks_snoc]
    rcases Nat.lt_or_ge k cs.length with hk' | hk'
    · have hu' : u ∈ cs[k]'hk' := by rwa [List.getElem_append_left hk'] at hu
      have hul : u < cs.length := (hwf1 k hk' u hu').trans hk'
      rw [List.getD_append _ _ _ _ (by simpa using hul),
        List.getD_append _ _ _ _ (by simpa using hk')]
      exact ih hwf1 k hk' u hu'
    · have hkk : k = cs.length := by omega
      subst hkk
      have hu' : u ∈ ps := by simpa using hu
      have hul := hps u hu'
      rw [List.getD_append _ _ _ _ (by simpa using hul),
        List.getD_append_right _ _ _ _ (by simp)]
      simp only [length_ranks, Nat.sub_self, List.getD_cons_zero]
      unfold rankStep
      have hne : ps.dedup ≠ [] := by
        intro h; have := List.mem_dedup.2 hu'; rw [h] at this; simp at this
      rw [if_neg hne]
      simp only
      have := le_lmax (List.mem_map_of_mem (f := fun u => (ranks cs).getD u 0)
        (List.mem_dedup.2 hu'))
      split_ifs <;> omega

/-! ## Quotients by value-respecting equivalences -/

section Quotient

variable {α : Type} {G : Type*} [Group G]

/-- Redirect the operands of an operation through `ρ`. -/
def Op.redirect (ρ : ℕ → ℕ) : Op α → Op α
  | .leaf a => .leaf a
  | .mul i j => .mul (ρ i) (ρ j)
  | .inv i => .inv (ρ i)

/-- **Quotient lemma** (004g, Lemma 6.1). Let `ρ` send every vertex to a vertex not after it
(the earliest member of its class) with the same value. Redirecting every operand through `ρ`
leaves all values unchanged. -/
theorem quotient_val (ν : α → G) (C : List (Op α)) (hwf : WellFormed C) (ρ : ℕ → ℕ)
    (hρle : ∀ u, ρ u ≤ u) (hρval : ∀ u, val ν C (ρ u) = val ν C u) :
    ∀ k < C.length, val ν (C.map (Op.redirect ρ)) k = val ν C k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have hk' : k < (C.map (Op.redirect ρ)).length := by simpa using hk
    rw [val_of_lt _ _ hk', val_of_lt _ _ hk]
    have hpre : ∀ (D : List (Op α)) i, i < k → k ≤ D.length →
        val ν (D.take k) i = val ν D i := by
      intro D i hi hD
      conv_rhs => rw [← List.take_append_drop k D]
      rw [val_append_of_lt _ _ _ (by simp; omega)]
    have hw := hwf k hk
    simp only [List.getElem_map]
    cases hop : C[k]'hk with
    | leaf a => rfl
    | mul i j =>
      rw [hop] at hw
      show val ν ((C.map (Op.redirect ρ)).take k) (ρ i) *
          val ν ((C.map (Op.redirect ρ)).take k) (ρ j) =
        val ν (C.take k) i * val ν (C.take k) j
      have hi := (hρle i).trans_lt hw.1
      have hj := (hρle j).trans_lt hw.2
      rw [hpre _ _ hi (by simp; omega), hpre _ _ hj (by simp; omega), hpre _ _ hw.1 hk.le,
        hpre _ _ hw.2 hk.le, ih _ hi (by omega), ih _ hj (by omega), hρval, hρval]
    | inv i =>
      rw [hop] at hw
      show (val ν ((C.map (Op.redirect ρ)).take k) (ρ i))⁻¹ = (val ν (C.take k) i)⁻¹
      have hi := (hρle i).trans_lt hw
      rw [hpre _ _ hi (by simp; omega), hpre _ _ hw hk.le, ih _ hi (by omega), hρval]

end Quotient

end GC.A5Programs
