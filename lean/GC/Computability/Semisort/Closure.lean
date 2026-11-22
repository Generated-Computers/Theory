import GC.Computability.Semisort.Basic

/-!
# The closure reduction: stable semisort from unstable semisort and padded sorting

Manuscript 011a, Theorem 3.1 and Lemmas 3.2–3.5, and the reductions
`IS ⪯ DS` and `SS ⪯ IS + USemi` of Theorem 4.1.

Stages (S1)–(S5) of the paper: from the output `T` of an unstable semisort (an arbitrary,
possibly adversarial, valid output), compute run marks `s[j]`, run numbers
`g[j] = ∑_{j' ≤ j} s[j'] - 1`, group identifiers `gid[T[j]] = g[j]`, composite keys
`z_i = (n+1) gid[i] + i`; then any valid padded-sort output for the keys `z`, compacted, is a
stable semisort.
-/

namespace GC.Semisort

open Finset

variable {K : Type*} [DecidableEq K]

/-- Run mark `s[j]` (stage S2): `1` at the first position of each run of equal keys in `T`. -/
def runStart (key : ℕ → K) (T : List ℕ) (j : ℕ) : ℕ :=
  if j = 0 ∨ key (T.getD j 0) ≠ key (T.getD (j - 1) 0) then 1 else 0

/-- Run number `g[j] = ∑_{j' ≤ j} s[j'] - 1` (stage S2). -/
def runIndex (key : ℕ → K) (T : List ℕ) (j : ℕ) : ℕ :=
  (∑ j' ∈ range (j + 1), runStart key T j') - 1

/-- Group identifier `gid[i]` (stage S3): the run number of the position of record `i` in `T`. -/
def groupId (key : ℕ → K) (T : List ℕ) (i : ℕ) : ℕ :=
  runIndex key T (T.idxOf i)

/-- Composite key `z_i = (n+1) gid[i] + i` (stage S4). -/
def compositeKey (key : ℕ → K) (T : List ℕ) (n i : ℕ) : ℕ :=
  (n + 1) * groupId key T i + i

/-! ### Run numbers -/

theorem runIndex_zero (key : ℕ → K) (T : List ℕ) : runIndex key T 0 = 0 := by
  simp [runIndex, runStart]

theorem runIndex_succ (key : ℕ → K) (T : List ℕ) (j : ℕ) :
    runIndex key T (j + 1) = runIndex key T j +
      if key (T.getD (j + 1) 0) ≠ key (T.getD j 0) then 1 else 0 := by
  have hpos : 1 ≤ ∑ j' ∈ range (j + 1), runStart key T j' := by
    rw [Finset.sum_range_succ']
    simp [runStart]
  unfold runIndex
  rw [Finset.sum_range_succ (n := j + 1)]
  have : runStart key T (j + 1) =
      if key (T.getD (j + 1) 0) ≠ key (T.getD j 0) then 1 else 0 := by
    simp [runStart]
  rw [this]
  omega

theorem runIndex_le (key : ℕ → K) (T : List ℕ) (j : ℕ) : runIndex key T j ≤ j := by
  induction j with
  | zero => simp [runIndex_zero]
  | succ j ih => rw [runIndex_succ]; split_ifs <;> omega

theorem runIndex_mono (key : ℕ → K) (T : List ℕ) {p p' : ℕ} (h : p ≤ p') :
    runIndex key T p ≤ runIndex key T p' := by
  induction p', h using Nat.le_induction with
  | base => exact le_rfl
  | succ m _ ih => rw [runIndex_succ]; omega

/-- Two positions `p ≤ p'` have the same run number iff no run starts in `(p, p']`. -/
theorem runIndex_eq_iff (key : ℕ → K) (T : List ℕ) {p p' : ℕ} (h : p ≤ p') :
    runIndex key T p = runIndex key T p' ↔
      ∀ t, p ≤ t → t < p' → key (T.getD (t + 1) 0) = key (T.getD t 0) := by
  induction p', h using Nat.le_induction with
  | base => exact ⟨fun _ t h1 h2 => absurd h2 (by omega), fun _ => rfl⟩
  | succ m hm ih =>
    have hmono := runIndex_mono key T hm
    rw [runIndex_succ]
    by_cases hk : key (T.getD (m + 1) 0) = key (T.getD m 0)
    · have h0 : ¬ (key (T.getD (m + 1) 0) ≠ key (T.getD m 0)) := not_not.2 hk
      rw [ite_eq_right h0, Nat.add_zero]
      constructor
      · intro hm' t ht1 ht2
        rcases Nat.lt_succ_iff_lt_or_eq.1 ht2 with ht | rfl
        · exact ih.1 hm' t ht1 ht
        · exact hk
      · intro hall
        exact ih.2 (fun t ht1 ht2 => hall t ht1 (by omega))
    · rw [ite_eq_left hk]
      constructor
      · intro he; omega
      · intro hall; exact absurd (hall m hm (by omega)) hk

omit [DecidableEq K] in
theorem eq_of_chain {f : ℕ → K} {p p' : ℕ} (h : p ≤ p')
    (hc : ∀ t, p ≤ t → t < p' → f (t + 1) = f t) : f p' = f p := by
  induction p', h using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
    rw [hc m hm (by omega), ih (fun t h1 h2 => hc t h1 (by omega))]

/-- Lemma 3.2 at the level of positions of `T`. -/
theorem runIndex_eq_iff_key_eq {key : ℕ → K} {T : List ℕ} (hc : KeysContiguous key T)
    {p p' : ℕ} (hp : p < T.length) (hp' : p' < T.length) :
    runIndex key T p = runIndex key T p' ↔ key (T.getD p 0) = key (T.getD p' 0) := by
  -- reduce to `p ≤ p'`
  suffices H : ∀ p p', p ≤ p' → p' < T.length →
      (runIndex key T p = runIndex key T p' ↔ key (T.getD p 0) = key (T.getD p' 0)) by
    rcases le_total p p' with h | h
    · exact H p p' h hp'
    · rw [eq_comm, H p' p h hp, eq_comm]
  intro p p' hpp' hp'
  rw [runIndex_eq_iff key T hpp']
  constructor
  · intro hall
    exact (eq_of_chain (f := fun t => key (T.getD t 0)) hpp' hall).symm
  · intro heq t ht1 ht2
    -- every position in `[p, p']` has the key of `p`, by contiguity
    have hmid : ∀ u, p ≤ u → u ≤ p' → key (T.getD u 0) = key (T.getD p 0) := by
      intro u hu1 hu2
      rcases Nat.eq_or_lt_of_le hu1 with rfl | hu1
      · rfl
      rcases Nat.eq_or_lt_of_le hu2 with rfl | hu2
      · exact heq.symm
      have := hc p u p' (by omega) (by omega) hp' hu1 hu2
      rw [List.getD_eq_getElem _ _ (show u < T.length by omega),
        List.getD_eq_getElem _ _ (show p < T.length by omega)]
      rw [List.getD_eq_getElem _ _ (show p < T.length by omega),
        List.getD_eq_getElem _ _ (show p' < T.length by omega)] at heq
      exact this heq
    rw [hmid (t + 1) (by omega) (by omega), hmid t ht1 (by omega)]

/-! ### Lemma 3.2 (group identifiers) -/

theorem idxOf_spec {T : List ℕ} {n i : ℕ} (hT : T.Perm (List.range n)) (hi : i < n) :
    T.idxOf i < T.length ∧ T.getD (T.idxOf i) 0 = i := by
  have hmem : i ∈ T := hT.mem_iff.2 (List.mem_range.2 hi)
  have hlt := List.idxOf_lt_length_of_mem hmem
  refine ⟨hlt, ?_⟩
  rw [List.getD_eq_getElem _ _ hlt, List.getElem_idxOf]

/-- Lemma 3.2: records have equal group identifiers iff they have equal keys. -/
theorem groupId_eq_iff {key : ℕ → K} {n : ℕ} {T : List ℕ} (hT : IsSemisort key n T)
    {i j : ℕ} (hi : i < n) (hj : j < n) :
    groupId key T i = groupId key T j ↔ key i = key j := by
  obtain ⟨hpi, hgi⟩ := idxOf_spec hT.1 hi
  obtain ⟨hpj, hgj⟩ := idxOf_spec hT.1 hj
  unfold groupId
  rw [runIndex_eq_iff_key_eq hT.2 hpi hpj, hgi, hgj]

/-- Lemma 3.2: group identifiers lie in `[0, n)`. -/
theorem groupId_lt {key : ℕ → K} {n : ℕ} {T : List ℕ} (hT : IsSemisort key n T)
    {i : ℕ} (hi : i < n) : groupId key T i < n := by
  obtain ⟨hpi, _⟩ := idxOf_spec hT.1 hi
  have := runIndex_le key T (T.idxOf i)
  have hl : T.length = n := by simpa using hT.1.length_eq
  unfold groupId; omega

/-! ### Lemma 3.3 (lexicographic encoding) -/

theorem lex_encode_lt_sq {n g i : ℕ} (hg : g < n + 1) (hi : i < n + 1) :
    (n + 1) * g + i < (n + 1) ^ 2 := by
  have h1 : (n + 1) * g + i < (n + 1) * (g + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
  have h2 : (n + 1) * (g + 1) ≤ (n + 1) * (n + 1) := Nat.mul_le_mul_left _ hg
  rw [Nat.pow_two]; omega

/-- Lemma 3.3: the composite keys form a valid `PaddedSort(n,(n+1)^2)` instance. -/
theorem compositeKey_valid {key : ℕ → K} {n : ℕ} {T : List ℕ} (hT : IsSemisort key n T) :
    IsDistinctKeyInstance (compositeKey key T n) n ((n + 1) ^ 2) := by
  refine ⟨fun i hi => ?_, fun i hi j hj h => ?_⟩
  · have hg := groupId_lt hT hi
    unfold compositeKey
    exact lex_encode_lt_sq (by omega) (by omega)
  · exact (lex_encode_inj (N := n + 1) (by omega) (by omega) h).2

/-! ### `IS ⪯ DS` (Theorem 4.1(a), second half) -/

/-- Theorem 4.1(a), `IS ⪯ DS`: sorting the distinct keys `(n+1) a_i + i` sorts stably by `a`. -/
theorem isStableIntSort_of_isDistinctSort {a : ℕ → ℕ} {n : ℕ} {out : List ℕ}
    (h : IsDistinctSort (fun i => (n + 1) * a i + i) n out) : IsStableIntSort a n out := by
  refine ⟨h.1, h.2.imp_of_mem fun {i j} hi hj hij => ?_⟩
  have hi' := lt_of_mem_perm_range h.1 hi
  have hj' := lt_of_mem_perm_range h.1 hj
  exact (lex_encode_lt_iff (N := n + 1) (by omega) (by omega)).1 hij

/-- The keys `(n+1) a_i + i` form a valid `DS` instance when `a_i ∈ [0,n]`. -/
theorem lexKey_valid {a : ℕ → ℕ} {n : ℕ} (ha : ∀ i < n, a i ≤ n) :
    IsDistinctKeyInstance (fun i => (n + 1) * a i + i) n ((n + 1) ^ 2) := by
  refine ⟨fun i hi => ?_, fun i hi j hj h => (lex_encode_inj (N := n + 1) (by omega)
    (by omega) h).2⟩
  exact lex_encode_lt_sq (Nat.lt_succ_of_le (ha i hi)) (by omega)

/-! ### `SS ⪯ IS + USemi` (Theorem 4.1(c)) -/

/-- Theorem 4.1(c): stably sorting by the group identifiers computed from an unstable semisort
gives a stable semisort. -/
theorem isStableSemisort_of_isStableIntSort_groupId {key : ℕ → K} {n : ℕ} {T out : List ℕ}
    (hT : IsSemisort key n T) (h : IsStableIntSort (groupId key T) n out) :
    IsStableSemisort key n out := by
  have hpw := List.pairwise_iff_getElem.1 h.2
  have hlt : ∀ (p : ℕ) (hp : p < out.length), out[p] < n := fun p hp =>
    lt_of_mem_perm_range h.1 (List.getElem_mem hp)
  refine ⟨⟨h.1, ?_⟩, ?_⟩
  · intro p q r hp hq hr hpq hqr hpr
    have h1 := hpw p q hp hq hpq
    have h2 := hpw q r hq hr hqr
    have hg : groupId key T out[p] = groupId key T out[r] :=
      (groupId_eq_iff hT (hlt p hp) (hlt r hr)).2 hpr
    have hq' : groupId key T out[q] = groupId key T out[p] := by omega
    exact (groupId_eq_iff hT (hlt q hq) (hlt p hp)).1 hq'
  · intro p q hp hq hpq hk
    have h1 := hpw p q hp hq hpq
    have hg := (groupId_eq_iff hT (hlt p hp) (hlt q hq)).2 hk
    omega

/-! ### Theorem 3.1 -/

/-- The output of the closure reduction: the compacted padded-sort output (stage S5). -/
def closureOutput (P : List (Option ℕ)) : List ℕ := compact P

/-- **Theorem 3.1 (closure reduction), correctness.** Let `T` be any valid output of an
unstable semisort of the records `0, …, n-1` (stages S1–S2), and let `P` be any valid output of
`PaddedSort(n,(n+1)^2)` on the composite keys `z_i = (n+1) gid[i] + i` built from `T` (stages
S3–S4). Then the composite keys form a valid instance (distinct, below `(n+1)^2`), and the
compaction of `P` (stage S5) is a stable semisort. -/
theorem closure_correct (key : ℕ → K) (n : ℕ) (T : List ℕ) (hT : IsSemisort key n T)
    (P : List (Option ℕ)) (hP : IsPaddedSort (compositeKey key T n) n P) :
    IsDistinctKeyInstance (compositeKey key T n) n ((n + 1) ^ 2) ∧
      IsStableSemisort key n (closureOutput P) :=
  ⟨compositeKey_valid hT, isStableSemisort_of_isStableIntSort_groupId hT
    (isStableIntSort_of_isDistinctSort (isDistinctSort_compact hP))⟩

/-- The closure reduction as an algorithm with two oracles: `usemi` (unstable semisort) and
`psort` (padded sorting on `n` records with keys below `(n+1)^2`). -/
def stableSemisortViaPadded (usemi : (ℕ → K) → List ℕ) (psort : (ℕ → ℕ) → List (Option ℕ))
    (n : ℕ) (key : ℕ → K) : List ℕ :=
  closureOutput (psort (compositeKey key (usemi key) n))

/-- **Theorem 3.1, oracle form: `SS ⪯ PaddedSort + USemi`.** If `usemi` returns a valid
unstable semisort and `psort` solves every valid instance of `PaddedSort(n,(n+1)^2)`, then the
closure reduction returns a stable semisort. -/
theorem stableSemisort_of_paddedSort (usemi : (ℕ → K) → List ℕ)
    (psort : (ℕ → ℕ) → List (Option ℕ)) (n : ℕ) (key : ℕ → K)
    (hU : IsSemisort key n (usemi key))
    (hP : ∀ z : ℕ → ℕ, IsDistinctKeyInstance z n ((n + 1) ^ 2) → IsPaddedSort z n (psort z)) :
    IsStableSemisort key n (stableSemisortViaPadded usemi psort n key) :=
  (closure_correct key n (usemi key) hU _ (hP _ (compositeKey_valid hU))).2

end GC.Semisort
