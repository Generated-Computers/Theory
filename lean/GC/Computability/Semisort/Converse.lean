import GC.Computability.Semisort.Closure
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Card

/-!
# The converse: padded sorting from stable semisort

Manuscript 011a, Theorem 4.1(a) (`DS ⪯ IS`), Theorem 4.1(b) (`IS ⪯ SS`), and their composition
with Lemma 2.4: `PaddedSort(n,(n+1)^2) ⪯ SS`, with no call to an unstable semisort.

`IS ⪯ SS`: from a stable semisort `out` of integer keys, every record gets its offset inside its
group by a segmented scan, the group lengths `L[k]` and their exclusive prefix sums
`B[k] = ∑_{k'<k} L[k']` are formed, and the record at output position `p` is scattered to
position `B[a(out[p])] + offset(p)`.

`DS ⪯ IS`: two stable passes, first by the low digit `z mod (n+1)`, then by the high digit
`z / (n+1)`.
-/

namespace GC.Semisort

open Finset

/-! ### Definitions of the glue code -/

/-- Segmented scan: offset of position `p` inside its run of equal values of `f`. -/
def segOffset {K : Type*} [DecidableEq K] (f : ℕ → K) : ℕ → ℕ
  | 0 => 0
  | p + 1 => if f (p + 1) = f p then segOffset f p + 1 else 0

/-- The group length `L[k]`: the number of records with key `k` in the semisorted list `out`. -/
def groupLen (a : ℕ → ℕ) (out : List ℕ) (k : ℕ) : ℕ :=
  out.countP (fun i => a i = k)

/-- Exclusive prefix sum `B[k] = ∑_{k' < k} L[k']`. -/
def groupBase (a : ℕ → ℕ) (out : List ℕ) (k : ℕ) : ℕ :=
  ∑ k' ∈ range k, groupLen a out k'

/-- Target position `B[a(out[p])] + offset(p)` of the record at position `p` of `out`. -/
def intSortTarget (a : ℕ → ℕ) (out : List ℕ) (p : ℕ) : ℕ :=
  groupBase a out (a (out.getD p 0)) + segOffset (fun p => a (out.getD p 0)) p

/-- Exclusive scatter: cell `t < m` receives the entry of `src` at the position `p` with
`pos p = t` (the first one, if several; in our use there is exactly one). -/
def scatter (m : ℕ) (pos : ℕ → ℕ) (src : List ℕ) : List ℕ :=
  (List.range m).map fun t =>
    src.getD (((List.range src.length).find? fun p => pos p = t).getD 0) 0

/-- Theorem 4.1(b), `IS ⪯ SS`: the stable integer sort computed from a stable semisort. -/
def intSortViaSS (a : ℕ → ℕ) (n : ℕ) (out : List ℕ) : List ℕ :=
  scatter n (intSortTarget a out) out

/-- Theorem 4.1(a), `DS ⪯ IS`: two-digit least-significant-digit radix sort with an `IS`
oracle. The second pass sorts the records in the order produced by the first pass. -/
def distinctSortViaIS (n : ℕ) (isort : (ℕ → ℕ) → List ℕ) (z : ℕ → ℕ) : List ℕ :=
  let O1 := isort (fun i => z i % (n + 1))
  let O2 := isort (fun t => z (O1.getD t 0) / (n + 1))
  O2.map (fun t => O1.getD t 0)

/-- `PaddedSort(n,(n+1)^2) ⪯ SS`: the composition of `DS ⪯ IS`, `IS ⪯ SS` and Lemma 2.4. -/
def paddedSortViaSS (n : ℕ) (ssort : (ℕ → ℕ) → List ℕ) (z : ℕ → ℕ) : List (Option ℕ) :=
  (distinctSortViaIS n (fun a => intSortViaSS a n (ssort a)) z).map some

/-! ### Stable rank -/

/-- The stable rank of record `i`: the number of records before it in stable integer order. -/
def stableRank (a : ℕ → ℕ) (n i : ℕ) : ℕ :=
  #((range n).filter fun j => a j < a i ∨ (a j = a i ∧ j < i))

theorem stableRank_lt {a : ℕ → ℕ} {n i : ℕ} (hi : i < n) : stableRank a n i < n := by
  unfold stableRank
  have : (range n).filter (fun j => a j < a i ∨ (a j = a i ∧ j < i)) ⊂ range n :=
    Finset.filter_ssubset.2 ⟨i, mem_range.2 hi, by omega⟩
  simpa using Finset.card_lt_card this

theorem stableRank_strictMono {a : ℕ → ℕ} {n i j : ℕ} (hi : i < n)
    (h : a i < a j ∨ (a i = a j ∧ i < j)) : stableRank a n i < stableRank a n j := by
  unfold stableRank
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨i, by simp only [mem_filter, mem_range]; omega,
      by simp only [mem_filter, mem_range]; omega⟩
  · intro x hx
    simp only [mem_filter, mem_range] at hx ⊢
    omega

theorem lex_of_stableRank_lt {a : ℕ → ℕ} {n i j : ℕ} (hi : i < n) (hj : j < n)
    (h : stableRank a n i < stableRank a n j) : a i < a j ∨ (a i = a j ∧ i < j) := by
  by_contra hne
  rcases Nat.lt_or_ge (a j) (a i) with h1 | h1
  · have := stableRank_strictMono (a := a) (n := n) hj (Or.inl h1); omega
  · rcases lt_trichotomy j i with h2 | rfl | h2
    · have := stableRank_strictMono (a := a) (n := n) hj
        (Or.inr ⟨(by omega : a j = a i), h2⟩); omega
    · omega
    · exact hne (by omega)

theorem stableRank_injOn {a : ℕ → ℕ} {n i j : ℕ} (hi : i < n) (hj : j < n)
    (h : stableRank a n i = stableRank a n j) : i = j := by
  by_contra hne
  rcases Nat.lt_or_ge (a i) (a j) with h1 | h1
  · have := stableRank_strictMono (a := a) (n := n) hi (Or.inl h1); omega
  rcases Nat.lt_or_ge (a j) (a i) with h2 | h2
  · have := stableRank_strictMono (a := a) (n := n) hj (Or.inl h2); omega
  rcases Nat.lt_or_ge i j with h3 | h3
  · have := stableRank_strictMono (a := a) (n := n) hi
      (Or.inr ⟨(by omega : a i = a j), h3⟩); omega
  · have := stableRank_strictMono (a := a) (n := n) hj
      (Or.inr ⟨(by omega : a j = a i), (by omega : j < i)⟩); omega

theorem stableRank_surj {a : ℕ → ℕ} {n t : ℕ} (ht : t < n) :
    ∃ i < n, stableRank a n i = t := by
  have hsub : (range n).image (stableRank a n) ⊆ range n := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hx
    exact mem_range.2 (stableRank_lt (mem_range.1 hi))
  have hcard : #(range n) ≤ #((range n).image (stableRank a n)) := by
    rw [card_image_of_injOn]
    intro i hi j hj h
    exact stableRank_injOn (mem_range.1 hi) (mem_range.1 hj) h
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have : t ∈ (range n).image (stableRank a n) := by rw [heq]; exact mem_range.2 ht
  obtain ⟨i, hi, h⟩ := mem_image.1 this
  exact ⟨i, mem_range.1 hi, h⟩

/-- The stable rank splits as `#{j : a j < a i} + #{j < i : a j = a i}`. -/
theorem stableRank_eq (a : ℕ → ℕ) (n i : ℕ) :
    stableRank a n i = #((range n).filter fun j => a j < a i) +
      #((range n).filter fun j => a j = a i ∧ j < i) := by
  unfold stableRank
  rw [card_filter, card_filter, card_filter, ← sum_add_distrib]
  apply sum_congr rfl
  intro j _
  split_ifs <;> omega

/-! ### Correctness of `IS ⪯ SS` -/

section ISfromSS

variable {a : ℕ → ℕ} {n : ℕ} {out : List ℕ}

theorem countP_range_eq_card (p : ℕ → Bool) (n : ℕ) :
    (List.range n).countP p = #((range n).filter fun j => p j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.countP_append, ih, Finset.range_add_one, Finset.filter_insert]
    split_ifs with h
    · rw [card_insert_of_notMem (by simp)]; simp [h]
    · simp [h]

theorem groupBase_eq (hperm : out.Perm (List.range n)) (k : ℕ) :
    groupBase a out k = #((range n).filter fun j => a j < k) := by
  unfold groupBase groupLen
  have : ∀ k', out.countP (fun i => a i = k') = #((range n).filter fun j => a j = k') := by
    intro k'
    rw [hperm.countP_eq, countP_range_eq_card]
    simp
  simp_rw [this, card_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  rw [sum_ite_eq]
  simp

theorem getD_lt (hperm : out.Perm (List.range n)) {p : ℕ} (hp : p < n) : out.getD p 0 < n := by
  have hl : out.length = n := by simpa using hperm.length_eq
  rw [List.getD_eq_getElem _ _ (by omega)]
  exact lt_of_mem_perm_range hperm (List.getElem_mem _)

/-- Contiguity, in `getD` form. -/
theorem contig_getD (h : IsStableSemisort a n out) {p q r : ℕ} (hpq : p < q) (hqr : q < r)
    (hr : r < n) (he : a (out.getD p 0) = a (out.getD r 0)) :
    a (out.getD q 0) = a (out.getD p 0) := by
  have hl : out.length = n := by simpa using h.1.1.length_eq
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at he ⊢
  exact h.1.2 p q r (by omega) (by omega) (by omega) hpq hqr he

/-- Stability, in `getD` form. -/
theorem stable_getD (h : IsStableSemisort a n out) {p q : ℕ} (hpq : p < q) (hq : q < n)
    (he : a (out.getD p 0) = a (out.getD q 0)) : out.getD p 0 < out.getD q 0 := by
  have hl : out.length = n := by simpa using h.1.1.length_eq
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at he ⊢
  exact h.2 p q (by omega) (by omega) hpq he

/-- In a semisort, the segmented scan computes the number of earlier positions with the
same key. -/
theorem segOffset_eq_card (h : IsStableSemisort a n out) {p : ℕ} (hp : p < n) :
    segOffset (fun p => a (out.getD p 0)) p =
      #((range p).filter fun p' => a (out.getD p' 0) = a (out.getD p 0)) := by
  induction p with
  | zero => simp [segOffset]
  | succ p ih =>
    have ih := ih (by omega)
    simp only [segOffset]
    rw [Finset.range_add_one, Finset.filter_insert]
    split_ifs with h1 h2 h2
    · rw [card_insert_of_notMem (by simp), ih]
      have hc : ∀ x, (a (out.getD x 0) = a (out.getD p 0)) ↔
          (a (out.getD x 0) = a (out.getD (p + 1) 0)) := fun x => by rw [h1]
      simp_rw [hc]
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · rw [eq_comm, card_eq_zero, filter_eq_empty_iff]
      intro x hx hx'
      have hx := mem_range.1 hx
      have := contig_getD h hx (show p < p + 1 by omega) hp hx'
      exact h1 (hx'.symm.trans this.symm)

/-- By stability, earlier positions with the same key carry exactly the records with the same
key and a smaller index. -/
theorem card_pos_eq_card_idx (h : IsStableSemisort a n out) {p : ℕ} (hp : p < n) :
    #((range p).filter fun p' => a (out.getD p' 0) = a (out.getD p 0)) =
      #((range n).filter fun j => a j = a (out.getD p 0) ∧ j < out.getD p 0) := by
  have hperm := h.1.1
  have hl : out.length = n := by simpa using hperm.length_eq
  have hnd : out.Nodup := hperm.nodup_iff.2 List.nodup_range
  apply card_bij (fun p' _ => out.getD p' 0)
  · intro p' hp'
    simp only [mem_filter, mem_range] at hp' ⊢
    exact ⟨getD_lt hperm (by omega), hp'.2, stable_getD h hp'.1 hp hp'.2⟩
  · intro p₁ h₁ p₂ h₂ he
    simp only [mem_filter, mem_range] at h₁ h₂
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at he
    exact (hnd.getElem_inj_iff).1 he
  · intro j hj
    simp only [mem_filter, mem_range] at hj
    obtain ⟨hpj, hgj⟩ := idxOf_spec hperm hj.1
    refine ⟨out.idxOf j, ?_, hgj⟩
    simp only [mem_filter, mem_range]
    rcases lt_trichotomy (out.idxOf j) p with h1 | h1 | h1
    · exact ⟨h1, by rw [hgj]; exact hj.2.1⟩
    · rw [h1] at hgj; omega
    · have := stable_getD h h1 (by omega) (by rw [hgj]; exact hj.2.1.symm)
      rw [hgj] at this; omega

/-- The target position of the record at position `p` is its stable rank. -/
theorem intSortTarget_eq (h : IsStableSemisort a n out) {p : ℕ} (hp : p < n) :
    intSortTarget a out p = stableRank a n (out.getD p 0) := by
  unfold intSortTarget
  rw [groupBase_eq h.1.1, segOffset_eq_card h hp, card_pos_eq_card_idx h hp, stableRank_eq]

/-- **Theorem 4.1(b), `IS ⪯ SS`, correctness.** From any stable semisort of integer keys, the
segmented scan, the group lengths, their prefix sums and one exclusive scatter produce the
stable integer sort. -/
theorem intSortViaSS_correct (h : IsStableSemisort a n out) :
    IsStableIntSort a n (intSortViaSS a n out) := by
  have hperm := h.1.1
  have hl : out.length = n := by simpa using hperm.length_eq
  set g : ℕ → ℕ := fun t =>
    out.getD (((List.range out.length).find? fun p => intSortTarget a out p = t).getD 0) 0
    with hg
  have hR : intSortViaSS a n out = (List.range n).map g := rfl
  -- the record sent to cell `t`
  have key : ∀ t < n, g t < n ∧ stableRank a n (g t) = t := by
    intro t ht
    obtain ⟨i, hi, hri⟩ := stableRank_surj (a := a) ht
    obtain ⟨hpi, hgi⟩ := idxOf_spec hperm hi
    have hex : ((List.range out.length).find? fun p => intSortTarget a out p = t).isSome := by
      rw [List.find?_isSome]
      refine ⟨out.idxOf i, List.mem_range.2 hpi, ?_⟩
      simp only [decide_eq_true_eq]
      rw [intSortTarget_eq h (by omega), hgi, hri]
    obtain ⟨p, hfp⟩ := Option.isSome_iff_exists.1 hex
    have hpmem := List.mem_range.1 (List.mem_of_find?_eq_some hfp)
    have hpt : intSortTarget a out p = t := by simpa using List.find?_some hfp
    have hgt : g t = out.getD p 0 := by simp only [hg, hfp, Option.getD_some]
    rw [hgt]
    exact ⟨getD_lt hperm (by omega), by rw [← intSortTarget_eq h (by omega), hpt]⟩
  have hinj : ∀ x ∈ List.range n, ∀ y ∈ List.range n, g x = g y → x = y := by
    intro x hx y hy hxy
    rw [← (key x (List.mem_range.1 hx)).2, ← (key y (List.mem_range.1 hy)).2, hxy]
  rw [hR]
  refine ⟨?_, ?_⟩
  · rw [List.perm_ext_iff_of_nodup (List.nodup_range.map_on hinj) List.nodup_range]
    intro x
    simp only [List.mem_map, List.mem_range]
    constructor
    · rintro ⟨t, ht, rfl⟩; exact (key t ht).1
    · intro hx
      have ht := stableRank_lt (a := a) hx
      refine ⟨stableRank a n x, ht, ?_⟩
      exact stableRank_injOn (key _ ht).1 hx (key _ ht).2
  · rw [List.pairwise_map]
    refine List.pairwise_lt_range.imp_of_mem fun {t t'} ht ht' htt => ?_
    have h1 := key t (List.mem_range.1 ht)
    have h2 := key t' (List.mem_range.1 ht')
    exact lex_of_stableRank_lt h1.1 h2.1 (by omega)

end ISfromSS

/-! ### Correctness of `DS ⪯ IS` -/

/-- **Theorem 4.1(a), `DS ⪯ IS`, correctness.** If `isort` solves every valid `IS` instance
(keys in `[0,n]`), then two passes (low digit, then high digit of `z` in base `n+1`) sort any
valid `DS` instance. Both calls are on valid `IS` instances. -/
theorem distinctSortViaIS_correct (n : ℕ) (isort : (ℕ → ℕ) → List ℕ) (z : ℕ → ℕ)
    (hz : IsDistinctKeyInstance z n ((n + 1) ^ 2))
    (his : ∀ a : ℕ → ℕ, (∀ i < n, a i ≤ n) → IsStableIntSort a n (isort a)) :
    IsDistinctSort z n (distinctSortViaIS n isort z) := by
  set O1 := isort (fun i => z i % (n + 1)) with hO1
  have h1 : IsStableIntSort (fun i => z i % (n + 1)) n O1 :=
    his _ fun i _ => Nat.le_of_lt_succ (Nat.mod_lt _ (by omega))
  have hl1 : O1.length = n := by simpa using h1.1.length_eq
  have hO1lt : ∀ t < n, O1.getD t 0 < n := fun t ht => getD_lt h1.1 ht
  have hq : ∀ i < n, z i / (n + 1) ≤ n := by
    intro i hi
    have := hz.1 i hi
    rw [Nat.pow_two] at this
    exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul (by omega)).2 this)
  set O2 := isort (fun t => z (O1.getD t 0) / (n + 1)) with hO2
  have h2 : IsStableIntSort (fun t => z (O1.getD t 0) / (n + 1)) n O2 :=
    his _ fun t ht => hq _ (hO1lt t ht)
  have hnd1 : O1.Nodup := h1.1.nodup_iff.2 List.nodup_range
  have hnd2 : O2.Nodup := h2.1.nodup_iff.2 List.nodup_range
  have hO2lt : ∀ t ∈ O2, t < n := fun t ht => lt_of_mem_perm_range h2.1 ht
  have hinj : ∀ x ∈ O2, ∀ y ∈ O2, O1.getD x 0 = O1.getD y 0 → x = y := by
    intro x hx y hy hxy
    rw [List.getD_eq_getElem _ _ (by have := hO2lt x hx; omega),
      List.getD_eq_getElem _ _ (by have := hO2lt y hy; omega)] at hxy
    exact hnd1.getElem_inj_iff.1 hxy
  have hpw1 := List.pairwise_iff_getElem.1 h1.2
  -- decomposition of a key into its two digits
  have hz_eq : ∀ i, z i = (n + 1) * (z i / (n + 1)) + z i % (n + 1) := fun i =>
    (Nat.div_add_mod (z i) (n + 1)).symm
  show IsDistinctSort z n (O2.map fun t => O1.getD t 0)
  refine ⟨?_, ?_⟩
  · rw [List.perm_ext_iff_of_nodup (hnd2.map_on hinj) List.nodup_range]
    intro x
    simp only [List.mem_map, List.mem_range]
    constructor
    · rintro ⟨t, ht, rfl⟩; exact hO1lt t (hO2lt t ht)
    · intro hx
      have hmem : x ∈ O1 := h1.1.mem_iff.2 (List.mem_range.2 hx)
      obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.1 hmem
      refine ⟨t, h2.1.mem_iff.2 (List.mem_range.2 (by omega)), ?_⟩
      rw [List.getD_eq_getElem _ _ ht]
  · rw [List.pairwise_map]
    refine h2.2.imp_of_mem fun {t t'} ht ht' hrel => ?_
    have htn := hO2lt t ht
    have htn' := hO2lt t' ht'
    set i := O1.getD t 0
    set j := O1.getD t' 0
    have hr : z i % (n + 1) < n + 1 := Nat.mod_lt _ (by omega)
    have hr' : z j % (n + 1) < n + 1 := Nat.mod_lt _ (by omega)
    rw [hz_eq i, hz_eq j, lex_encode_lt_iff hr hr']
    rcases hrel with hlt | ⟨heq, htt⟩
    · exact Or.inl hlt
    · have heq : z i / (n + 1) = z j / (n + 1) := heq
      refine Or.inr ⟨heq, ?_⟩
      have := hpw1 t t' (by omega) (by omega) htt
      rw [← List.getD_eq_getElem _ 0 (by omega), ← List.getD_eq_getElem _ 0 (by omega)] at this
      rcases this with hlt | ⟨heq', hij⟩
      · exact hlt
      · exfalso
        have heq' : z i % (n + 1) = z j % (n + 1) := heq'
        have hzij : z i = z j := by rw [hz_eq i, hz_eq j, heq, heq']
        have := hz.2 i (hO1lt t htn) j (hO1lt t' htn') hzij
        omega

/-! ### The converse reduction -/

/-- **Converse reduction: `PaddedSort(n,(n+1)^2) ⪯ SS`** (Theorem 4.1(a),(b) with Lemma 2.4;
no unstable semisort is used). If `ssort` returns a stable semisort for every integer-keyed
instance with keys in `[0,n]`, then `paddedSortViaSS` (two `IS` calls, each made of one `SS`
call plus scans and a scatter, then padding with `c = 1`) solves every valid instance of
`PaddedSort(n,(n+1)^2)`. -/
theorem paddedSort_of_stableSemisort (n : ℕ) (ssort : (ℕ → ℕ) → List ℕ)
    (hss : ∀ a : ℕ → ℕ, (∀ i < n, a i ≤ n) → IsStableSemisort a n (ssort a))
    (z : ℕ → ℕ) (hz : IsDistinctKeyInstance z n ((n + 1) ^ 2)) :
    IsPaddedSort z n (paddedSortViaSS n ssort z) :=
  isPaddedSort_map_some (distinctSortViaIS_correct n _ z hz fun a ha =>
    intSortViaSS_correct (hss a ha))

end GC.Semisort
