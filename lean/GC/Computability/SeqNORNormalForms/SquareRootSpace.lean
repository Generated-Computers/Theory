import GC.Computability.SeqNORNormalForms.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Interval.Finset.Nat

/-!
# 006c: the counting obstruction for reset sets, and the subdivision embedding

Reset sets are represented on the positive positions: `R⋆ ∩ [1,n] = {i : x_{j_i} = 1}`.
-/

namespace GC.SeqNORNormalForms

/-- The reset set `R⋆ ∩ {1, …, n} = {i ∈ [1,n] : x_{j_i} = 1}` of an instance. -/
def resetFinset (n : ℕ) (j : ℕ → ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter (fun i => trace j (j i) = true)

/-- The instance of Theorem 6.1: `j_1 = 0`, `j_i = 0` for `i ∈ S`, `j_i = 1` otherwise. -/
def surjInstance (S : Finset ℕ) (i : ℕ) : ℕ := if i ≤ 1 then 0 else if i ∈ S then 0 else 1

theorem trace_one_false (n : ℕ) (j : ℕ → ℕ) (hj : IsParentArray n j) (hn : 1 ≤ n) :
    j 1 = 0 ∧ trace j 1 = false := by
  have h := hj 1 le_rfl hn
  have h0 : j 1 = 0 := by omega
  refine ⟨h0, ?_⟩
  rw [trace_step j 1 0 le_rfl h0 (by omega)]; simp [trace_zero, nor]

/-- **Theorem 6.1 of 006c.** For every `S ⊆ {2, …, n}` the instance `surjInstance S` has
reset set `{1} ∪ S`. -/
theorem surject_instance (n : ℕ) (hn : 1 ≤ n) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 2 n) :
    IsParentArray n (surjInstance S) ∧ resetFinset n (surjInstance S) = insert 1 S := by
  have hpa : IsParentArray n (surjInstance S) := by
    intro i hi hin; unfold surjInstance; split_ifs <;> omega
  refine ⟨hpa, ?_⟩
  have hx1 := (trace_one_false n _ hpa hn).2
  ext i
  simp only [resetFinset, Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert]
  constructor
  · rintro ⟨⟨h1, h2⟩, hx⟩
    by_cases hi1 : i = 1
    · left; exact hi1
    · right
      by_contra hiS
      have : surjInstance S i = 1 := by unfold surjInstance; rw [if_neg (by omega), if_neg hiS]
      rw [this, hx1] at hx; exact absurd hx (by decide)
  · rintro (rfl | hiS)
    · refine ⟨⟨le_rfl, hn⟩, ?_⟩
      have : surjInstance S 1 = 0 := by simp [surjInstance]
      rw [this, trace_zero]
    · have := Finset.mem_Icc.1 (hS hiS)
      refine ⟨⟨by omega, this.2⟩, ?_⟩
      have : surjInstance S i = 0 := by unfold surjInstance; rw [if_neg (by omega), if_pos hiS]
      rw [this, trace_zero]

/-- **Theorem 6.1 of 006c (exact range of reset sets).** The reset sets of instances of
length `n ≥ 1` are exactly the subsets of `{1, …, n}` that contain `1`. -/
theorem reset_sets_exact (n : ℕ) (hn : 1 ≤ n) (T : Finset ℕ) :
    (∃ j, IsParentArray n j ∧ resetFinset n j = T) ↔ T ⊆ Finset.Icc 1 n ∧ 1 ∈ T := by
  constructor
  · rintro ⟨j, hj, rfl⟩
    refine ⟨Finset.filter_subset _ _, ?_⟩
    simp only [resetFinset, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨le_rfl, hn⟩, ?_⟩
    rw [(trace_one_false n j hj hn).1, trace_zero]
  · rintro ⟨hT, h1⟩
    refine ⟨surjInstance (T.erase 1), ?_⟩
    have hS : T.erase 1 ⊆ Finset.Icc 2 n := by
      intro i hi
      have := Finset.mem_Icc.1 (hT (Finset.mem_of_mem_erase hi))
      have := Finset.ne_of_mem_erase hi
      exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
    obtain ⟨hpa, hR⟩ := surject_instance n hn _ hS
    exact ⟨hpa, by rw [hR, Finset.insert_erase h1]⟩

/-- **Theorem 6.1 of 006c (count).** There are exactly `2^{n-1}` such sets. -/
theorem reset_sets_card (n : ℕ) (hn : 1 ≤ n) :
    ((Finset.Icc 1 n).powerset.filter (fun T => 1 ∈ T)).card = 2 ^ (n - 1) := by
  have heq : (Finset.Icc 1 n).powerset.filter (fun T => 1 ∈ T) =
      (Finset.Icc 2 n).powerset.image (insert 1) := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
    constructor
    · rintro ⟨hT, h1⟩
      refine ⟨T.erase 1, ?_, Finset.insert_erase h1⟩
      intro i hi
      have := Finset.mem_Icc.1 (hT (Finset.mem_of_mem_erase hi))
      have := Finset.ne_of_mem_erase hi
      exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
    · rintro ⟨A, hA, rfl⟩
      refine ⟨?_, Finset.mem_insert_self _ _⟩
      intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact Finset.mem_Icc.2 ⟨le_rfl, hn⟩
      · have := Finset.mem_Icc.1 (hA hi); exact Finset.mem_Icc.2 ⟨by omega, this.2⟩
  rw [heq, Finset.card_image_of_injOn, Finset.card_powerset, Nat.card_Icc]
  · rw [show n + 1 - 2 = n - 1 by omega]
  · intro A hA B hB hAB
    have h1A : 1 ∉ A := fun h => by
      have := Finset.mem_Icc.1 ((Finset.mem_powerset.1 hA) h); omega
    have h1B : 1 ∉ B := fun h => by
      have := Finset.mem_Icc.1 ((Finset.mem_powerset.1 hB) h); omega
    have := congrArg (fun T => Finset.erase T 1) hAB
    simpa [Finset.erase_insert h1A, Finset.erase_insert h1B] using this

/-! ### The graph `H_j` (Section 4) -/

/-- The edges of the graph `H_j`: `i - 1 → i` and `j_i → i` for `1 ≤ i ≤ n`. -/
def HEdge (n : ℕ) (j : ℕ → ℕ) (u v : ℕ) : Prop := 1 ≤ v ∧ v ≤ n ∧ (u = v - 1 ∨ u = j v)

/-- **Section 4 of 006c (the source's embedding claim is false).** No graph `H_j` contains two
distinct vertices `c, d` that both have the same two distinct in-neighbours `a, b`. Hence the
directed acyclic graph with sources `a, b` and two vertices `c, d` with in-neighbours `{a, b}`
is not a subgraph of any Sequential NOR graph on the same vertices, under any placement. -/
theorem not_subgraph (n : ℕ) (j : ℕ → ℕ) (hj : IsParentArray n j) (a b c d : ℕ) (hab : a ≠ b)
    (hcd : c ≠ d) (hac : HEdge n j a c) (hbc : HEdge n j b c) (had : HEdge n j a d)
    (hbd : HEdge n j b d) : False := by
  have key : ∀ c d, c < d → HEdge n j a c → HEdge n j b c → HEdge n j a d → HEdge n j b d →
      False := by
    intro c d hlt hac hbc had hbd
    have h1 := hj c hac.1 hac.2.1
    have h2 := hj d had.1 had.2.1
    -- `a, b < c`, and one of `a, b` is `d - 1`
    have ha : a < c := by rcases hac.2.2 with h | h <;> omega
    have hb : b < c := by rcases hbc.2.2 with h | h <;> omega
    rcases had.2.2 with h | h <;> rcases hbd.2.2 with h' | h' <;> omega
  rcases Nat.lt_or_gt_of_ne hcd with h | h
  · exact key c d h hac hbc had hbd
  · exact key d c h had hbd hac hbc

/-- **Lemma 4.3 of 006c (subdivision embedding).** Let a DAG on `v_1, …, v_N` (topological
order) have at most two in-neighbours per vertex, given by `p1 k` (first) and `p2 k`
(second), all `< k`. Put `P(v_k) = 2k`, helper `u_k = 2k - 1`, `j_{2k} = P(a)` for the first
in-neighbour `a` (or `0`), `j_{u_k} = P(b)` for the second in-neighbour `b` (or `0`). Then
`H_j` contains the edge `P(a) → 2k` and the path `P(b) → u_k → 2k`. -/
theorem subdivision_embed (N : ℕ) (p1 p2 : ℕ → Option ℕ)
    (hp1 : ∀ k a, p1 k = some a → 1 ≤ a ∧ a < k) (hp2 : ∀ k b, p2 k = some b → 1 ≤ b ∧ b < k) :
    let j : ℕ → ℕ := fun i =>
      if i % 2 = 0 then (match p1 (i / 2) with | some a => 2 * a | none => 0)
      else (match p2 ((i + 1) / 2) with | some b => 2 * b | none => 0)
    IsParentArray (2 * N) j ∧
    (∀ k a, 1 ≤ k → k ≤ N → p1 k = some a → HEdge (2 * N) j (2 * a) (2 * k)) ∧
    (∀ k b, 1 ≤ k → k ≤ N → p2 k = some b →
      HEdge (2 * N) j (2 * b) (2 * k - 1) ∧ HEdge (2 * N) j (2 * k - 1) (2 * k)) := by
  intro j
  refine ⟨?_, ?_, ?_⟩
  · intro i hi hin
    simp only [j]
    split
    · split
      · next a ha => have := hp1 _ _ ha; omega
      · omega
    · split
      · next b hb => have := hp2 _ _ hb; omega
      · omega
  · intro k a hk hkN ha
    refine ⟨by omega, by omega, Or.inr ?_⟩
    simp only [j, show 2 * k % 2 = 0 by omega, if_true, show 2 * k / 2 = k by omega, ha]
  · intro k b hk hkN hb
    refine ⟨⟨by omega, by omega, Or.inr ?_⟩, ⟨by omega, by omega, Or.inl (by omega)⟩⟩
    simp only [j, show (2 * k - 1) % 2 = 1 by omega, show (2 * k - 1 + 1) / 2 = k by omega, hb]
    simp

end GC.SeqNORNormalForms
