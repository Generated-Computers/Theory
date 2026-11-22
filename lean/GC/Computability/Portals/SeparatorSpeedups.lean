import GC.Computability.Portals.Basic
import Mathlib.Algebra.Group.Action.Defs

/-!
# Separator speedups would put MCVP in NC (manuscript 005a)

We formalize the combinatorics of the balanced interval tree on which the paper rests:

* `constant_lag`: Lemma "Constant-lag chains" — every node is assigned at most `c` of the edges
  `(s, s + c)`;
* `congestion`: Lemma "Congestion of a padded instance" — a node receives at most `M + c₀`
  edges if at most `c₀` of its edges read outside an interval of `M` stages and every stage is
  the read end of at most one edge;
* `separator_budget`, `heavy_mul_lt`: the linear separator budget `∑_v |E_v| ≤ N - 1` (the edge
  sets `E_v` of distinct tree nodes are disjoint) and "fewer than `N / B` heavy nodes";
* `frontier_le`: Lemma "Dyadic-to-chronological frontier" — inside an all-low subtree of height
  `h` every cut is crossed by at most `B h` edges;
* `online_transfer_calls`: the counting in the proof of Theorem "Online separator transfer" —
  the recursion `Solve` makes at most `1 + 2 · #heavy · ⌈log₂ N⌉` calls, and `#heavy · B < N`.

The complexity-theoretic conclusions (MCP ∈ NC, P ⊆ SP) are not formalized.
-/

namespace GC.Portals

/-- The set `E_v` of edges of `D` assigned to the tree node `v`. -/
def edgesAt (D : Finset (ℕ × ℕ)) (v : ℕ × ℕ) : Finset (ℕ × ℕ) := D.filter (fun e => Assigned v e)

/-- Lemma (constant-lag chains): every node is assigned at most `c` of the edges `(s, s + c)`. -/
theorem constant_lag (N c : ℕ) (v : ℕ × ℕ) :
    ((Finset.Icc 1 (N - c)).filter (fun s => Assigned v (s, s + c))).card ≤ c := by
  have hsub : (Finset.Icc 1 (N - c)).filter (fun s => Assigned v (s, s + c)) ⊆
      Finset.Ioc (mid v.1 v.2 - c) (mid v.1 v.2) := by
    intro s hs
    rw [Finset.mem_filter, Finset.mem_Icc] at hs
    obtain ⟨⟨h1, _⟩, h3⟩ := hs
    unfold Assigned at h3
    simp only at h3
    rw [Finset.mem_Ioc]
    omega
  refine (Finset.card_le_card hsub).trans ?_
  simp only [Nat.card_Ioc]
  omega

/-- Lemma (congestion of a padded instance). If every stage is the read end of at most one edge
of `D`, and at most `c₀` edges assigned to `v` have their read end outside a set `J` of stages,
then `|E_v| ≤ |J| + c₀`. -/
theorem congestion (D : Finset (ℕ × ℕ)) (hinj : Set.InjOn Prod.snd (D : Set (ℕ × ℕ)))
    (v : ℕ × ℕ) (J : Finset ℕ) (c₀ : ℕ)
    (hout : ((edgesAt D v).filter (fun e => e.2 ∉ J)).card ≤ c₀) :
    (edgesAt D v).card ≤ J.card + c₀ := by
  rw [← Finset.card_filter_add_card_filter_not (s := edgesAt D v) (fun e => e.2 ∈ J)]
  refine Nat.add_le_add ?_ hout
  refine Finset.card_le_card_of_injOn Prod.snd ?_ ?_
  · intro e he
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at he
    exact he.2
  · intro a ha b hb hab
    simp only [Finset.coe_filter, Set.mem_setOf_eq, edgesAt, Finset.mem_filter] at ha hb
    exact hinj ha.1.1 hb.1.1 hab

/-- Lemma (linear separator budget): if every edge `(s, t) ∈ D` satisfies `1 ≤ s < t ≤ N` and
every stage is the read end of at most one edge, then `∑_v |E_v| ≤ N - 1` over the nodes of the
balanced interval tree on `[1, N]`. -/
theorem separator_budget (N : ℕ) (D : Finset (ℕ × ℕ))
    (hD : ∀ e ∈ D, 1 ≤ e.1 ∧ e.1 < e.2 ∧ e.2 ≤ N)
    (hinj : Set.InjOn Prod.snd (D : Set (ℕ × ℕ))) :
    ∑ v ∈ treeNodes 1 N, (edgesAt D v).card ≤ N - 1 := by
  have h1 : ∑ v ∈ treeNodes 1 N, (edgesAt D v).card =
      ∑ e ∈ D, ((treeNodes 1 N).filter (fun v => Assigned v e)).card := by
    simp only [edgesAt, Finset.card_filter]
    exact Finset.sum_comm
  rw [h1]
  refine (Finset.sum_le_card_nsmul D _ 1 (fun e _ => card_assigned_le_one 1 N e)).trans ?_
  simp only [smul_eq_mul, mul_one]
  have : D.card ≤ (Finset.Icc 2 N).card := by
    refine Finset.card_le_card_of_injOn Prod.snd ?_ hinj
    intro e he
    have := hD e he
    simp only [Finset.coe_Icc, Set.mem_Icc]
    omega
  simpa using this

/-- The heavy nodes for threshold `B`: tree nodes with more than `B` assigned edges. -/
def heavyNodes (N B : ℕ) (D : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  (treeNodes 1 N).filter (fun v => B < (edgesAt D v).card)

/-- Fewer than `N / B` nodes are heavy: `#heavy · B < N`. -/
theorem heavy_mul_lt (N B : ℕ) (hN : 1 ≤ N) (D : Finset (ℕ × ℕ))
    (hD : ∀ e ∈ D, 1 ≤ e.1 ∧ e.1 < e.2 ∧ e.2 ≤ N)
    (hinj : Set.InjOn Prod.snd (D : Set (ℕ × ℕ))) :
    (heavyNodes N B D).card * B < N := by
  have h1 : (heavyNodes N B D).card * (B + 1) ≤ ∑ v ∈ heavyNodes N B D, (edgesAt D v).card := by
    have := Finset.card_nsmul_le_sum (heavyNodes N B D) (fun v => (edgesAt D v).card) (B + 1)
      (fun v hv => by simp only [heavyNodes, Finset.mem_filter] at hv; omega)
    simpa using this
  have h2 : ∑ v ∈ heavyNodes N B D, (edgesAt D v).card ≤
      ∑ v ∈ treeNodes 1 N, (edgesAt D v).card :=
    Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have h3 := separator_budget N D hD hinj
  have : (heavyNodes N B D).card * (B + 1) = (heavyNodes N B D).card * B +
    (heavyNodes N B D).card := by ring
  omega

/-- Lemma (dyadic-to-chronological frontier). If every node `w` of the subtree of `[lo, hi]`
has `|E_w| ≤ B`, then every cut `τ` is crossed by at most `B · height` edges of `D` with both
ends in `[lo, hi]`. -/
theorem frontier_le (D : Finset (ℕ × ℕ)) (lo hi B τ : ℕ)
    (hlow : ∀ w ∈ treeNodes lo hi, (edgesAt D w).card ≤ B) :
    (D.filter (fun e => lo ≤ e.1 ∧ e.1 ≤ τ ∧ τ < e.2 ∧ e.2 ≤ hi)).card ≤
      B * treeHeight lo hi := by
  have hsub : D.filter (fun e => lo ≤ e.1 ∧ e.1 ≤ τ ∧ τ < e.2 ∧ e.2 ≤ hi) ⊆
      (pathNodes lo hi τ).biUnion (edgesAt D) := by
    intro e he
    simp only [Finset.mem_filter] at he
    obtain ⟨heD, h1, h2, h3, h4⟩ := he
    obtain ⟨v, hv, hvA⟩ := exists_pathNode_assigned lo hi τ e h1 h2 h3 h4
    exact Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_filter.mpr ⟨heD, hvA⟩⟩
  refine (Finset.card_le_card hsub).trans ?_
  refine (Finset.card_biUnion_le_card_mul _ _ B
    (fun v hv => hlow v (pathNodes_subset lo hi τ hv))).trans ?_
  rw [mul_comm]
  exact Nat.mul_le_mul_left _ (card_pathNodes_le lo hi τ)

/-- The number of calls of the recursion `Solve` of Theorem "Online separator transfer", when the
low-subtree algorithm reports failure exactly at the internal nodes satisfying `fail`: `Solve(v)`
makes one call on `v`; on failure it recurses into the two children. -/
def solveCalls (fail : ℕ × ℕ → Prop) [DecidablePred fail] (lo hi : ℕ) : ℕ :=
  if lo < hi ∧ fail (lo, hi) then
    solveCalls fail lo (mid lo hi) + solveCalls fail (mid lo hi + 1) hi + 1
  else 1
termination_by hi - lo
decreasing_by all_goals (unfold mid; omega)

theorem solveCalls_le (fail : ℕ × ℕ → Prop) [DecidablePred fail] (lo hi : ℕ) (h : lo ≤ hi) :
    solveCalls fail lo hi ≤
      1 + 2 * ((treeNodes lo hi).filter (fun v => v.1 < v.2 ∧ fail v)).card := by
  induction' hn : hi - lo using Nat.strong_induction_on with k ih generalizing lo hi
  rw [solveCalls]
  split_ifs with hf
  · have hL := ih _ (by unfold mid; omega) lo (mid lo hi) (by unfold mid; omega) rfl
    have hR := ih _ (by unfold mid; omega) (mid lo hi + 1) hi (by unfold mid; omega) rfl
    rw [treeNodes_eq, if_pos hf.1, Finset.filter_insert, if_pos (by exact ⟨hf.1, hf.2⟩),
      Finset.filter_union]
    have hdisj : Disjoint ((treeNodes lo (mid lo hi)).filter (fun v => v.1 < v.2 ∧ fail v))
        ((treeNodes (mid lo hi + 1) hi).filter (fun v => v.1 < v.2 ∧ fail v)) := by
      rw [Finset.disjoint_left]
      intro v h1 h2
      simp only [Finset.mem_filter] at h1 h2
      have a := mem_treeNodes_bounds h1.1
      have b := mem_treeNodes_bounds h2.1
      have c := mem_treeNodes_le (by unfold mid; omega) h1.1
      omega
    have hnot : (lo, hi) ∉ (treeNodes lo (mid lo hi)).filter (fun v => v.1 < v.2 ∧ fail v) ∪
        (treeNodes (mid lo hi + 1) hi).filter (fun v => v.1 < v.2 ∧ fail v) := by
      intro hm
      simp only [Finset.mem_union, Finset.mem_filter] at hm
      rcases hm with hm | hm
      · have := mem_treeNodes_bounds hm.1; unfold mid at this; simp at this; omega
      · have := mem_treeNodes_bounds hm.1; unfold mid at this; simp at this; omega
    rw [Finset.card_insert_of_notMem hnot, Finset.card_union_of_disjoint hdisj]
    omega
  · omega

/-- A node is marked if its subtree contains a heavy node. -/
def Marked (D : Finset (ℕ × ℕ)) (B : ℕ) (v : ℕ × ℕ) : Prop :=
  ∃ w ∈ treeNodes v.1 v.2, B < (edgesAt D w).card

/-- There are at most `#heavy · ⌈log₂ N⌉` marked nodes. -/
theorem card_marked_le (N B : ℕ) (D : Finset (ℕ × ℕ)) (S : Finset (ℕ × ℕ))
    (hS : S ⊆ treeNodes 1 N) (hm : ∀ v ∈ S, Marked D B v) :
    S.card ≤ (heavyNodes N B D).card * Nat.clog 2 N := by
  classical
  have hsub : S ⊆ (heavyNodes N B D).biUnion (fun w => pathNodes 1 N w.1) := by
    intro v hv
    obtain ⟨w, hw, hwB⟩ := hm v hv
    have hwT : w ∈ treeNodes 1 N := mem_treeNodes_trans (hS hv) hw
    obtain ⟨e, he⟩ : (edgesAt D w).Nonempty := Finset.card_pos.mp (by omega)
    have hwint : w.1 < w.2 := (Finset.mem_filter.mp he).2.1
    have hb := mem_treeNodes_bounds hw
    refine Finset.mem_biUnion.mpr ⟨w, Finset.mem_filter.mpr ⟨hwT, hwB⟩, ?_⟩
    exact mem_pathNodes_of_mem (hS hv) (by omega) hb.1 (by omega)
  refine (Finset.card_le_card hsub).trans ?_
  refine Finset.card_biUnion_le_card_mul _ _ _ (fun w _ => ?_)
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0
    rw [pathNodes_eq, if_neg (by omega)]; simp
  · have := card_pathNodes_le 1 N w.1
    rw [treeHeight_eq_clog 1 N hpos] at this
    simpa using this

/-- Theorem (online separator transfer), counting part. Let `D` be a set of write–read edges
`(s, t)` with `1 ≤ s < t ≤ N`, each stage the read end of at most one edge. If the low-subtree
algorithm reports failure only at marked nodes, the recursion `Solve(root)` makes at most
`1 + 2 · #heavy · ⌈log₂ N⌉` calls, and `#heavy · B < N`. -/
theorem online_transfer_calls (N B : ℕ) (hN : 1 ≤ N) (D : Finset (ℕ × ℕ))
    (hD : ∀ e ∈ D, 1 ≤ e.1 ∧ e.1 < e.2 ∧ e.2 ≤ N)
    (hinj : Set.InjOn Prod.snd (D : Set (ℕ × ℕ)))
    (fail : ℕ × ℕ → Prop) [DecidablePred fail]
    (hfail : ∀ v ∈ treeNodes 1 N, v.1 < v.2 → fail v → Marked D B v) :
    solveCalls fail 1 N ≤ 1 + 2 * ((heavyNodes N B D).card * Nat.clog 2 N) ∧
      (heavyNodes N B D).card * B < N := by
  refine ⟨(solveCalls_le fail 1 N hN).trans ?_, heavy_mul_lt N B hN D hD hinj⟩
  have := card_marked_le N B D ((treeNodes 1 N).filter (fun v => v.1 < v.2 ∧ fail v))
    (Finset.filter_subset _ _) (fun v hv => by
      simp only [Finset.mem_filter] at hv
      exact hfail v hv.1 hv.2.1 hv.2.2)
  omega

end GC.Portals
