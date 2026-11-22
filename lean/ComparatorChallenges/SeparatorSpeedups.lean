import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Cases
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Order.Lattice.Nat
import Mathlib.Algebra.Group.Action.Defs


namespace GC.Portals

/-- The split point of the interval `[lo, hi]`. -/
def mid (lo hi : ℕ) : ℕ := (lo + hi) / 2

/-- The nodes of the balanced interval tree with root interval `[lo, hi]`. -/
def treeNodes (lo hi : ℕ) : Finset (ℕ × ℕ) :=
  if lo < hi then
    insert (lo, hi) (treeNodes lo (mid lo hi) ∪ treeNodes (mid lo hi + 1) hi)
  else {(lo, hi)}
termination_by hi - lo
decreasing_by all_goals (unfold mid; omega)

/-- The height of the balanced interval tree with root interval `[lo, hi]`. -/
def treeHeight (lo hi : ℕ) : ℕ :=
  if lo < hi then
    max (treeHeight lo (mid lo hi)) (treeHeight (mid lo hi + 1) hi) + 1
  else 0
termination_by hi - lo
decreasing_by all_goals (unfold mid; omega)

/-- The edge `e = (s, t)` is assigned to the node `v = (lo, hi)`: `v` is internal, its left child
`[lo, mid]` contains `s` and its right child `[mid + 1, hi]` contains `t`. -/
def Assigned (v e : ℕ × ℕ) : Prop :=
  v.1 < v.2 ∧ v.1 ≤ e.1 ∧ e.1 ≤ mid v.1 v.2 ∧ mid v.1 v.2 < e.2 ∧ e.2 ≤ v.2

instance (v e : ℕ × ℕ) : Decidable (Assigned v e) := by unfold Assigned; infer_instance

/-- The set `E_v` of edges of `D` assigned to the tree node `v`. -/
def edgesAt (D : Finset (ℕ × ℕ)) (v : ℕ × ℕ) : Finset (ℕ × ℕ) := D.filter (fun e => Assigned v e)

/-- The heavy nodes for threshold `B`: tree nodes with more than `B` assigned edges. -/
def heavyNodes (N B : ℕ) (D : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  (treeNodes 1 N).filter (fun v => B < (edgesAt D v).card)

/-- The number of calls of the recursion `Solve` of Theorem "Online separator transfer", when the
low-subtree algorithm reports failure exactly at the internal nodes satisfying `fail`: `Solve(v)`
makes one call on `v`; on failure it recurses into the two children. -/
def solveCalls (fail : ℕ × ℕ → Prop) [DecidablePred fail] (lo hi : ℕ) : ℕ :=
  if lo < hi ∧ fail (lo, hi) then
    solveCalls fail lo (mid lo hi) + solveCalls fail (mid lo hi + 1) hi + 1
  else 1
termination_by hi - lo
decreasing_by all_goals (unfold mid; omega)

/-- A node is marked if its subtree contains a heavy node. -/
def Marked (D : Finset (ℕ × ℕ)) (B : ℕ) (v : ℕ × ℕ) : Prop :=
  ∃ w ∈ treeNodes v.1 v.2, B < (edgesAt D w).card

/-- The height of the balanced interval tree on `n ≥ 1` stages is `⌈log₂ n⌉`. -/
theorem treeHeight_eq_clog (lo hi : ℕ) (h : lo ≤ hi) :
    treeHeight lo hi = Nat.clog 2 (hi + 1 - lo) := by
  sorry

/-- Lemma (constant-lag chains): every node is assigned at most `c` of the edges `(s, s + c)`. -/
theorem constant_lag (N c : ℕ) (v : ℕ × ℕ) :
    ((Finset.Icc 1 (N - c)).filter (fun s => Assigned v (s, s + c))).card ≤ c := by
  sorry

/-- Lemma (congestion of a padded instance). If every stage is the read end of at most one edge
of `D`, and at most `c₀` edges assigned to `v` have their read end outside a set `J` of stages,
then `|E_v| ≤ |J| + c₀`. -/
theorem congestion (D : Finset (ℕ × ℕ)) (hinj : Set.InjOn Prod.snd (D : Set (ℕ × ℕ)))
    (v : ℕ × ℕ) (J : Finset ℕ) (c₀ : ℕ)
    (hout : ((edgesAt D v).filter (fun e => e.2 ∉ J)).card ≤ c₀) :
    (edgesAt D v).card ≤ J.card + c₀ := by
  sorry

/-- Lemma (linear separator budget): if every edge `(s, t) ∈ D` satisfies `1 ≤ s < t ≤ N` and
every stage is the read end of at most one edge, then `∑_v |E_v| ≤ N - 1` over the nodes of the
balanced interval tree on `[1, N]`. -/
theorem separator_budget (N : ℕ) (D : Finset (ℕ × ℕ))
    (hD : ∀ e ∈ D, 1 ≤ e.1 ∧ e.1 < e.2 ∧ e.2 ≤ N)
    (hinj : Set.InjOn Prod.snd (D : Set (ℕ × ℕ))) :
    ∑ v ∈ treeNodes 1 N, (edgesAt D v).card ≤ N - 1 := by
  sorry

/-- Fewer than `N / B` nodes are heavy: `#heavy · B < N`. -/
theorem heavy_mul_lt (N B : ℕ) (hN : 1 ≤ N) (D : Finset (ℕ × ℕ))
    (hD : ∀ e ∈ D, 1 ≤ e.1 ∧ e.1 < e.2 ∧ e.2 ≤ N)
    (hinj : Set.InjOn Prod.snd (D : Set (ℕ × ℕ))) :
    (heavyNodes N B D).card * B < N := by
  sorry

/-- Lemma (dyadic-to-chronological frontier). If every node `w` of the subtree of `[lo, hi]`
has `|E_w| ≤ B`, then every cut `τ` is crossed by at most `B · height` edges of `D` with both
ends in `[lo, hi]`. -/
theorem frontier_le (D : Finset (ℕ × ℕ)) (lo hi B τ : ℕ)
    (hlow : ∀ w ∈ treeNodes lo hi, (edgesAt D w).card ≤ B) :
    (D.filter (fun e => lo ≤ e.1 ∧ e.1 ≤ τ ∧ τ < e.2 ∧ e.2 ≤ hi)).card ≤
      B * treeHeight lo hi := by
  sorry

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
  sorry

end GC.Portals
