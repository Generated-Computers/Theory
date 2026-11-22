import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Cases
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.List.Chain
import Mathlib.Data.Finset.Card


namespace GC.Portals

section Rounds

variable (Edge : ℕ → ℕ → Prop) (H : Finset ℕ)

/-- The number of fanout nodes on a path. -/
def hcount (l : List ℕ) : ℕ := (l.filter (· ∈ H)).length

/-- `u` is a skeleton predecessor of `v`: `u ∈ H` and there is a path `u, w₁, …, w_r, v` whose
internal vertices `wᵢ` avoid `H`. -/
def SkelArc (u v : ℕ) : Prop :=
  u ∈ H ∧ ∃ l : List ℕ, (u :: l ++ [v]).IsChain Edge ∧ ∀ w ∈ l, w ∉ H

/-- The nodes known after `j` rounds: round `j + 1` computes every node all of whose skeleton
predecessors are known after round `j` (by `Lemma "Formula forests"` such a node is a formula
in those predecessors and the terminals). -/
def known : ℕ → Set ℕ
  | 0 => ∅
  | j + 1 => {v | ∀ u, SkelArc Edge H u v → u ∈ known j}

/-- Round bound of the fanout-height compiler: if every path has at most `d` fanout nodes,
every node is computed after `d + 1` rounds. -/
theorem rounds_bound (d : ℕ) (hd : ∀ l : List ℕ, l.IsChain Edge → hcount H l ≤ d) (v : ℕ) :
    v ∈ known Edge H (d + 1) := by
  sorry

/-- On an acyclic graph (`Edge u v → u < v`) a path carries at most `|H|` fanout nodes, so
`d(C) ≤ h`. -/
theorem hcount_le_card (hacyc : ∀ u v, Edge u v → u < v) (l : List ℕ) (hl : l.IsChain Edge) :
    hcount H l ≤ H.card := by
  sorry

end Rounds

/-- The operand edges of the Sequential NOR program with parent array `j`: node `v ∈ [1, n]` has
the operands `v - 1` and `j v`. -/
def seqnorEdge (n : ℕ) (j : ℕ → ℕ) (u v : ℕ) : Prop := 1 ≤ v ∧ v ≤ n ∧ (u = v - 1 ∨ u = j v)

/-- The out-degree of node `k`, counted with multiplicity. -/
def seqnorOutdeg (n : ℕ) (j : ℕ → ℕ) (k : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter (fun i => i - 1 = k)).card +
    ((Finset.Icc 1 n).filter (fun i => j i = k)).card

/-- The fanout set `H = {k : outdeg k ≥ 2}`. -/
def seqnorFanout (n : ℕ) (j : ℕ → ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun k => 2 ≤ seqnorOutdeg n j k)

/-- Proposition (Sequential NOR), first part: `H = {j₁, …, jₙ}`. -/
theorem seqnor_fanout_set (n : ℕ) (j : ℕ → ℕ) (hj : ∀ i, 1 ≤ i → i ≤ n → j i < i) :
    seqnorFanout n j = (Finset.Icc 1 n).image j := by
  sorry

/-- Proposition (Sequential NOR), second part: the fanout height equals `h = |H|`: no path
carries more than `h` fanout nodes, and the chain `x₀ → x₁ → ⋯ → xₙ` carries all of them. -/
theorem seqnor_fanout_height (n : ℕ) (j : ℕ → ℕ) (hj : ∀ i, 1 ≤ i → i ≤ n → j i < i) :
    (∀ l : List ℕ, l.IsChain (seqnorEdge n j) →
        hcount (seqnorFanout n j) l ≤ (seqnorFanout n j).card) ∧
      ∃ l : List ℕ, l.IsChain (seqnorEdge n j) ∧
        hcount (seqnorFanout n j) l = (seqnorFanout n j).card := by
  sorry

/-- The search of Corollary "One-shot criterion" (005c) and Corollary "Searching for the best
rank" (005e): after rank `K` it knows `β_K = min_{K' ≤ K} (K' + c K')` and stops at the first `K`
with `β_K ≤ K`. The first stopping rank is at most `Φ = min_K (K + c K)`. -/
theorem search_first_stop_le (c : ℕ → ℕ) (K₀ : ℕ)
    (hfirst : ∀ K < K₀, ¬ ∃ K' ≤ K, K' + c K' ≤ K) :
    K₀ ≤ sInf (Set.range fun K => K + c K) := by
  sorry

end GC.Portals
