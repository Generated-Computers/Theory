import GC.Computability.Portals.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.Finset.Card

/-!
# Fanout height bounds parallel evaluation depth (manuscript 005e)

A program is a directed acyclic graph on node indices (`Edge u v`: `u` is an operand of `v`),
with a distinguished set `H` of fanout nodes. Paths are lists `l` with `l.IsChain Edge`; the
fanout height `d(C)` is the maximum number of `H`-nodes on a path.

* `rounds_bound`: the round structure of Theorem "Fanout-height compiler". A node is computed in
  round `j + 1` as soon as every *skeleton predecessor* (an `H`-node with a path to it whose
  internal vertices avoid `H`) was computed in round `j`. If every path carries at most `d`
  fanout nodes, every node is computed after `d + 1` rounds.
* `seqnor_fanout_set`, `seqnor_fanout_height`: Proposition "Fanout height of Sequential NOR":
  `H = {j₁, …, jₙ}` and `d(C) = h`.
* `search_first_stop_le` (in `Basic`): the stopping rule of Corollary "Searching for the best
  rank".

Not formalized: the per-round formula evaluation (tree contraction) and its depth, the
equality-assisted redirection, and the tensor-network results of Section 4 (copy-context normal
form, Hopf identities, copy-tensor rank, low-copy-debt compiler).
-/

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

theorem hcount_append (l₁ l₂ : List ℕ) : hcount H (l₁ ++ l₂) = hcount H l₁ + hcount H l₂ := by
  simp [hcount, List.filter_append]

theorem hcount_cons_mem {u : ℕ} (hu : u ∈ H) (l : List ℕ) : hcount H (u :: l) = hcount H l + 1 := by
  simp [hcount, List.filter_cons, hu]

theorem hcount_eq_zero {l : List ℕ} (hl : ∀ w ∈ l, w ∉ H) : hcount H l = 0 := by
  simp only [hcount, List.length_eq_zero_iff, List.filter_eq_nil_iff, decide_eq_true_eq]
  exact hl

theorem known_of_paths (j : ℕ) (v : ℕ)
    (hv : ∀ p : List ℕ, (p ++ [v]).IsChain Edge → hcount H p ≤ j) :
    v ∈ known Edge H (j + 1) := by
  induction j generalizing v with
  | zero =>
    intro u ⟨hu, l, hl, hlH⟩
    have := hv (u :: l) (by simpa using hl)
    rw [hcount_cons_mem H hu] at this
    omega
  | succ j ih =>
    intro u ⟨hu, l, hl, hlH⟩
    apply ih
    intro p hp
    have hchain : (p ++ [u] ++ (l ++ [v])).IsChain Edge :=
      List.IsChain.append_overlap hp (by simpa using hl) (List.cons_ne_nil _ _)
    have := hv (p ++ [u] ++ l) (by simpa [List.append_assoc] using hchain)
    rw [hcount_append, hcount_append, hcount_eq_zero H hlH,
      show hcount H [u] = 1 by simp [hcount, hu]] at this
    omega

/-- Round bound of the fanout-height compiler: if every path has at most `d` fanout nodes,
every node is computed after `d + 1` rounds. -/
theorem rounds_bound (d : ℕ) (hd : ∀ l : List ℕ, l.IsChain Edge → hcount H l ≤ d) (v : ℕ) :
    v ∈ known Edge H (d + 1) := by
  apply known_of_paths
  intro p hp
  have := hd _ hp
  rw [hcount_append] at this
  omega

/-- On an acyclic graph (`Edge u v → u < v`) a path carries at most `|H|` fanout nodes, so
`d(C) ≤ h`. -/
theorem hcount_le_card (hacyc : ∀ u v, Edge u v → u < v) (l : List ℕ) (hl : l.IsChain Edge) :
    hcount H l ≤ H.card := by
  have hnd : l.Nodup := by
    have : l.IsChain (· < ·) := hl.imp (fun u v h => hacyc u v h)
    exact (List.isChain_iff_pairwise.mp this).nodup
  have hnd' := hnd.filter (fun x => decide (x ∈ H))
  unfold hcount
  rw [← List.toFinset_card_of_nodup hnd']
  apply Finset.card_le_card
  intro x hx
  simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hx
  exact hx.2

end Rounds

section SeqNOR

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
  have hfirst : ∀ k, ((Finset.Icc 1 n).filter (fun i => i - 1 = k)).card ≤ 1 := by
    intro k
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter, Finset.mem_Icc] at ha hb
    omega
  ext k
  rw [seqnorFanout, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
  unfold seqnorOutdeg
  simp only [Finset.mem_Icc]
  constructor
  · rintro ⟨_, h2⟩
    have h1 := hfirst k
    obtain ⟨i, hi⟩ : ((Finset.Icc 1 n).filter (fun i => j i = k)).Nonempty :=
      Finset.card_pos.mp (by omega)
    simp only [Finset.mem_filter, Finset.mem_Icc] at hi
    exact ⟨i, hi.1, hi.2⟩
  · rintro ⟨i, hi, rfl⟩
    have hji := hj i hi.1 hi.2
    refine ⟨by omega, ?_⟩
    have a1 : 1 ≤ ((Finset.Icc 1 n).filter (fun i' => i' - 1 = j i)).card :=
      Finset.card_pos.mpr ⟨j i + 1, by simp only [Finset.mem_filter, Finset.mem_Icc]; omega⟩
    have a2 : 1 ≤ ((Finset.Icc 1 n).filter (fun i' => j i' = j i)).card :=
      Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr hi, rfl⟩⟩
    omega

theorem isChain_range_seqnor (n : ℕ) (j : ℕ → ℕ) :
    (List.range (n + 1)).IsChain (seqnorEdge n j) := by
  rw [List.isChain_iff_getElem]
  intro i hi
  simp only [List.length_range] at hi
  simp only [List.getElem_range, seqnorEdge]
  omega

/-- Proposition (Sequential NOR), second part: the fanout height equals `h = |H|`: no path
carries more than `h` fanout nodes, and the chain `x₀ → x₁ → ⋯ → xₙ` carries all of them. -/
theorem seqnor_fanout_height (n : ℕ) (j : ℕ → ℕ) (hj : ∀ i, 1 ≤ i → i ≤ n → j i < i) :
    (∀ l : List ℕ, l.IsChain (seqnorEdge n j) →
        hcount (seqnorFanout n j) l ≤ (seqnorFanout n j).card) ∧
      ∃ l : List ℕ, l.IsChain (seqnorEdge n j) ∧
        hcount (seqnorFanout n j) l = (seqnorFanout n j).card := by
  refine ⟨hcount_le_card _ _ (fun u v ⟨h1, h2, h3⟩ => ?_), List.range (n + 1),
    isChain_range_seqnor n j, ?_⟩
  · rcases h3 with rfl | rfl
    · omega
    · exact hj v h1 h2
  · have hnd : ((List.range (n + 1)).filter (fun x => decide (x ∈ seqnorFanout n j))).Nodup :=
      (List.nodup_range).filter _
    unfold hcount
    rw [← List.toFinset_card_of_nodup hnd]
    congr 1
    ext k
    simp only [List.mem_toFinset, List.mem_filter, List.mem_range, decide_eq_true_eq,
      and_iff_right_iff_imp]
    intro hk
    simp only [seqnorFanout, Finset.mem_filter, Finset.mem_range] at hk
    exact hk.1

end SeqNOR

end GC.Portals
