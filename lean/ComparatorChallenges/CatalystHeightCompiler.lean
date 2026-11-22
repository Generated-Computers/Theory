import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.Chain
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.OfFn
import Mathlib.Logic.Relation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-! Comparator challenge for result family 003 (generated from the solution files: the
definitions are verbatim, the main theorems are stated with `sorry`). -/

namespace GC.FlowCircuits

open Finset

/-- A carrier graph: arcs and fusion pairs. -/
structure CarrierGraph (V : Type*) where
  arc : V → V → Prop
  fusion : Finset (V × V)

namespace CarrierGraph

variable {V : Type*} [DecidableEq V] (G : CarrierGraph V)

/-- A nonempty directed path. -/
def IsPath (P : List V) : Prop := P ≠ [] ∧ P.IsChain G.arc

/-- The weight `∑_{v ∈ P} x_v` of a path. -/
def weight (x : V → ℝ) (P : List V) : ℝ := ∑ v ∈ P.toFinset, x v

/-- `H` is a catalyst cover: it contains a parent of every fusion. -/
def IsCatalystCover (H : Finset V) : Prop := ∀ e ∈ G.fusion, e.1 ∈ H ∨ e.2 ∈ H

/-- The number `|P ∩ H|` of cover nodes on a path. -/
def coverCount (H : Finset V) (P : List V) : ℕ := (P.toFinset.filter (· ∈ H)).card

/-- `cht(H) ≤ k`: every directed path contains at most `k` nodes of `H`. -/
def HeightLE (H : Finset V) (k : ℕ) : Prop := ∀ P, G.IsPath P → coverCount H P ≤ k

/-- Feasibility for the fractional catalyst load (003b, Definition 2.1): `x ≥ 0`,
`x_u + x_w ≥ 1` on fusion pairs, and every path has weight at most `d`. -/
def LoadFeasible (x : V → ℝ) (d : ℝ) : Prop :=
  (∀ v, 0 ≤ x v) ∧ (∀ e ∈ G.fusion, 1 ≤ x e.1 + x e.2) ∧ ∀ P, G.IsPath P → weight x P ≤ d

/-- Fractional feasibility (003e, Definition 5.1): as `LoadFeasible` with `x ∈ [0,1]^V`. -/
def FracFeasible (x : V → ℝ) (d : ℝ) : Prop :=
  (∀ v, 0 ≤ x v ∧ x v ≤ 1) ∧ (∀ e ∈ G.fusion, 1 ≤ x e.1 + x e.2) ∧
    ∀ P, G.IsPath P → weight x P ≤ d

end CarrierGraph

end GC.FlowCircuits

namespace GC.FlowCircuits

open Finset

namespace CarrierGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : CarrierGraph V)

/-- The threshold set `{v : x_v ≥ 1/2}`. -/
noncomputable def threshold (x : V → ℝ) : Finset V := by
  classical
  exact univ.filter (fun v => 1 / 2 ≤ x v)

variable {G}

/-- **Theorem 5.2 (factor-two rounding).** If `(x, d)` is fractionally feasible, then
`H = {v : x_v ≥ 1/2}` is a catalyst cover and every directed path contains at most `2d` of its
nodes. -/
theorem rounding {x : V → ℝ} {d : ℝ} (hx : G.FracFeasible x d) :
    G.IsCatalystCover (threshold x) ∧
      ∀ P, G.IsPath P → (coverCount (threshold x) P : ℝ) ≤ 2 * d := by
  sorry

/-- A catalyst cover `H` of height at most `k` gives the fractionally feasible pair
`(1_H, k)`. -/
theorem cover_fracFeasible {H : Finset V} {k : ℕ} (hH : G.IsCatalystCover H)
    (hk : G.HeightLE H k) :
    G.FracFeasible (fun v => if v ∈ H then 1 else 0) k := by
  sorry

/-- **Theorem 5.2 (`d* ≤ χ ≤ 2 d*`).** A catalyst cover of height `≤ k` gives a fractional
certificate of value `k`, and a fractional certificate of value `d` rounds to a catalyst cover
meeting every path in at most `2d` nodes. -/
theorem integrality_gap_two :
    (∀ (H : Finset V) (k : ℕ), G.IsCatalystCover H → G.HeightLE H k →
      ∃ x : V → ℝ, G.FracFeasible x k) ∧
    (∀ (x : V → ℝ) (d : ℝ), G.FracFeasible x d →
      ∃ H, G.IsCatalystCover H ∧ ∀ P, G.IsPath P → (coverCount H P : ℝ) ≤ 2 * d) := by
  sorry

/-- **Lemma 5.3 (path potentials), "if" direction.** If `x ≥ 0` and numbers `p_v` satisfy
`p_v ≥ x_v`, `p_v ≥ p_u + x_v` for every arc `u → v`, and `p_v ≤ d`, then every directed path has
`x`-weight at most `d`. -/
theorem weight_le_of_potentials (x p : V → ℝ) (d : ℝ) (hx : ∀ v, 0 ≤ x v)
    (h1 : ∀ v, x v ≤ p v) (h2 : ∀ u v, G.arc u v → p u + x v ≤ p v) (h3 : ∀ v, p v ≤ d) :
    ∀ P, G.IsPath P → weight x P ≤ d := by
  sorry

/-- **Batch-side accumulator (Theorem 4.1).** A catalyst cover consisting of sources (nodes without
incoming arcs) has height at most one. -/
theorem heightLE_one_of_sources (H : Finset V) (hsrc : ∀ h ∈ H, ∀ u, ¬ G.arc u h) :
    G.HeightLE H 1 := by
  sorry

end CarrierGraph

/-- One fusion `v = ψ(u, w)` of two sources `u = 0`, `w = 1`, with `v = 2`. -/
def tightGraph : CarrierGraph (Fin 3) where
  arc u v := (u = 0 ∨ u = 1) ∧ v = 2
  fusion := {(0, 1)}

/-- **Tightness in Theorem 5.2.** For one fusion of two sources, `d* = 1/2` while the least
catalyst height is `χ = 1`. -/
theorem tightGraph_gap :
    tightGraph.FracFeasible ![1 / 2, 1 / 2, 0] (1 / 2) ∧
    (∀ x d, tightGraph.FracFeasible x d → 1 / 2 ≤ d) ∧
    (tightGraph.IsCatalystCover {0} ∧ tightGraph.HeightLE {0} 1) ∧
    (∀ H, tightGraph.IsCatalystCover H → ¬ tightGraph.HeightLE H 0) := by
  sorry

section Compiler

variable {V : Type*} (par : V → Finset V)

/-- Parent relation `u → v` (`u` is a predecessor of `v`). -/
def ParRel (u v : V) : Prop := u ∈ par v

/-- The closed ancestor cone `C_r` of the cover nodes of level `r`. -/
def InCone (H : Finset V) (ℓ : V → ℕ) (r : ℕ) (v : V) : Prop :=
  ∃ h ∈ H, ℓ h = r ∧ Relation.ReflTransGen (ParRel par) v h

/-- Nodes known before round `r`: the sources and the cones `C_s`, `s < r`. -/
def KnownBefore (H : Finset V) (ℓ : V → ℕ) (r : ℕ) (v : V) : Prop :=
  par v = ∅ ∨ ∃ s < r, InCone par H ℓ s v

/-- **Theorem 3.2, combinatorial core.** Let every node have at most two predecessors, let `H` be
a catalyst cover (every node with two predecessors has one in `H`), and let `ℓ` be a grading of
`H` that strictly increases along proper ancestry inside `H` (for instance the levels `ℓ_H`, whose
maximum is `cht(H)`). Then in round `r` every node of the cone `C_r` has at most one predecessor
that is not known before round `r`; that is, `C_r` is functional relative to the known nodes, so
`cht(H)` rounds of functional closure (plus one final round, `functional_rel_cover`) evaluate the
circuit. -/
theorem compiler_round_functional (hdeg : ∀ v, (par v).card ≤ 2) (H : Finset V)
    (hH : ∀ v, (par v).card = 2 → ∃ u ∈ par v, u ∈ H) (ℓ : V → ℕ)
    (hℓ : ∀ h ∈ H, ∀ h' ∈ H, Relation.TransGen (ParRel par) h' h → ℓ h' < ℓ h)
    (r : ℕ) (v : V) (hv : InCone par H ℓ r v) :
    ∀ u₁ ∈ par v, ∀ u₂ ∈ par v, ¬ KnownBefore par H ℓ r u₁ → ¬ KnownBefore par H ℓ r u₂ →
      u₁ = u₂ := by
  sorry

/-- **Theorem 2.4 (joint catalyst composition), combinatorial core.** Relative to a catalyst
cover `H`, every node has at most one predecessor outside `H`. -/
theorem functional_rel_cover (hdeg : ∀ v, (par v).card ≤ 2) (H : Finset V)
    (hH : ∀ v, (par v).card = 2 → ∃ u ∈ par v, u ∈ H) (v : V) :
    ∀ u₁ ∈ par v, ∀ u₂ ∈ par v, u₁ ∉ H → u₂ ∉ H → u₁ = u₂ := by
  sorry

end Compiler

/-- The two-register recurrence `a_t = ψ_t(a_{t-1}, b_{t-1})`, `b_t = ψ'_t(a_{t-1}, b_{t-1})`,
`1 ≤ t ≤ m`: vertices `(t, false) = a_t`, `(t, true) = b_t`; both registers of level `t` are
predecessors of both registers of level `t + 1`; the fusion pairs are `{a_t, b_t}`, `t < m`. -/
def twoRegister (m : ℕ) : CarrierGraph (Fin (m + 1) × Bool) where
  arc u v := v.1.val = u.1.val + 1
  fusion := (univ.filter (fun t : Fin (m + 1) => t.val < m)).image (fun t => ((t, false), (t, true)))

/-- **Example 4.2.** Every catalyst cover of the two-register recurrence of length `m ≥ 1` has a
directed path containing `m` of its nodes, so its height is at least `m`. -/
theorem twoRegister_height (m : ℕ) (hm : 1 ≤ m) (H : Finset (Fin (m + 1) × Bool))
    (hH : (twoRegister m).IsCatalystCover H) :
    ∃ P, (twoRegister m).IsPath P ∧ m ≤ CarrierGraph.coverCount H P := by
  sorry

end GC.FlowCircuits
