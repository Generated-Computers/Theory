import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Chain
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.OfFn
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

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

/-- The load `ℓ_v = ∑_{e ∋ v} y_e` of a vertex. -/
def load (y : V × V → ℝ) (v : V) : ℝ :=
  ∑ e ∈ G.fusion, y e * ((if e.1 = v then 1 else 0) + (if e.2 = v then 1 else 0))

/-- The path marginal `p_v = ∑_{P ∋ v} λ_P` of a finitely supported path weighting. -/
def marg (Λ : Finset (List V)) (lam : List V → ℝ) (v : V) : ℝ :=
  ∑ P ∈ Λ, if v ∈ P then lam P else 0

/-- Feasibility for the path-flow fusion-packing dual of Theorem 3.1: `y ≥ 0`, `λ ≥ 0` supported
on directed paths with total mass at most one, and `∑_{e ∋ v} y_e ≤ p_v` for every `v`. -/
def DualFeasible (y : V × V → ℝ) (Λ : Finset (List V)) (lam : List V → ℝ) : Prop :=
  (∀ e, 0 ≤ y e) ∧ (∀ P ∈ Λ, G.IsPath P) ∧ (∀ P, 0 ≤ lam P) ∧ (∑ P ∈ Λ, lam P ≤ 1) ∧
    ∀ v, G.load y v ≤ marg Λ lam v

variable {G}

/-- **Theorem 3.1, weak duality.** For every primal-feasible `(x, d)` with `d ≥ 0` and every
dual-feasible `(y, λ)`, `∑_e y_e ≤ d`. Hence every dual-feasible pair certifies `δ(C) ≥ ∑ y_e`. -/
theorem weak_duality {x : V → ℝ} {d : ℝ} (hx : G.LoadFeasible x d) (hd : 0 ≤ d)
    {y : V × V → ℝ} {Λ : Finset (List V)} {lam : List V → ℝ}
    (hy : G.DualFeasible y Λ lam) :
    ∑ e ∈ G.fusion, y e ≤ d := by
  sorry

/-- `e` crosses `(P, Q)`: one endpoint on `P` and the other on `Q`. -/
def Crosses (e : V × V) (P Q : List V) : Prop := (e.1 ∈ P ∧ e.2 ∈ Q) ∨ (e.2 ∈ P ∧ e.1 ∈ Q)

instance (e : V × V) (P Q : List V) : Decidable (Crosses e P Q) := by
  unfold Crosses; infer_instance

variable {y : V × V → ℝ} {Λ : Finset (List V)} {lam : List V → ℝ}

/-- The probability weight `λ_P λ_Q` of a pair of independently drawn paths. -/
def pw (lam : List V → ℝ) (pq : List V × List V) : ℝ := lam pq.1 * lam pq.2

/-- **Theorem 4.2 (two-path concentration).** Let `(y, λ)` be dual feasible with
`∑_P λ_P = 1`, `D = ∑_e y_e` and `s = |supp y|`. Then some two paths `P₀, Q₀` of the support
of `λ` are crossed by at least `D²/s` pairs of `supp y`, and some two paths `P₁, Q₁` carry crossing
dual weight at least `D³/s²`. -/
theorem concentration (hy : ∀ e, 0 ≤ y e) (hlam : ∀ P, 0 ≤ lam P)
    (hsum : ∑ P ∈ Λ, lam P = 1) (hload : ∀ v, G.load y v ≤ marg Λ lam v) :
    (∃ P ∈ Λ, ∃ Q ∈ Λ, (∑ e ∈ G.fusion, y e) ^ 2 / (G.fusion.filter (y · ≠ 0)).card ≤
      (((G.fusion.filter (y · ≠ 0)).filter (fun e => Crosses e P Q)).card : ℝ)) ∧
    (∃ P ∈ Λ, ∃ Q ∈ Λ, (∑ e ∈ G.fusion, y e) ^ 3 / ((G.fusion.filter (y · ≠ 0)).card) ^ 2 ≤
      ∑ e ∈ G.fusion, if Crosses e P Q then y e else 0) := by
  sorry

/-- **Theorem 4.2, incomparable case.** If no path of the support of `λ` contains both vertices
of a pair of `supp y` (as when the two parents of every fusion are incomparable), both bounds hold
with an extra factor `2`. -/
theorem concentration_incomparable (hy : ∀ e, 0 ≤ y e) (hlam : ∀ P, 0 ≤ lam P)
    (hsum : ∑ P ∈ Λ, lam P = 1) (hload : ∀ v, G.load y v ≤ marg Λ lam v)
    (hinc : ∀ e ∈ G.fusion, y e ≠ 0 → ∀ P ∈ Λ, ¬ (e.1 ∈ P ∧ e.2 ∈ P)) :
    (∃ P ∈ Λ, ∃ Q ∈ Λ, 2 * ((∑ e ∈ G.fusion, y e) ^ 2 / (G.fusion.filter (y · ≠ 0)).card) ≤
      (((G.fusion.filter (y · ≠ 0)).filter (fun e => Crosses e P Q)).card : ℝ)) ∧
    (∃ P ∈ Λ, ∃ Q ∈ Λ,
      2 * ((∑ e ∈ G.fusion, y e) ^ 3 / ((G.fusion.filter (y · ≠ 0)).card) ^ 2) ≤
      ∑ e ∈ G.fusion, if Crosses e P Q then y e else 0) := by
  sorry

end CarrierGraph

/-- A single arc `u → w` (`u = 0`, `w = 1`) with fusion pair `{u, w}`. -/
def arcGraph : CarrierGraph (Fin 2) where
  arc u v := u = 0 ∧ v = 1
  fusion := {(0, 1)}

/-- **Example 4.3.** For a single arc `u → w` with `E_f = {{u, w}}`, the pair `y = 1`,
`λ = δ_{u → w}` is dual feasible with `D = s = 1`, but no two paths are crossed by more than one
pair, so the bound `2 D²/s = 2` of the incomparable case fails. -/
theorem factorTwo_example :
    arcGraph.DualFeasible (fun _ => 1) {[0, 1]} (fun _ => 1) ∧
    ∀ P Q : List (Fin 2),
      (((arcGraph.fusion.filter (fun _ => (1 : ℝ) ≠ 0)).filter
        (fun e => CarrierGraph.Crosses e P Q)).card : ℝ) <
      2 * ((∑ e ∈ arcGraph.fusion, (1 : ℝ)) ^ 2 /
        (arcGraph.fusion.filter (fun _ => (1 : ℝ) ≠ 0)).card) := by
  sorry

/-- Two unary rails `A_0 → ⋯ → A_{h-1}` and `B_0 → ⋯ → B_{h-1}` (`Sum.inl i = A_i`,
`Sum.inr (Sum.inl j) = B_j`) and readout fusions `Z_r = ψ_r(A_{ra r}, B_{rb r})`
(`Sum.inr (Sum.inr r) = Z_r`) that feed nothing. -/
def railGraph (h : ℕ) {ρ : Type*} [DecidableEq ρ] (ra rb : ρ → Fin h) [Fintype ρ] :
    CarrierGraph (Fin h ⊕ Fin h ⊕ ρ) where
  arc u v := match u, v with
    | .inl i, .inl j => j.val = i.val + 1
    | .inr (.inl i), .inr (.inl j) => j.val = i.val + 1
    | .inl i, .inr (.inr r) => ra r = i
    | .inr (.inl i), .inr (.inr r) => rb r = i
    | _, _ => False
  fusion := univ.image (fun r => (Sum.inl (ra r), Sum.inr (Sum.inl (rb r))))

section Rails

variable {h : ℕ} {ρ : Type*} [Fintype ρ] [DecidableEq ρ] {ra rb : ρ → Fin h}

/-- Not on the `B` rail. -/
def notB : Fin h ⊕ Fin h ⊕ ρ → Bool
  | .inr (.inl _) => false
  | _ => true

/-- Not on the `A` rail. -/
def notA : Fin h ⊕ Fin h ⊕ ρ → Bool
  | .inl _ => false
  | _ => true

/-- **Theorem 5.1 and Proposition 5.2 (`δ = h/2`).** For two unary rails of length `h ≥ 1` and
any family of readouts `Z_r = ψ_r(A_{ra r}, B_{rb r})` that contains a perfect matching
`{A_i, B_{π i}}` (the matched-rail mirage for one permutation `π`, or the complete readout grid),
weight `1/2` on every rail vertex is a feasible fractional load of value `h/2`, and every feasible
fractional load has value at least `h/2`. -/
theorem railGraph_load (hh : 1 ≤ h) (π : Equiv.Perm (Fin h))
    (hπ : ∀ i, ∃ r, ra r = i ∧ rb r = π i) :
    (railGraph h ra rb).LoadFeasible (fun v => match v with
      | .inr (.inr _) => 0
      | _ => 1 / 2) (h / 2) ∧
    ∀ x d, (railGraph h ra rb).LoadFeasible x d → (h : ℝ) / 2 ≤ d := by
  sorry

/-- The matched-rail mirage for a permutation `π`: readouts `Z_i = ψ_i(A_i, B_{π i})`. -/
abbrev mirage (h : ℕ) (π : Equiv.Perm (Fin h)) :
    CarrierGraph (Fin h ⊕ Fin h ⊕ Fin h) := railGraph h id π

/-- **Theorem 5.1 (integral catalyst height of the mirage).** Every catalyst cover of the
matched-rail mirage has a rail containing at least `h/2` of its nodes, and the cover
`{A_i : i < ⌈h/2⌉} ∪ {B_{π i} : i ≥ ⌈h/2⌉}` has height `⌈h/2⌉`. Hence `χ = ⌈h/2⌉`. -/
theorem mirage_height (hh : 1 ≤ h) (π : Equiv.Perm (Fin h)) :
    (∀ H, (mirage h π).IsCatalystCover H →
      ∃ P, (mirage h π).IsPath P ∧ h ≤ 2 * CarrierGraph.coverCount H P) ∧
    ∃ H, (mirage h π).IsCatalystCover H ∧ (mirage h π).HeightLE H ((h + 1) / 2) := by
  sorry

end Rails

end GC.FlowCircuits
