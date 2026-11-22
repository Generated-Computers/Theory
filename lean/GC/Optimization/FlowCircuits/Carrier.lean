import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Chain
import Mathlib.Basic.Real.Basic

/-!
# Carrier graphs, catalyst covers and fractional catalyst loads

Shared definitions for manuscripts 003b and 003e. A carrier graph is a finite directed graph
(`arc u v` means `u → v`) together with a finite set of fusion pairs `(u, w)` (the parent pairs of
the fusion gates). A directed path is a nonempty list of vertices along arcs (single vertices
included); the vertex set of a path `P` is `P.toFinset`.
-/

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
