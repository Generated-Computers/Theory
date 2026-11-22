import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Fin
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Comparator challenge for result family 003 (generated from the solution files: the
definitions are verbatim, the main theorems are stated with `sorry`). -/

namespace GC.FlowCircuits

open Finset

variable {V A : Type*} [Fintype A] [DecidableEq V]

/-- Incidence coefficient of arc `a` at vertex `v`: `+1` at the tail, `-1` at the head
(`0` for a loop). -/
def inc (tail head : A → V) (a : A) (v : V) : ℤ :=
  (if tail a = v then 1 else 0) - (if head a = v then 1 else 0)

/-- Net outflow `(∂h)(v) = ∑_{a ∈ δ⁺(v)} h_a - ∑_{a ∈ δ⁻(v)} h_a`. -/
def netOut (tail head : A → V) (h : A → ℤ) (v : V) : ℤ :=
  ∑ a, h a * inc tail head a v

/-- `χ` is conformal to `h`: on every arc, `χ_a` lies between `0` and `h_a`. -/
def Conformal (χ h : A → ℤ) : Prop :=
  ∀ a, (0 ≤ χ a ∧ χ a ≤ h a) ∨ (h a ≤ χ a ∧ χ a ≤ 0)

section lemmas

variable (tail head : A → V)

/-- The total mass `∑ |h_a|`, used as the induction measure. -/
def mass (h : A → ℤ) : ℕ := ∑ a, (h a).natAbs

end lemmas

end GC.FlowCircuits

namespace GC.FlowCircuits

/-- A Boolean value as the real number `0` or `1`. -/
def b2r (b : Bool) : ℝ := if b then 1 else 0

/-- A vertex of a monotone circuit: an input with a fixed value, or a gate
(`isAnd = true` for AND, `false` for OR) with two children. -/
inductive Node (n : ℕ) where
  | input (b : Bool)
  | gate (isAnd : Bool) (c₁ c₂ : Fin n)

/-- A monotone fan-in-two circuit on `Fin n`, children have smaller index. -/
structure MonCircuit (n : ℕ) where
  node : Fin n → Node n
  topo : ∀ v a c₁ c₂, node v = .gate a c₁ c₂ → c₁ < v ∧ c₂ < v

namespace MonCircuit

variable {n : ℕ}

/-- The Boolean value of a vertex. -/
def val (C : MonCircuit n) (v : Fin n) : Bool :=
  match h : C.node v with
  | .input b => b
  | .gate a c₁ c₂ =>
    have := C.topo v a c₁ c₂ h
    if a then val C c₁ && val C c₂ else val C c₁ || val C c₂
termination_by v
decreasing_by all_goals first | exact this.1 | exact this.2

variable (C : MonCircuit n)

end MonCircuit

end GC.FlowCircuits

namespace GC.FlowCircuits

open Finset

namespace MonCircuit

variable {n : ℕ} (C : MonCircuit n)

/-- Alternation: a gate child of an AND gate is an OR gate and a gate child of an OR gate is an
AND gate. -/
def Alternating : Prop :=
  ∀ v a c₁ c₂, C.node v = .gate a c₁ c₂ → ∀ a' d₁ d₂,
    (C.node c₁ = .gate a' d₁ d₂ → a' = !a) ∧ (C.node c₂ = .gate a' d₁ d₂ → a' = !a)

/-- Is `v` a gate? -/
def isGate (v : Fin n) : Bool :=
  match C.node v with
  | .gate _ _ _ => true
  | .input _ => false

/-- The type of a gate (`true` = AND). -/
def gtype (v : Fin n) : Bool :=
  match C.node v with
  | .gate a _ _ => a
  | .input _ => false

/-- The `k`-th child of a gate (`k = 0, 1`). -/
def kid (v : Fin n) (k : Fin 2) : Fin n :=
  match C.node v with
  | .gate _ c₁ c₂ => ![c₁, c₂] k
  | .input _ => v

/-- The transformed bit `b_v`: `t_v` for an OR gate and `1 - t_v` for an AND gate. -/
def tbit (v : Fin n) : Bool :=
  match C.node v with
  | .gate a _ _ => if a then !C.val v else C.val v
  | .input _ => C.val v

/-- `b_{u → v}` for a predecessor `u` of a gate of type `a`: the transformed bit `b_u` if `u` is
a gate, and the encoded constant (`t_u` below an AND gate, `1 - t_u` below an OR gate) if `u` is
an input. -/
def edgeBit (a : Bool) (u : Fin n) : Bool :=
  match C.node u with
  | .input t => if a then t else !t
  | .gate _ _ _ => C.tbit u

variable {C}

/-- **Theorem 2.1 (NAND normalization).** In an alternating monotone circuit every gate `v` with
predecessors `u, w` satisfies `b_v = NAND(b_{u→v}, b_{w→v})`. -/
theorem nand_normalization (hC : C.Alternating) {v c₁ c₂ : Fin n} {a : Bool}
    (h : C.node v = .gate a c₁ c₂) :
    C.tbit v = !(C.edgeBit a c₁ && C.edgeBit a c₂) := by
  sorry

end MonCircuit

/-- The four NAND triples `(x, y, NAND(x, y))`. -/
def nandPoints : Set (ℝ × ℝ × ℝ) := {(0, 0, 1), (0, 1, 1), (1, 0, 1), (1, 1, 0)}

/-- The polytope `P = {(x,y,z) ∈ [0,1]^3 : z + x ≥ 1, z + y ≥ 1, z + x + y ≤ 2}`. -/
def nandPolytope : Set (ℝ × ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2.1 ∧ p.2.1 ≤ 1 ∧ 0 ≤ p.2.2 ∧ p.2.2 ≤ 1 ∧
    1 ≤ p.2.2 + p.1 ∧ 1 ≤ p.2.2 + p.2.1 ∧ p.2.2 + p.1 + p.2.1 ≤ 2}

/-- **Theorem 3.1 (NAND polytope).** The convex hull of the four NAND triples is cut out of the
unit cube by `z + x ≥ 1`, `z + y ≥ 1` and `z + x + y ≤ 2`. -/
theorem nand_polytope : convexHull ℝ nandPoints = nandPolytope := by
  sorry

/-- **Lemma 3.2 (forcing).** If `x, y ∈ {0,1}` and `z ∈ [0,1]` satisfy the three NAND
inequalities, then `z = NAND(x, y)`. -/
theorem forcing (x y : Bool) (z : ℝ) (h0 : 0 ≤ z) (h1 : z ≤ 1) (hx : 1 ≤ z + b2r x)
    (hy : 1 ≤ z + b2r y) (hs : z + b2r x + b2r y ≤ 2) : z = b2r (!(x && y)) := by
  sorry

/-- A point of the residual NAND program (Definition 4.1). For a gate `v`: `zocc v = z_v` is its
own occurrence, `cocc v k` (`k = 0, 1`) are the occurrences `x_v, y_v` of its two predecessors;
`slack v = s` and `surplus v k = r_x, r_y` are the slacks of the rows (3.1); `pos v k`, `neg v k`
are the variables `p, n` of the spanning-tree edge joining the occurrence `cocc v k` of the `k`-th
child, when it is a gate `u`, to the occurrence `zocc u` (we use the star spanning tree of
`Occ(u)` centred at `z_u`). -/
structure ResPoint (n : ℕ) where
  zocc : Fin n → ℝ
  cocc : Fin n → Fin 2 → ℝ
  slack : Fin n → ℝ
  surplus : Fin n → Fin 2 → ℝ
  pos : Fin n → Fin 2 → ℝ
  neg : Fin n → Fin 2 → ℝ

namespace MonCircuit

variable {n : ℕ} (C : MonCircuit n)

/-- Feasibility for the residual NAND program (Definition 4.1): bounds, the three rows
`z + x + y + s = 2`, `z + x - r_x = 1`, `z + y - r_y = 1` of every gate, input occurrences fixed
to their encoded constants, and the tree-edge equations `o_a - o_{a'} - p + n = 0`. -/
def ResFeasible (P : ResPoint n) : Prop :=
  ∀ v, C.isGate v = true →
    (0 ≤ P.zocc v ∧ P.zocc v ≤ 1) ∧ (∀ k, 0 ≤ P.cocc v k ∧ P.cocc v k ≤ 1) ∧
    (0 ≤ P.slack v ∧ P.slack v ≤ 2) ∧ (∀ k, 0 ≤ P.surplus v k ∧ P.surplus v k ≤ 1) ∧
    P.zocc v + P.cocc v 0 + P.cocc v 1 + P.slack v = 2 ∧
    (∀ k, P.zocc v + P.cocc v k - P.surplus v k = 1) ∧
    ∀ k,
      (C.isGate (C.kid v k) = false →
        P.cocc v k = b2r (C.edgeBit (C.gtype v) (C.kid v k))) ∧
      (C.isGate (C.kid v k) = true →
        0 ≤ P.pos v k ∧ P.pos v k ≤ 1 ∧ 0 ≤ P.neg v k ∧ P.neg v k ≤ 1 ∧
        P.cocc v k - P.zocc (C.kid v k) - P.pos v k + P.neg v k = 0)

/-- The objective `∑ (p + n)` over all tree edges. -/
def resCost (P : ResPoint n) : ℝ :=
  ∑ v, ∑ k : Fin 2,
    if C.isGate v = true ∧ C.isGate (C.kid v k) = true then P.pos v k + P.neg v k else 0

/-- The transcript point: every occurrence of a gate `u` is `b_u`, every input occurrence is its
encoded constant, the slacks are determined by the rows, and `p = n = 0`. -/
def transcript : ResPoint n where
  zocc v := b2r (C.tbit v)
  cocc v k := b2r (C.edgeBit (C.gtype v) (C.kid v k))
  slack v := 2 - (b2r (C.tbit v) + b2r (C.edgeBit (C.gtype v) (C.kid v 0)) +
    b2r (C.edgeBit (C.gtype v) (C.kid v 1)))
  surplus v k := b2r (C.tbit v) + b2r (C.edgeBit (C.gtype v) (C.kid v k)) - 1
  pos _ _ := 0
  neg _ _ := 0

variable {C}

/-- **Theorem 4.2 (iv)–(v) (dyadic elimination).** For an alternating monotone circuit, the
residual NAND program has optimum value `0`, attained by the transcript point, and every optimal
(cost-`0`) feasible point coincides with the transcript point on all variables of the program; in
particular every occurrence of a gate `u` carries the transformed bit `b_u`. -/
theorem dyadic_elimination (hC : C.Alternating) :
    C.ResFeasible C.transcript ∧ C.resCost C.transcript = 0 ∧
    (∀ P, C.ResFeasible P → 0 ≤ C.resCost P) ∧
    ∀ P, C.ResFeasible P → C.resCost P = 0 → ∀ v, C.isGate v = true →
      P.zocc v = C.transcript.zocc v ∧ P.cocc v = C.transcript.cocc v ∧
      P.slack v = C.transcript.slack v ∧ P.surplus v = C.transcript.surplus v ∧
      ∀ k, C.isGate (C.kid v k) = true → P.pos v k = 0 ∧ P.neg v k = 0 := by
  sorry

/-- **Theorem 5.1, the equal-flow form (logical content).** Replace the disagreement objective by
hard equality of all occurrences of each gate (`p = n = 0` on every tree edge). Then the feasible
point is unique: it is the transcript point; it is integral (every occurrence is `0` or `1`), and
the common value of the occurrences of a gate `u` (its own `z_u` and every `x_v`, `y_v` that uses
`u`) is the transformed bit `b_u`. -/
theorem equalFlow_unique (hC : C.Alternating) (P : ResPoint n) (hP : C.ResFeasible P)
    (heq : ∀ v, C.isGate v = true → ∀ k, C.isGate (C.kid v k) = true →
      P.pos v k = 0 ∧ P.neg v k = 0) :
    (∀ v, C.isGate v = true →
      P.zocc v = C.transcript.zocc v ∧ P.cocc v = C.transcript.cocc v ∧
      P.slack v = C.transcript.slack v ∧ P.surplus v = C.transcript.surplus v) ∧
    (∀ v, C.isGate v = true → (P.zocc v = 0 ∨ P.zocc v = 1) ∧ ∀ k, P.cocc v k = 0 ∨ P.cocc v k = 1) ∧
    (∀ u, C.isGate u = true → P.zocc u = b2r (C.tbit u) ∧
      ∀ v k, C.isGate v = true → C.kid v k = u → P.cocc v k = b2r (C.tbit u)) := by
  sorry

end MonCircuit

/-- Weak max-flow/min-cut: the value of a flow from `s` to `t` (its net outflow at `s`) is at most
the capacity of every cut `S` with `s ∈ S`, `t ∉ S`. -/
theorem cut_bound {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V]
    (tail head : A → V) (cap f : A → ℤ) {s t : V} {S : Finset V} (hs : s ∈ S) (ht : t ∉ S)
    (hf : ∀ a, 0 ≤ f a ∧ f a ≤ cap a)
    (hcons : ∀ v, v ≠ s → v ≠ t → netOut tail head f v = 0) :
    netOut tail head f s ≤ ∑ a ∈ univ.filter (fun a => tail a ∈ S ∧ head a ∉ S), cap a := by
  sorry

/-- **Proposition 6.1 (cut-size bound).** If a two-terminal network with arc capacities at most
`U` carries a flow of value at least `2^i`, every separating cut has at least `2^i / U` arcs, i.e.
`(#cut) * U ≥ 2^i`. -/
theorem cut_size_bound {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V]
    (tail head : A → V) (cap f : A → ℤ) {s t : V} {S : Finset V} (hs : s ∈ S) (ht : t ∉ S)
    (hf : ∀ a, 0 ≤ f a ∧ f a ≤ cap a)
    (hcons : ∀ v, v ≠ s → v ≠ t → netOut tail head f v = 0) (U : ℤ) (hU : ∀ a, cap a ≤ U)
    (i : ℕ) (hval : 2 ^ i ≤ netOut tail head f s) :
    2 ^ i ≤ ((univ.filter (fun a => tail a ∈ S ∧ head a ∉ S)).card : ℤ) * U := by
  sorry

end GC.FlowCircuits
