import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.WithTop
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Interval
import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Lattice
import Mathlib.Tactic.FinCases
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

open Finset

/-- An open network: arcs `A` between vertices `T ⊕ I` (terminals `T`, internal vertices `I`),
with integral lower and upper bounds and costs on the arcs, and a fixed integral excess on every
internal vertex. Costs may be negative and lower bounds nonzero. -/
structure Network (T I A : Type*) where
  tail : A → T ⊕ I
  head : A → T ⊕ I
  lower : A → ℤ
  upper : A → ℤ
  cost : A → ℤ
  supply : I → ℤ

namespace Network

variable {T I A : Type*} [Fintype A] [DecidableEq T] [DecidableEq I]

/-- `f` is a feasible integral flow with boundary `b`: bounds hold, net outflow is `b` at the
terminals and the fixed excess at internal vertices. -/
def Feasible (N : Network T I A) (b : T → ℤ) (f : A → ℤ) : Prop :=
  (∀ a, N.lower a ≤ f a ∧ f a ≤ N.upper a) ∧
    ∀ v, netOut N.tail N.head f v = Sum.elim b N.supply v

/-- Cost `c^T f` of a flow. -/
def flowCost (N : Network T I A) (f : A → ℤ) : ℤ := ∑ a, N.cost a * f a

/-- The (finite) set of feasible integral flows with boundary `b`. -/
noncomputable def feasibleSet [DecidableEq A] (N : Network T I A) (b : T → ℤ) :
    Finset (A → ℤ) := by
  classical
  exact (Fintype.piFinset fun a => Finset.Icc (N.lower a) (N.upper a)).filter (N.Feasible b)

/-- The boundary function `Φ_G(b)`: least cost of a feasible flow with boundary `b`,
or `⊤` if there is none. -/
noncomputable def boundary [DecidableEq A] (N : Network T I A) (b : T → ℤ) : WithTop ℤ :=
  ((N.feasibleSet b).image N.flowCost).min

variable [DecidableEq A] (N : Network T I A)

/-- **Flow exchange** (the flow-level content of Theorem 3.1). For feasible flows `f`, `g` with
boundaries `b`, `b'` and a terminal `i` with `b' i < b i`, there is a terminal `j` with
`b j < b' j` and feasible flows with the exchanged boundaries `b - e_i + e_j` and
`b' + e_i - e_j` whose total cost equals that of `f` and `g`. -/
theorem flow_exchange {b b' : T → ℤ} {f g : A → ℤ} (hf : N.Feasible b f) (hg : N.Feasible b' g)
    {i : T} (hi : b' i < b i) :
    ∃ j, b j < b' j ∧ ∃ f' g', N.Feasible (b - Pi.single i 1 + Pi.single j 1) f' ∧
      N.Feasible (b' + Pi.single i 1 - Pi.single j 1) g' ∧
      N.flowCost f' + N.flowCost g' = N.flowCost f + N.flowCost g := by
  sorry

/-- **Boundary exchange** (Theorem 3.1). For `b, b' ∈ dom Φ_G` and `i` with `b' i < b i` there is
`j` with `b j < b' j` and `Φ(b) + Φ(b') ≥ Φ(b - e_i + e_j) + Φ(b' + e_i - e_j)`. -/
theorem boundary_exchange {b b' : T → ℤ} (hb : N.boundary b ≠ ⊤) (hb' : N.boundary b' ≠ ⊤)
    {i : T} (hi : b' i < b i) :
    ∃ j, b j < b' j ∧
      N.boundary (b - Pi.single i 1 + Pi.single j 1) +
        N.boundary (b' + Pi.single i 1 - Pi.single j 1) ≤ N.boundary b + N.boundary b' := by
  sorry

end Network

/-- M-convexity (Murota): nonempty domain and the exchange axiom (2.2). -/
def IsMConvex {T : Type*} [DecidableEq T] (Φ : (T → ℤ) → WithTop ℤ) : Prop :=
  (∃ b, Φ b ≠ ⊤) ∧
    ∀ b b' : T → ℤ, Φ b ≠ ⊤ → Φ b' ≠ ⊤ → ∀ i, b' i < b i →
      ∃ j, b j < b' j ∧
        Φ (b - Pi.single i 1 + Pi.single j 1) + Φ (b' + Pi.single i 1 - Pi.single j 1) ≤
          Φ b + Φ b'

/-- **Theorem 3.1.** The boundary function of every network with nonempty domain is M-convex. -/
theorem Network.boundary_isMConvex {T I A : Type*} [Fintype A] [DecidableEq T] [DecidableEq I]
    [DecidableEq A] (N : Network T I A) (hdom : ∃ b, N.boundary b ≠ ⊤) :
    IsMConvex N.boundary := by
  sorry

/-- Intended boundary state `β_S = ∑_{k ∈ S} (e_{X_k^in} - e_{X_k^out})` of a gadget whose
terminals are `Sum.inl k = X_k^in` and `Sum.inr k = X_k^out`. -/
def intended {K : Type*} [DecidableEq K] (S : Finset K) : K ⊕ K → ℤ :=
  Sum.elim (fun k => if k ∈ S then 1 else 0) (fun k => if k ∈ S then -1 else 0)

/-- Definition 4.2: `N` is a pass-through gadget with cost table `τ` if, for a constant `c`,
(i) `Φ(β_S) = c + τ(S)` for every `S`, and (ii) `Φ(b) > c` for every boundary `b` that is not an
intended state. (The normalization `τ ≥ 0`, `min τ = 0` of the paper is not needed below.) -/
def IsPassThrough {K I A : Type*} [Fintype A] [DecidableEq K] [DecidableEq I] [DecidableEq A]
    (N : Network (K ⊕ K) I A) (τ : Finset K → ℤ) : Prop :=
  ∃ c : ℤ, (∀ S, N.boundary (intended S) = ((c + τ S : ℤ) : WithTop ℤ)) ∧
    ∀ b : K ⊕ K → ℤ, (∀ S, b ≠ intended S) → ((c : ℤ) : WithTop ℤ) < N.boundary b

/-- The read-only comparator table `τ(x, y) = |x - y|` on two channels. -/
def comparatorTable (S : Finset (Fin 2)) : ℤ :=
  |(if (0 : Fin 2) ∈ S then 1 else 0) - (if (1 : Fin 2) ∈ S then 1 else 0)|

/-- **Corollary 4.4 (no all-equal sensor).** Let `K` have at least two channels. No network is a
pass-through gadget whose table vanishes at `∅` and at the full set and is positive on every proper
nonempty set of channels. -/
theorem Network.no_allEqualSensor {K I A : Type*} [Fintype K] [DecidableEq K] [Nontrivial K]
    [Fintype A] [DecidableEq I] [DecidableEq A] (N : Network (K ⊕ K) I A) (τ : Finset K → ℤ)
    (h0 : τ ∅ = 0) (huniv : τ univ = 0)
    (hpos : ∀ S : Finset K, S.Nonempty → S ≠ univ → 0 < τ S) :
    ¬ IsPassThrough N τ := by
  sorry

/-- **Theorem 4.3 (no read-only comparator).** No network, of any size and with arbitrary integral
bounds, internal supplies and costs, is a pass-through gadget on two channels with cost table
`|x - y|`. -/
theorem Network.no_readOnlyComparator {I A : Type*} [Fintype A] [DecidableEq I] [DecidableEq A]
    (N : Network (Fin 2 ⊕ Fin 2) I A) : ¬ IsPassThrough N comparatorTable := by
  sorry

/-- The four-arc crossbar: arcs `X_in → X_out`, `Y_in → Y_out` of cost `1` and the crossing arcs
`X_in → Y_out`, `Y_in → X_out` of cost `0`, all with bounds `[0, 1]`, no internal vertices. -/
def crossbar : Network (Fin 2 ⊕ Fin 2) Empty (Fin 4) where
  tail := ![Sum.inl (Sum.inl 0), Sum.inl (Sum.inl 1), Sum.inl (Sum.inl 0), Sum.inl (Sum.inl 1)]
  head := ![Sum.inl (Sum.inr 0), Sum.inl (Sum.inr 1), Sum.inl (Sum.inr 1), Sum.inl (Sum.inr 0)]
  lower := fun _ => 0
  upper := fun _ => 1
  cost := ![1, 1, 0, 0]
  supply := fun e => e.elim

/-- **Remark 4.6 (the crossbar).** The crossbar realizes the intended table `Φ(β_S) = |x - y|`,
but the two crossed states `e_{X_in} - e_{Y_out}` and `e_{Y_in} - e_{X_out}` also cost `0`, so
condition (ii) of Definition 4.2 fails and cannot be dropped from Theorem 4.3. -/
theorem crossbar_table :
    (∀ S, crossbar.boundary (intended S) = (comparatorTable S : WithTop ℤ)) ∧
    crossbar.boundary (Pi.single (Sum.inl 0) 1 - Pi.single (Sum.inr 1) 1) = (0 : ℤ) ∧
    crossbar.boundary (Pi.single (Sum.inl 1) 1 - Pi.single (Sum.inr 0) 1) = (0 : ℤ) := by
  sorry

/-- **Proposition 4.1.** `min {p + n : x + n = y + p, p, n ≥ 0} = |x - y|`. -/
theorem oneShot_isLeast (x y : ℝ) :
    IsLeast {t | ∃ p n : ℝ, 0 ≤ p ∧ 0 ≤ n ∧ x + n = y + p ∧ t = p + n} |x - y| := by
  sorry

/-- Submodularity on a lattice: `F(a) + F(a') ≥ F(a ⊓ a') + F(a ⊔ a')`. -/
def Submodular {L : Type*} [Lattice L] (F : L → ℝ) : Prop :=
  ∀ z z', F (z ⊓ z') + F (z ⊔ z') ≤ F z + F z'

/-- Projected minimizer relation `R_F = {x : F(x, a) = min F for some a}` (minimum = global
minimum of `F`). -/
def projMinRel {X Y : Type*} (F : X × Y → ℝ) : Set X :=
  {x | ∃ a, ∀ z, F (x, a) ≤ F z}

/-- The NAND relation `{(x₁, x₂, z) : z = 1 - x₁ x₂}` on Boolean labels. -/
def nandRel : Set (Fin 3 → Bool) := {x | x 2 = !(x 0 && x 1)}

/-- **Theorem 5.2 (no submodular NAND gadget).** No submodular function `F(x, a)` of three visible
Boolean labels and any family of auxiliary Boolean labels has the NAND relation as its projected
minimizer relation. -/
theorem no_submodular_nand {α : Type*} (F : (Fin 3 → Bool) × (α → Bool) → ℝ)
    (hF : Submodular F) : projMinRel F ≠ nandRel := by
  sorry

/-- **Remark after Theorem 5.2.** None of the eight complemented versions of the NAND relation is
closed under both `⊓` and `⊔`; hence no submodular function has any of them as its projected
minimizer relation. -/
theorem no_submodular_nand_any_polarity {α : Type*} (F : (Fin 3 → Bool) × (α → Bool) → ℝ)
    (hF : Submodular F) (m : Fin 3 → Bool) :
    projMinRel F ≠ {x | (fun i => xor (x i) (m i)) ∈ nandRel} := by
  sorry

end GC.FlowCircuits
