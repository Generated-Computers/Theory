import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Group.Commutator
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.GroupTheory.Perm.ClosureSwap
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.Induction
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.GroupTheory.FreeGroup.Basic

namespace GC.A5Programs

open Equiv

section Descriptors

variable {G : Type*} [Group G]

/-- A Latin factor `z = x y` can be solved for each of its variables, which gives the six
oriented forms `y = x⁻¹ z`, `x = z y⁻¹`, `z = x y` (with the known third value as a coefficient)
of 004e, Lemma 5.1. -/
theorem latin_relations (x y z : G) :
    (z = x * y ↔ y = x⁻¹ * z) ∧ (z = x * y ↔ x = z * y⁻¹) := by
  sorry

/-- The descriptor `x ↦ a x^ε b`, with sign `ε = true` for `+1` and `false` for `-1`. -/
def descr (a b : G) : Bool → G → G
  | true, x => a * x * b
  | false, x => a * x⁻¹ * b

theorem descriptor_comp_pos (a b c d : G) (ε : Bool) (x : G) :
    descr c d true (descr a b ε x) = descr (c * a) (b * d) ε x := by
  sorry

theorem descriptor_comp_neg (a b c d : G) (ε : Bool) (x : G) :
    descr c d false (descr a b ε x) = descr (c * b⁻¹) (a⁻¹ * d) (!ε) x := by
  sorry

theorem descriptor_inv_pos (a b x : G) :
    descr a⁻¹ b⁻¹ true (descr a b true x) = x := by
  sorry

theorem descriptor_inv_neg (a b x : G) :
    descr b a false (descr a b false x) = x := by
  sorry

/-- Composition of descriptors is a descriptor (with explicit new coefficients). -/
theorem comp_descriptors (Φ : ℕ → G × G × Bool) (m : ℕ) :
    ∃ A B : G, ∃ ε : Bool, ∀ x,
      (List.range m).foldl (fun y i => descr (Φ i).1 (Φ i).2.1 (Φ i).2.2 y) x = descr A B ε x := by
  sorry

end Descriptors

section Monodromy

variable {X : Type*}

/-- The prefix compositions `Ψ_i = Φ_{i-1} ∘ ⋯ ∘ Φ_0`. -/
def prefixMap (Φ : ℕ → X → X) : ℕ → X → X
  | 0, x => x
  | i + 1, x => Φ i (prefixMap Φ i x)

/-- **Cycle monodromy** (004e, Theorem 5.2; 004f, Theorem 3.3). For relations
`q_{i+1} = Φ_i(q_i)` (`0 ≤ i < m - 1`) closed by `q_0 = Φ_{m-1}(q_{m-1})`, an assignment
`q_0, …, q_{m-1}` satisfies all `m` relations iff `q_i = Ψ_i(q_0)` for all `i < m` and `q_0` is a
root of the return map `Ψ_m`. Hence `r ↦ (Ψ_i r)_i` is a bijection from the roots of
`r = Ψ_m(r)` onto the solutions. -/
theorem cycle_monodromy (Φ : ℕ → X → X) (m : ℕ) (hm : 0 < m) (q : ℕ → X) :
    ((∀ i, i + 1 < m → q (i + 1) = Φ i (q i)) ∧ q 0 = Φ (m - 1) (q (m - 1))) ↔
    ((∀ i, i < m → q i = prefixMap Φ i (q 0)) ∧ q 0 = prefixMap Φ m (q 0)) := by
  sorry

end Monodromy

section General

variable {G : Type*} [Group G]

/-- **Hard-coefficient cycle** (004f, Theorem 2.1). The two Latin factors `F₁ : q = g r` and
`F₂ : q = r e` form a cycle whose return map is `r ↦ g r`; the system is satisfiable iff
`g = e`, and then every `r` extends uniquely, by `q = r`. -/
theorem hard_coefficient (g : G) :
    ((∃ r q : G, q = g * r ∧ q = r * 1) ↔ g = 1) ∧
    (g = 1 → ∀ r : G, ∃! q : G, q = g * r ∧ q = r * 1) := by
  sorry

/-- Exactly one shift `h` makes the system with coefficient `g h⁻¹` satisfiable, namely
`h = g` (004f, proof of Corollary 2.2). -/
theorem hard_coefficient_unique (g : G) :
    ∃! h : G, ∃ r q : G, q = (g * h⁻¹) * r ∧ q = r * 1 := by
  sorry

/-- **Mixer cycle** (004f, Lemma 3.1): the factors `u = x y`, `v = u y` are equivalent to the
opened system `y² = x⁻¹ v`, `u = x y`. -/
theorem mixer_cycle (x y u v : G) : (u = x * y ∧ v = u * y) ↔ (y * y = x⁻¹ * v ∧ u = x * y) := by
  sorry

/-- The mixer `M(x, y) = (x y, x y²)`. -/
def mixer (p : G × G) : G × G := (p.1 * p.2, p.1 * p.2 * p.2)

/-- The mixer is a bijection, with inverse `y = u⁻¹ v`, `x = u v⁻¹ u` (004f, Section 4). -/
theorem mixer_inverse :
    Function.LeftInverse (fun p : G × G => (p.1 * p.2⁻¹ * p.1, p.1⁻¹ * p.2)) (mixer (G := G)) ∧
    Function.RightInverse (fun p : G × G => (p.1 * p.2⁻¹ * p.1, p.1⁻¹ * p.2))
      (mixer (G := G)) := by
  sorry

/-- Apply the mixer to registers `i ≠ j`: `(g_i, g_j) ← M(g_i, g_j)`. -/
def mixAt {W : ℕ} (i j : Fin W) (g : Fin W → G) : Fin W → G :=
  Function.update (Function.update g i (g i * g j)) j (g i * g j * g j)

/-- A mixer strip: a sequence of mixers on ordered pairs of distinct registers (a layer of
`W/2` disjoint pairs is a run of `W/2` consecutive entries). -/
def mixerStrip {W : ℕ} (pairs : List (Fin W × Fin W)) (g : Fin W → G) : Fin W → G :=
  pairs.foldl (fun h p => mixAt p.1 p.2 h) g

/-- **Mixer-strip barrier, bijectivity** (004f, Theorem 3.2(iii), first part). -/
theorem mixerStrip_bijective {W : ℕ} (pairs : List (Fin W × Fin W))
    (hp : ∀ p ∈ pairs, p.1 ≠ p.2) : Function.Bijective (mixerStrip (G := G) pairs) := by
  sorry

/-- **No small summary** (004f, Theorem 3.2(iii)): for a finite group with at least two
elements, no function of fewer than `W` group values determines all output registers of a
mixer strip of width `W`. -/
theorem mixerStrip_no_small_summary [Fintype G] (hG : 2 ≤ Fintype.card G) {W : ℕ}
    (pairs : List (Fin W × Fin W)) (hp : ∀ p ∈ pairs, p.1 ≠ p.2) {k : ℕ} (hk : k < W)
    (f : (Fin W → G) → (Fin k → G)) (h : (Fin k → G) → (Fin W → G)) :
    ¬ ∀ x, h (f x) = mixerStrip pairs x := by
  sorry

end General

section

/-- One node of a straight-line program over a group with leaves labelled by `α`. -/
inductive Op (α : Type) where
  | leaf : α → Op α
  | mul : ℕ → ℕ → Op α
  | inv : ℕ → Op α
  deriving DecidableEq, Repr

variable {α β : Type} {G H : Type*} [Group G] [Group H]

/-- The value of one operation, given the values of the earlier nodes. -/
def Op.step (ν : α → G) (vals : List G) : Op α → G
  | .leaf a => ν a
  | .mul i j => vals.getD i 1 * vals.getD j 1
  | .inv i => (vals.getD i 1)⁻¹

/-- The values of all nodes of a program. -/
def evalProg (ν : α → G) (ops : List (Op α)) : List G :=
  ops.foldl (fun vals op => vals ++ [op.step ν vals]) []

/-- The value of node `k`. -/
def val (ν : α → G) (ops : List (Op α)) (k : ℕ) : G := (evalProg ν ops).getD k 1

/-- A program is well formed if every operand is an earlier node. -/
def Op.WF (k : ℕ) : Op α → Prop
  | .leaf _ => True
  | .mul i j => i < k ∧ j < k
  | .inv i => i < k

/-- Every operand of node `k` refers to an earlier node. -/
def WellFormed (ops : List (Op α)) : Prop :=
  ∀ k (h : k < ops.length), (ops[k]'h).WF k

end

/-- A permutation of `Fin 5` from the vector of its values and the vector of its inverse. -/
def mk5 (f g : Fin 5 → Fin 5) (h1 : ∀ i, g (f i) = i := by decide)
    (h2 : ∀ i, f (g i) = i := by decide) : Perm (Fin 5) := ⟨f, g, h1, h2⟩

/-- `p = (1 2 3 4 5)` (paper notation), i.e. `0 ↦ 1 ↦ 2 ↦ 3 ↦ 4 ↦ 0`. -/
def pA : Perm (Fin 5) := mk5 ![1,2,3,4,0] ![4,0,1,2,3]
/-- `q = (1 2 3)`. -/
def qA : Perm (Fin 5) := mk5 ![1,2,0,3,4] ![2,0,1,3,4]

/-- The 60 elements of `A₅`, in breadth-first order from `p, q, p⁻¹, q⁻¹, e`. -/
def A5list : List (Perm (Fin 5)) :=
  [mk5 ![1,2,3,4,0] ![4,0,1,2,3],
   mk5 ![1,2,0,3,4] ![2,0,1,3,4],
   mk5 ![4,0,1,2,3] ![1,2,3,4,0],
   mk5 ![2,0,1,3,4] ![1,2,0,3,4],
   mk5 ![0,1,2,3,4] ![0,1,2,3,4],
   mk5 ![2,3,4,0,1] ![3,4,0,1,2],
   mk5 ![2,3,1,4,0] ![4,2,0,1,3],
   mk5 ![3,1,2,4,0] ![4,1,2,0,3],
   mk5 ![2,0,3,4,1] ![1,4,0,2,3],
   mk5 ![4,1,2,0,3] ![3,1,2,4,0],
   mk5 ![0,1,4,2,3] ![0,1,3,4,2],
   mk5 ![3,4,0,1,2] ![2,3,4,0,1],
   mk5 ![1,4,0,2,3] ![2,0,3,4,1],
   mk5 ![0,1,3,4,2] ![0,1,4,2,3],
   mk5 ![4,2,0,1,3] ![2,3,1,4,0],
   mk5 ![3,4,2,0,1] ![3,4,2,0,1],
   mk5 ![4,2,3,0,1] ![3,4,1,2,0],
   mk5 ![3,1,4,0,2] ![3,1,4,0,2],
   mk5 ![0,2,3,1,4] ![0,3,1,2,4],
   mk5 ![1,2,4,0,3] ![3,0,1,4,2],
   mk5 ![0,3,1,2,4] ![0,2,3,1,4],
   mk5 ![0,3,4,1,2] ![0,3,4,1,2],
   mk5 ![0,3,2,4,1] ![0,4,2,1,3],
   mk5 ![3,2,0,4,1] ![2,4,1,0,3],
   mk5 ![3,4,1,2,0] ![4,2,3,0,1],
   mk5 ![2,4,1,0,3] ![3,2,0,4,1],
   mk5 ![1,4,2,3,0] ![4,0,2,3,1],
   mk5 ![3,0,1,4,2] ![1,2,4,0,3],
   mk5 ![4,0,3,1,2] ![1,3,4,2,0],
   mk5 ![4,0,2,3,1] ![1,4,2,3,0],
   mk5 ![1,3,4,2,0] ![4,0,3,1,2],
   mk5 ![1,3,0,4,2] ![2,0,4,1,3],
   mk5 ![2,0,4,1,3] ![1,3,0,4,2],
   mk5 ![0,4,2,1,3] ![0,3,2,4,1],
   mk5 ![2,3,0,1,4] ![2,3,0,1,4],
   mk5 ![1,4,3,0,2] ![3,0,4,2,1],
   mk5 ![4,3,1,0,2] ![3,2,4,1,0],
   mk5 ![3,0,2,1,4] ![1,3,2,0,4],
   mk5 ![2,4,0,3,1] ![2,4,0,3,1],
   mk5 ![3,1,0,2,4] ![2,1,3,0,4],
   mk5 ![1,0,3,2,4] ![1,0,3,2,4],
   mk5 ![3,2,4,1,0] ![4,3,1,0,2],
   mk5 ![1,3,2,0,4] ![3,0,2,1,4],
   mk5 ![4,1,3,2,0] ![4,1,3,2,0],
   mk5 ![4,1,0,3,2] ![2,1,4,3,0],
   mk5 ![4,2,1,3,0] ![4,2,1,3,0],
   mk5 ![2,1,4,3,0] ![4,1,0,3,2],
   mk5 ![0,2,4,3,1] ![0,4,1,3,2],
   mk5 ![3,0,4,2,1] ![1,4,3,0,2],
   mk5 ![2,1,3,0,4] ![3,1,0,2,4],
   mk5 ![0,4,1,3,2] ![0,2,4,3,1],
   mk5 ![4,3,0,2,1] ![2,4,3,1,0],
   mk5 ![2,4,3,1,0] ![4,3,0,2,1],
   mk5 ![0,2,1,4,3] ![0,2,1,4,3],
   mk5 ![1,0,2,4,3] ![1,0,2,4,3],
   mk5 ![4,3,2,1,0] ![4,3,2,1,0],
   mk5 ![3,2,1,0,4] ![3,2,1,0,4],
   mk5 ![1,0,4,3,2] ![1,0,4,3,2],
   mk5 ![0,4,3,2,1] ![0,4,3,2,1],
   mk5 ![2,1,0,4,3] ![2,1,0,4,3]]

/-- `a = (1 2 3 4 5)`. -/
def aA : Perm (Fin 5) := mk5 ![1,2,3,4,0] ![4,0,1,2,3]
/-- `b = (1 2 4 5 3)`. -/
def bA : Perm (Fin 5) := mk5 ![1,3,0,4,2] ![2,0,4,1,3]
/-- `c = (3 5 4)`. -/
def cA : Perm (Fin 5) := mk5 ![0,1,4,2,3] ![0,1,3,4,2]
/-- `d = (2 4 3)`. -/
def dA : Perm (Fin 5) := mk5 ![0,3,1,2,4] ![0,2,3,1,4]
/-- `(1 4 2 3 5)`. -/
def abComm : Perm (Fin 5) := mk5 ![3,2,4,1,0] ![4,3,1,0,2]

/-- Encoding of Boolean values: `false ↦ e`, `true ↦ a`. -/
def enc : Bool → Perm (Fin 5)
  | false => 1
  | true => aA

/-- A gate of a Boolean circuit: a constant, or NOT / AND of earlier nodes. -/
inductive BOp where
  | const : Bool → BOp
  | not : ℕ → BOp
  | and : ℕ → ℕ → BOp
  deriving DecidableEq, Repr

def BOp.step (vals : List Bool) : BOp → Bool
  | .const b => b
  | .not i => !(vals.getD i false)
  | .and i j => vals.getD i false && vals.getD j false

/-- Values of all nodes of a Boolean circuit. -/
def evalBool (bs : List BOp) : List Bool :=
  bs.foldl (fun vals b => vals ++ [b.step vals]) []

/-- The value of Boolean node `k`. -/
def bval (bs : List BOp) (k : ℕ) : Bool := (evalBool bs).getD k false

def BOp.WF (k : ℕ) : BOp → Prop
  | .const _ => True
  | .not i => i < k
  | .and i j => i < k ∧ j < k

/-- Every gate reads earlier nodes only. -/
def BWellFormed (bs : List BOp) : Prop := ∀ k (h : k < bs.length), (bs[k]'h).WF k

/-- The NOT block for an operand at node `m`, appended at position `L`:
`L: a`, `L+1: x²`, `L+2: x⁴`, `L+3: a·x⁴`. -/
def notBlock (L m : ℕ) : List (Op (Perm (Fin 5))) :=
  [.leaf aA, .mul m m, .mul (L+1) (L+1), .mul L (L+2)]

/-- The AND block for operands at nodes `i, j`, appended at position `L`: four constants and
13 product gates computing `d⁻¹ x⁴ (c⁻¹ y⁴ c) x (c⁻¹ y c) d`. -/
def andBlock (L i j : ℕ) : List (Op (Perm (Fin 5))) :=
  [.leaf dA⁻¹, .leaf cA⁻¹, .leaf cA, .leaf dA,
   .mul i i, .mul (L+4) (L+4),
   .mul j j, .mul (L+6) (L+6),
   .mul (L+1) (L+7), .mul (L+8) (L+2),
   .mul (L+1) j, .mul (L+10) (L+2),
   .mul L (L+5), .mul (L+12) (L+9), .mul (L+13) i, .mul (L+14) (L+11), .mul (L+15) (L+3)]

/-- One compilation step: the program so far and the node index of every Boolean node. -/
def compileStep (st : List (Op (Perm (Fin 5))) × List ℕ) (b : BOp) :
    List (Op (Perm (Fin 5))) × List ℕ :=
  match b with
  | .const v => (st.1 ++ [.leaf (enc v)], st.2 ++ [st.1.length])
  | .not i => (st.1 ++ notBlock st.1.length (st.2.getD i 0), st.2 ++ [st.1.length + 3])
  | .and i j => (st.1 ++ andBlock st.1.length (st.2.getD i 0) (st.2.getD j 0),
      st.2 ++ [st.1.length + 16])

/-- The `A₅` multiplication circuit of a Boolean circuit, with the node map. -/
def compile (bs : List BOp) : List (Op (Perm (Fin 5))) × List ℕ :=
  bs.foldl compileStep ([], [])

/-- **Hard coefficient from a Boolean circuit** (004f, Corollary 2.2, mathematical core). Take any
Boolean circuit, compile it into `A₅` (Corollary 3.4 of 004g) and let `g` be the copy of
node `k`. The hard-coefficient cycle with coefficient `g` is satisfiable iff node `k` is false. -/
theorem hard_coefficient_boolean (bs : List BOp) (hwf : BWellFormed bs) {k : ℕ}
    (hk : k < bs.length) :
    (∃ r q : Perm (Fin 5), q = val id (compile bs).1 ((compile bs).2.getD k 0) * r ∧ q = r * 1) ↔
      bval bs k = false := by
  sorry

section Nielsen

variable {G : Type} [Group G]

/-- The transvection `g_i ← g_i g_j`. -/
def transvect (p : ℕ × ℕ) (g : ℕ → G) : ℕ → G := Function.update g p.1 (g p.1 * g p.2)

/-- Run a list of transvections. -/
def runStrip (ts : List (ℕ × ℕ)) (g : ℕ → G) : ℕ → G :=
  ts.foldl (fun h p => transvect p h) g

/-- Initial registers: the value of every input, `e` for every gate. -/
def initRegs (C : List (Op G)) (k : ℕ) : G :=
  match C[k]? with
  | some (.leaf a) => a
  | _ => 1

/-- The transvections for gate `z`: `z ← z x`, then `z ← z y`. -/
def gateTrans (z : ℕ) : Op G → List (ℕ × ℕ)
  | .mul x y => [(z, x), (z, y)]
  | _ => []

/-- The Nielsen strip of a circuit. -/
def nielsenStrip (C : List (Op G)) : List (ℕ × ℕ) :=
  (List.range C.length).flatMap fun z => match C[z]? with
    | some op => gateTrans z op
    | none => []

/-- A multiplication circuit: inputs and product gates only. -/
def NoInv (C : List (Op G)) : Prop := ∀ op ∈ C, ∀ i, op ≠ .inv i

/-- **Linear reversible embedding** (004f, Theorem 7.2). For every well-formed multiplication
circuit `C` over a group, the Nielsen strip has at most `2 s` transvections, each `g_i ← g_i g_j`
with `i ≠ j`, and after running it from the initial registers, register `k` holds the value of
node `k` for every `k < s`. -/
theorem nielsen_embedding (C : List (Op G)) (hwf : WellFormed C) (hC : NoInv C) :
    (nielsenStrip C).length ≤ 2 * C.length ∧
    (∀ p ∈ nielsenStrip C, p.1 ≠ p.2) ∧
    ∀ k < C.length, runStrip (nielsenStrip C) (initRegs C) k = val id C k := by
  sorry

end Nielsen

end GC.A5Programs
