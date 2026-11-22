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

/-- `A₅` as a group: the alternating group on five points. -/
abbrev A5 := alternatingGroup (Fin 5)

/-- Exponents of the nodes of a one-entry program: its values in `Multiplicative ℤ` with the
entry `1`. -/
def oneEntryExp (ops : List (Op Unit)) (k : ℕ) : ℤ :=
  Multiplicative.toAdd (val (fun _ => Multiplicative.ofAdd (1 : ℤ)) ops k)

/-- **One-generator power normal form** (004d, Theorem 3.1). In a program over any group whose
only leaves are the entry `r`, node `k` equals `x ^ a_k` for every value `x` of `r`. -/
theorem oneEntry_power {G : Type*} [Group G] (ops : List (Op Unit)) (k : ℕ) (x : G) :
    val (fun _ => x) ops k = x ^ oneEntryExp ops k := by
  sorry

/-- **Thirty-class contraction** (004d, Corollary 3.2). Over `A₅`, with exponents reduced
modulo 30, every node of a one-entry region is `x ^ e_k` with `e_k ∈ ZMod 30`; nodes with the
same residue are equal for every entry value, and there are at most 30 value functions. -/
theorem thirty_classes (ops : List (Op Unit)) :
    (∀ k (x : A5), val (fun _ => x) ops k = x ^ ((oneEntryExp ops k : ZMod 30).val)) ∧
    (∀ k l, (oneEntryExp ops k : ZMod 30) = oneEntryExp ops l →
      ∀ x : A5, val (fun _ => x) ops k = val (fun _ => x) ops l) ∧
    ((Finset.range ops.length).image (fun k => fun x : A5 => val (fun _ => x) ops k)).card
      ≤ 30 := by
  sorry

section Dominators

variable {α : Type} (ops : List (Op α))

/-- `Avoids d v`: node `v` is reached from some entry along a path that does not pass
through `d` (paths follow operand arcs). -/
inductive Avoids (d : ℕ) : ℕ → Prop
  | leaf {v : ℕ} {a : α} : v ≠ d → ops[v]? = some (.leaf a) → Avoids d v
  | mulLeft {v i j : ℕ} : v ≠ d → ops[v]? = some (.mul i j) → Avoids d i → Avoids d v
  | mulRight {v i j : ℕ} : v ≠ d → ops[v]? = some (.mul i j) → Avoids d j → Avoids d v
  | inv {v i : ℕ} : v ≠ d → ops[v]? = some (.inv i) → Avoids d i → Avoids d v

/-- `d` dominates the node `v`: every path from an entry (from the added source) to `v` passes
through `d`. -/
def Dominates (d v : ℕ) : Prop := v < ops.length ∧ ¬ Avoids ops d v

variable {G : Type*} [Group G]

/-- **Dominator power condensation** (004d, Theorem 4.3). In a well-formed program over any
group, if `d` dominates `v`, then `val v = (val d)^a` for an integer exponent `a` that does not
depend on the values assigned to the entries. -/
theorem dominator_power (hwf : WellFormed ops) {d v : ℕ} (hdom : Dominates ops d v) :
    ∃ a : ℤ, ∀ ν : α → G, val ν ops v = (val ν ops d) ^ a := by
  sorry

/-- An inverse gate is dominated by its operand (004d, Theorem 4.3(iii)). -/
theorem inv_gate_dominated {v i : ℕ} (hv : v < ops.length) (h : ops[v]? = some (.inv i)) :
    Dominates ops i v := by
  sorry

/-- A squaring gate `u · u` is dominated by its operand (004d, Theorem 4.3(iii)). -/
theorem square_gate_dominated {v i : ℕ} (hv : v < ops.length) (h : ops[v]? = some (.mul i i)) :
    Dominates ops i v := by
  sorry

end Dominators

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

/-- Terminal values: `P ↦ p`, `Q ↦ q`. -/
def pq : Fin 2 → Perm (Fin 5) := ![pA, qA]

/-- The library: `P, Q, P⁻¹, Q⁻¹, P P⁻¹`, then one product per remaining element along a
breadth-first tree of the Cayley graph. -/
def libOps : List (Op (Fin 2)) :=
  [Op.leaf 0, Op.leaf 1, Op.inv 0, Op.inv 1, Op.mul 0 2, Op.mul 0 0, Op.mul 0 1, Op.mul 0 3, Op.mul 1 0, Op.mul 1 2, Op.mul 2 1, Op.mul 2 2, Op.mul 2 3, Op.mul 3 0, Op.mul 3 2, Op.mul 5 1, Op.mul 5 3, Op.mul 6 0, Op.mul 6 2, Op.mul 7 0, Op.mul 7 2, Op.mul 8 0, Op.mul 8 1, Op.mul 8 3, Op.mul 9 2, Op.mul 9 3, Op.mul 10 0, Op.mul 10 2, Op.mul 11 1, Op.mul 12 0, Op.mul 13 0, Op.mul 13 1, Op.mul 14 1, Op.mul 14 3, Op.mul 16 0, Op.mul 17 1, Op.mul 17 3, Op.mul 18 3, Op.mul 19 0, Op.mul 20 1, Op.mul 20 3, Op.mul 22 0, Op.mul 23 2, Op.mul 24 1, Op.mul 25 0, Op.mul 26 1, Op.mul 26 3, Op.mul 29 1, Op.mul 31 0, Op.mul 31 2, Op.mul 32 0, Op.mul 35 0, Op.mul 36 2, Op.mul 37 0, Op.mul 39 0, Op.mul 41 3, Op.mul 42 1, Op.mul 44 1, Op.mul 48 1, Op.mul 53 1]

/-- Index of an element in the library (`4` is the identity node). -/
def libIdx (g : Perm (Fin 5)) : ℕ := A5list.idxOf g

/-- Redirect one operation of an `A₅` circuit into the two-generator program: a constant `g`
becomes the copy `lib(g) · lib(e)`; other gates are shifted by 60. -/
def redirect : Op (Perm (Fin 5)) → Op (Fin 2)
  | .leaf g => .mul (libIdx g) 4
  | .mul i j => .mul (60 + i) (60 + j)
  | .inv i => .inv (60 + i)

/-- The two-generator normal form of an `A₅` circuit. -/
def normalForm (C : List (Op (Perm (Fin 5)))) : List (Op (Fin 2)) := libOps ++ C.map redirect

/-- **One entry versus two entries** (004d, Theorem 6.1, mathematical content). (i) Over every
group, a program with one entry computes only powers of the entry, with exponents given by the
local rules. (ii) Programs with the two entries `P ↦ p`, `Q ↦ q` of `A₅` and no constants carry
every Boolean circuit: the copy of each Boolean node evaluates to `e` or `a` according to its
value (with size at most `17 s + 60`). -/
theorem dichotomy :
    (∀ {G : Type} [Group G] (ops : List (Op Unit)) (k : ℕ) (x : G),
      val (fun _ => x) ops k = x ^ oneEntryExp ops k) ∧
    (∀ bs : List BOp, BWellFormed bs →
      WellFormed (normalForm (compile bs).1) ∧
      (normalForm (compile bs).1).length ≤ 17 * bs.length + 60 ∧
      ∀ k < bs.length,
        val pq (normalForm (compile bs).1) (60 + (compile bs).2.getD k 0) = enc (bval bs k)) := by
  sorry

end GC.A5Programs
