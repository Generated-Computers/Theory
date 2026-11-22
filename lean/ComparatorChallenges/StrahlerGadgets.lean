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

/-- The commutator convention of the papers, `[x, y] = x⁻¹ y⁻¹ x y`. -/
def pcomm (x y : Perm (Fin 5)) : Perm (Fin 5) := x⁻¹ * y⁻¹ * x * y

/-- 004g, Lemma 3.2: the gadget elements are even and satisfy
`c⁻¹ a c = b`, `[a, b] = (1 4 2 3 5)` and `d⁻¹ [a, b] d = a`. -/
theorem gadget_identities :
    (aA ∈ alternatingGroup (Fin 5) ∧ bA ∈ alternatingGroup (Fin 5) ∧
      cA ∈ alternatingGroup (Fin 5) ∧ dA ∈ alternatingGroup (Fin 5)) ∧
    cA⁻¹ * aA * cA = bA ∧ pcomm aA bA = abComm ∧ dA⁻¹ * pcomm aA bA * dA = aA := by
  sorry

/-- Encoding of Boolean values: `false ↦ e`, `true ↦ a`. -/
def enc : Bool → Perm (Fin 5)
  | false => 1
  | true => aA

/-- The NOT gadget `a x⁴`. -/
def notGadget (x : Perm (Fin 5)) : Perm (Fin 5) := aA * x ^ 4
/-- The AND gadget `d⁻¹ [x, c⁻¹ y c] d`. -/
def andGadget (x y : Perm (Fin 5)) : Perm (Fin 5) := dA⁻¹ * pcomm x (cA⁻¹ * y * cA) * dA

/-- 004g, Theorem 3.3 (and 004a, Lemma 2.2): the gadgets compute NOT and AND on encodings, and
the multiplication-only form of AND, `d⁻¹ x⁴ (c⁻¹ y⁴ c) x (c⁻¹ y c) d`, agrees with it. -/
theorem gadgets_correct (u v : Bool) :
    notGadget (enc u) = enc (!u) ∧ andGadget (enc u) (enc v) = enc (u && v) ∧
    dA⁻¹ * enc u ^ 4 * (cA⁻¹ * enc v ^ 4 * cA) * enc u * (cA⁻¹ * enc v * cA) * dA =
      enc (u && v) := by
  sorry

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

/-- A multiplication circuit with constants in `A₅`: no inverse gates, every constant even. -/
def IsMulCircuit (ops : List (Op (Perm (Fin 5)))) : Prop :=
  ∀ op ∈ ops, match op with
    | .leaf g => g ∈ alternatingGroup (Fin 5)
    | .mul _ _ => True
    | .inv _ => False

/-- **Linear Boolean-to-`A₅` reduction** (004g, Corollary 3.4; 004a, Lemma 2.2). For every
well-formed Boolean circuit `bs` of size `s`, the compiled program is an `A₅` multiplication
circuit (constants in `A₅`, no inverse gates, operands earlier) of size at most `17 s`, and every
Boolean node `k` has a copy whose value is the encoding of its Boolean value. In particular the
output is `1` iff the copy of the output evaluates to `a`. -/
theorem boolean_to_A5 (bs : List BOp) (hwf : BWellFormed bs) :
    IsMulCircuit (compile bs).1 ∧ WellFormed (compile bs).1 ∧
    (compile bs).1.length ≤ 17 * bs.length ∧
    ∀ k < bs.length, val id (compile bs).1 ((compile bs).2.getD k 0) = enc (bval bs k) := by
  sorry

/-- The largest element of a list of naturals (`0` for the empty list). -/
def lmax (l : List ℕ) : ℕ := l.foldr max 0

/-- The Strahler rule: inputs and gates without predecessors have rank `0`; otherwise the
largest rank `r₁` among the distinct predecessors, plus one if it is attained twice. -/
def rankStep (rs : List ℕ) (ps : List ℕ) : ℕ :=
  if ps.dedup = [] then 0
  else
    let vals := ps.dedup.map (fun u => rs.getD u 0)
    if 2 ≤ vals.count (lmax vals) then lmax vals + 1 else lmax vals

/-- Ranks of all vertices; vertex `k` has predecessor list `cs[k]`. -/
def ranks (cs : List (List ℕ)) : List ℕ := cs.foldl (fun rs ps => rs ++ [rankStep rs ps]) []

/-- Size of the unfolding of the cone (over distinct predecessors). -/
def unfoldStep (us : List ℕ) (ps : List ℕ) : ℕ := 1 + (ps.dedup.map (fun u => us.getD u 0)).sum

/-- Unfolding sizes of all vertices. -/
def unfoldSizes (cs : List (List ℕ)) : List ℕ :=
  cs.foldl (fun us ps => us ++ [unfoldStep us ps]) []

/-- Every vertex lists only earlier vertices as predecessors. -/
def CircWF (cs : List (List ℕ)) : Prop := ∀ k (h : k < cs.length), ∀ u ∈ cs[k]'h, u < k

/-- **Unfolding bound** (004g, Corollary 6.8): `2^{sr(v)} ≤ U(v)` for every vertex, that is,
`sr(v) ≤ log₂ U(v)`. -/
theorem strahler_unfolding (cs : List (List ℕ)) (hwf : CircWF cs) :
    ∀ k < cs.length, 2 ^ (ranks cs).getD k 0 ≤ (unfoldSizes cs).getD k 0 := by
  sorry

/-- Rank does not decrease along arcs: every predecessor has rank at most that of the vertex. -/
theorem strahler_mono (cs : List (List ℕ)) (hwf : CircWF cs) :
    ∀ k (hk : k < cs.length), ∀ u ∈ cs[k]'hk, (ranks cs).getD u 0 ≤ (ranks cs).getD k 0 := by
  sorry

section Quotient

variable {α : Type} {G : Type*} [Group G]

/-- Redirect the operands of an operation through `ρ`. -/
def Op.redirect (ρ : ℕ → ℕ) : Op α → Op α
  | .leaf a => .leaf a
  | .mul i j => .mul (ρ i) (ρ j)
  | .inv i => .inv (ρ i)

/-- **Quotient lemma** (004g, Lemma 6.1). Let `ρ` send every vertex to a vertex not after it
(the earliest member of its class) with the same value. Redirecting every operand through `ρ`
leaves all values unchanged. -/
theorem quotient_val (ν : α → G) (C : List (Op α)) (hwf : WellFormed C) (ρ : ℕ → ℕ)
    (hρle : ∀ u, ρ u ≤ u) (hρval : ∀ u, val ν C (ρ u) = val ν C u) :
    ∀ k < C.length, val ν (C.map (Op.redirect ρ)) k = val ν C k := by
  sorry

end Quotient

end GC.A5Programs
