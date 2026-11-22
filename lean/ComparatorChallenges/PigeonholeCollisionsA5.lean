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

/-- Group terms in `k` variables with constants from `G`. -/
inductive GTerm (G : Type*) (k : ℕ) where
  | var : Fin k → GTerm G k
  | const : G → GTerm G k
  | mul : GTerm G k → GTerm G k → GTerm G k
  | inv : GTerm G k → GTerm G k

section MaurerRhodesTerms

variable {G : Type*} [Group G] {k : ℕ}

/-- Evaluation of a group term. -/
def GTerm.eval : GTerm G k → (Fin k → G) → G
  | .var i, x => x i
  | .const g, _ => g
  | .mul s t, x => s.eval x * t.eval x
  | .inv t, x => (t.eval x)⁻¹

/-- A function `G^k → G` is polynomial if some group term with constants computes it. -/
def IsPolynomial (f : (Fin k → G) → G) : Prop := ∃ t : GTerm G k, ∀ x, t.eval x = f x

section Simple

variable [IsSimpleGroup G]

variable [Fintype G] [DecidableEq G]

/-- **Maurer–Rhodes.** In a finite simple nonabelian group every function `G^k → G` is a
polynomial function. -/
theorem maurer_rhodes (hG : ∃ a b : G, a * b ≠ b * a) (f : (Fin k → G) → G) :
    IsPolynomial f := by
  sorry

end Simple

end MaurerRhodesTerms

/-- `A₅` as a group: the alternating group on five points. -/
abbrev A5 := alternatingGroup (Fin 5)

/-- **61-probe collision selector for `A₅`** (004a, Theorem 3.2). There are an enumeration
`A₅ ≃ Fin 60` and 61 fixed unary group terms `T_0, …, T_60` with constants in `A₅` such that for
every value `x` of the anchor node, the probe values `T_i(x)` contain exactly one equal pair,
namely `{0, enum x + 1}`. -/
theorem probe_selector_A5 : ∃ (enum : A5 ≃ Fin 60) (T : Fin 61 → GTerm A5 1),
    ∀ x : A5, ∀ i j : Fin 61, i < j →
      ((T i).eval (fun _ => x) = (T j).eval (fun _ => x) ↔ i = 0 ∧ j = (enum x).succ) := by
  sorry

/-- **Collision search is as hard as evaluation** (004a, Corollary 3.4, mathematical core): any
colliding pair of the 61 probes determines the value of the anchor. -/
theorem collision_determines_value : ∃ T : Fin 61 → GTerm A5 1,
    (∀ x : A5, ∃ i j : Fin 61, i < j ∧ (T i).eval (fun _ => x) = (T j).eval (fun _ => x)) ∧
    ∀ x y : A5, ∀ i j : Fin 61, i < j →
      (T i).eval (fun _ => x) = (T j).eval (fun _ => x) →
      (T i).eval (fun _ => y) = (T j).eval (fun _ => y) → x = y := by
  sorry

/-- **Predicate-complete equality** (004a, Theorem 3.5): for every `S ⊆ A₅` there are unary terms
`U, V` with `U(x) = V(x)` exactly when `x ∈ S`. -/
theorem predicate_complete_A5 (S : Set A5) :
    ∃ U V : GTerm A5 1, ∀ x : A5, U.eval (fun _ => x) = V.eval (fun _ => x) ↔ x ∈ S := by
  sorry

/-- **Universal collisions under a small context** (004a, Theorem 4.2 and Corollary 4.3). Let
`U` be a set of `N` nodes with explicit value tables `f u : X → A₅` over a finite context set `X`.
Then there are pairwise disjoint pairs of distinct nodes of `U`, at least `(N - 60^|X|)/2` of
them, whose tables agree, so that the two nodes are equal whatever the true context is. For
`|X| = 2` the bound is `(N - 3600)/2`. -/
theorem universal_collisions {ι X : Type*} [DecidableEq ι] [Fintype X] [DecidableEq X]
    (U : Finset ι) (f : ι → X → A5) :
    ∃ M : Finset (ι × ι), (∀ p ∈ M, p.1 ∈ U ∧ p.2 ∈ U ∧ p.1 ≠ p.2 ∧ ∀ x, f p.1 x = f p.2 x) ∧
      (M.image Prod.fst ∪ M.image Prod.snd).card = 2 * M.card ∧
      U.card ≤ 2 * M.card + 60 ^ Fintype.card X := by
  sorry

section Calculus

variable {α : Type} {G : Type*} [Group G] (ν : α → G) (ops : List (Op α))

/-- Facts: `V g u` (node `u` has value `g`) and `E u v` (nodes `u, v` have equal values). -/
inductive Fact (G : Type*) where
  | V : G → ℕ → Fact G
  | E : ℕ → ℕ → Fact G

/-- The calculus (R1)–(R6) of 004a, Section 5. -/
inductive Derivable : Fact G → Prop
  | leaf {u : ℕ} {a : α} : ops[u]? = some (.leaf a) → Derivable (.V (ν a) u)
  | fwdMul {z x y : ℕ} {g h : G} : ops[z]? = some (.mul x y) →
      Derivable (.V g x) → Derivable (.V h y) → Derivable (.V (g * h) z)
  | fwdInv {z x : ℕ} {g : G} : ops[z]? = some (.inv x) →
      Derivable (.V g x) → Derivable (.V g⁻¹ z)
  | bwdInv {z x : ℕ} {g : G} : ops[z]? = some (.inv x) →
      Derivable (.V g z) → Derivable (.V g⁻¹ x)
  | cancelLeft {z x y : ℕ} {k g : G} : ops[z]? = some (.mul x y) →
      Derivable (.V k z) → Derivable (.V g x) → Derivable (.V (g⁻¹ * k) y)
  | cancelRight {z x y : ℕ} {k h : G} : ops[z]? = some (.mul x y) →
      Derivable (.V k z) → Derivable (.V h y) → Derivable (.V (k * h⁻¹) x)
  | eqOfVal {u v : ℕ} {g : G} : Derivable (.V g u) → Derivable (.V g v) → Derivable (.E u v)
  | congMul {z x y z' x' y' : ℕ} : ops[z]? = some (.mul x y) → ops[z']? = some (.mul x' y') →
      Derivable (.E x x') → Derivable (.E y y') → Derivable (.E z z')
  | cancMulLeft {z x y z' x' y' : ℕ} : ops[z]? = some (.mul x y) →
      ops[z']? = some (.mul x' y') →
      Derivable (.E z z') → Derivable (.E x x') → Derivable (.E y y')
  | cancMulRight {z x y z' x' y' : ℕ} : ops[z]? = some (.mul x y) →
      ops[z']? = some (.mul x' y') →
      Derivable (.E z z') → Derivable (.E y y') → Derivable (.E x x')
  | congInv {z x z' x' : ℕ} : ops[z]? = some (.inv x) → ops[z']? = some (.inv x') →
      Derivable (.E x x') → Derivable (.E z z')
  | cancInv {z x z' x' : ℕ} : ops[z]? = some (.inv x) → ops[z']? = some (.inv x') →
      Derivable (.E z z') → Derivable (.E x x')
  | symm {u v : ℕ} : Derivable (.E u v) → Derivable (.E v u)
  | trans {u v w : ℕ} : Derivable (.E u v) → Derivable (.E v w) → Derivable (.E u w)

/-- Truth of a fact in the evaluation of the program. -/
def Fact.Holds : Fact G → Prop
  | .V g u => val ν ops u = g
  | .E u v => val ν ops u = val ν ops v

/-- **Soundness** (004a, Theorem 5.1): in a well-formed program every derivable fact is
true. -/
theorem calculus_sound (hwf : WellFormed ops) {f : Fact G} (h : Derivable ν ops f) :
    f.Holds ν ops := by
  sorry

/-- **Completeness** (004a, Theorem 5.1): in a well-formed program, `V (val u) u` is derivable
for every node `u`, and `E u v` is derivable whenever `val u = val v`. -/
theorem calculus_complete (hwf : WellFormed ops) :
    (∀ u < ops.length, Derivable ν ops (.V (val ν ops u) u)) ∧
    (∀ u < ops.length, ∀ v < ops.length, val ν ops u = val ν ops v →
      Derivable ν ops (.E u v)) := by
  sorry

end Calculus

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

/-- **Boolean circuits to constant-free two-generator programs** (004a, Lemma 2.2; 004d,
Theorem 6.1(ii)). Every well-formed Boolean circuit of size `s` becomes a well-formed
program over the two terminals `P ↦ p`, `Q ↦ q` of size at most `17 s + 60`, without constants,
in which the copy of every Boolean node evaluates to the encoding (`e` or `a`) of its value. -/
theorem boolean_to_twoGen (bs : List BOp) (hwf : BWellFormed bs) :
    WellFormed (normalForm (compile bs).1) ∧
    (normalForm (compile bs).1).length ≤ 17 * bs.length + 60 ∧
    ∀ k < bs.length,
      val pq (normalForm (compile bs).1) (60 + (compile bs).2.getD k 0) = enc (bval bs k) := by
  sorry

end GC.A5Programs
