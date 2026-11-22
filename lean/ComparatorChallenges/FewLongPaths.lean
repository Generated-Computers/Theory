import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Lattice.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Comparator challenge for manuscript 006g (Few Long Paths Put Sequential NOR in QuasiNC). -/


/-!
# Sequential NOR: basic definitions

A parent array of length `n` is modelled as a function `j : ℕ → ℕ` with `j i < i` for
`1 ≤ i ≤ n` (the values `j 0` and `j i`, `i > n`, are irrelevant).  Its trace is
`x 0 = 1`, `x i = NOR (x (i-1)) (x (j i))`.

The arc of position `i` (`1 ≤ i ≤ n`) is `(j i, i)`; every position is the right endpoint of
exactly one arc, so a page assignment is a function of the right endpoint.
-/

namespace GC.SeqNORNormalForms

/-- Boolean NOR. -/
def nor (a b : Bool) : Bool := !(a || b)

/-- `j` is a parent array of length `n`: `j i < i` for every `1 ≤ i ≤ n`. -/
def IsParentArray (n : ℕ) (j : ℕ → ℕ) : Prop :=
  ∀ i, 1 ≤ i → i ≤ n → j i < i

/-- The Sequential NOR trace: `x 0 = true` and `x (i+1) = NOR (x i) (x (j (i+1)))`.
(If `j (i+1) ≥ i+1`, which never happens for a parent array, a junk value is used.) -/
def trace (j : ℕ → ℕ) : ℕ → Bool
  | 0 => true
  | i + 1 => nor (trace j i) (if h : j (i + 1) < i + 1 then trace j (j (i + 1)) else true)
termination_by i => i

/-- Two arcs `(a,b)` and `(a',b')` (with `a < b`, `a' < b'`) cross if their endpoints
strictly interleave. -/
def Cross (a b a' b' : ℕ) : Prop :=
  (a < a' ∧ a' < b ∧ b < b') ∨ (a' < a ∧ a < b' ∧ b' < b)

/-- A `k`-page assignment of the arcs `(j i, i)`, `1 ≤ i ≤ n`: arcs on the same page do not
cross. -/
def IsPageAssignment (n : ℕ) (j : ℕ → ℕ) (k : ℕ) (page : ℕ → Fin k) : Prop :=
  ∀ i i', 1 ≤ i → i ≤ n → 1 ≤ i' → i' ≤ n → page i = page i' → ¬ Cross (j i) i (j i') i'

/-- `pg(j) ≤ k`: the arcs of `j` have a `k`-page assignment. -/
def PageNumberLE (n : ℕ) (j : ℕ → ℕ) (k : ℕ) : Prop :=
  ∃ page : ℕ → Fin k, IsPageAssignment n j k page

/-- A NOR circuit with `G ≥ 2` gates: wires `w 0 = 1`, `w 1 = 0` and
`w g = NOR (w (a g)) (w (b g))` for `2 ≤ g ≤ G`, with `a g, b g < g`. -/
structure NorCircuit where
  G : ℕ
  a : ℕ → ℕ
  b : ℕ → ℕ

/-- Well-formedness of a NOR circuit. -/
def NorCircuit.Valid (C : NorCircuit) : Prop :=
  2 ≤ C.G ∧ ∀ g, 2 ≤ g → g ≤ C.G → C.a g < g ∧ C.b g < g

/-- The wire values of a NOR circuit. -/
def NorCircuit.wire (C : NorCircuit) : ℕ → Bool
  | 0 => true
  | 1 => false
  | g + 2 => nor (if h : C.a (g + 2) < g + 2 then C.wire (C.a (g + 2)) else false)
                 (if h : C.b (g + 2) < g + 2 then C.wire (C.b (g + 2)) else false)
termination_by g => g

/-! ### Elementary lemmas -/

end GC.SeqNORNormalForms


/-!
# 006f: Sequential NOR is circuit evaluation on its binary core

Resets `j_i = 0`, chronological negations `j_i = i - 1`, anchors `1 ≤ j_i ≤ i - 2`; an anchor
is guarded if `j_{i-1} = 0`. The binary core `B(j)` is the set of unguarded anchors. Core
variables are indexed here by the core position `b ∈ B(j)` itself instead of its rank `k`
(the rank is an order-preserving renaming).
-/

namespace GC.SeqNORNormalForms

/-- `i` is an unguarded anchor: `1 ≤ j_i ≤ i - 2` and `j_{i-1} ≠ 0`. -/
def IsCore (j : ℕ → ℕ) (i : ℕ) : Prop := 1 ≤ j i ∧ j i + 2 ≤ i ∧ j (i - 1) ≠ 0

instance (j : ℕ → ℕ) (i : ℕ) : Decidable (IsCore j i) := by unfold IsCore; infer_instance

/-- Predecessor of a non-root: `q - 1` for a chronological negation, `j_q` for a guarded
anchor. -/
def corePred (j : ℕ → ℕ) (q : ℕ) : ℕ := if j q = q - 1 then q - 1 else j q

/-- Descriptors: a constant or a signed reference `(b, σ)` to a core variable. -/
inductive Desc
  | const (c : Bool)
  | ref (b : ℕ) (σ : Bool)
  deriving DecidableEq, Repr

/-- Negation of a descriptor. -/
def Desc.neg : Desc → Desc
  | Desc.const c => Desc.const (!c)
  | Desc.ref b σ => Desc.ref b (!σ)

/-- Value `⟦d⟧(w)` of a descriptor. -/
def Desc.sem (w : ℕ → Bool) : Desc → Bool
  | Desc.const c => c
  | Desc.ref b σ => xor (w b) σ

/-- The descriptor `δ(q)`: `1` at `0`, `0` at resets, `(q, 0)` at core positions, and the
negated descriptor of the predecessor otherwise. -/
def desc (j : ℕ → ℕ) : ℕ → Desc
  | 0 => Desc.const true
  | q + 1 =>
      if j (q + 1) = 0 then Desc.const false
      else if IsCore j (q + 1) then Desc.ref (q + 1) false
      else if h : corePred j (q + 1) < q + 1 then (desc j (corePred j (q + 1))).neg
      else Desc.const false
termination_by q => q

/-- The variables mentioned by a descriptor. -/
def Desc.Mentions : Desc → ℕ → Prop
  | Desc.const _, _ => False
  | Desc.ref b _, b' => b = b'

section

variable (j : ℕ → ℕ)

/-- The core system (Definition 3.1 of 006f): `w_b = NOR(⟦L_b⟧ w, ⟦R_b⟧ w)` for every core position
`b ≤ n`, with `L_b = δ(b-1)` and `R_b = δ(j_b)`. -/
def CoreSystemHolds (n : ℕ) (w : ℕ → Bool) : Prop :=
  ∀ b, 1 ≤ b → b ≤ n → IsCore j b →
    w b = nor ((desc j (b - 1)).sem w) ((desc j (j b)).sem w)

end

/-! ### Four-coordinate universality (Section 5) -/

/-- A source of a gate of an ordered NOR circuit: an input `a_ℓ` (`1 ≤ ℓ ≤ t`) or an earlier
gate `w_ℓ`. -/
inductive CSrc
  | inp (ℓ : ℕ)
  | gate (ℓ : ℕ)
  deriving DecidableEq, Repr

/-- An ordered NOR circuit with `t` assigned inputs `a_1, …, a_t` and gates
`w_i = NOR(u_i, v_i)`, `1 ≤ i ≤ G`. -/
structure OrderedNorCircuit where
  t : ℕ
  G : ℕ
  a : ℕ → Bool
  u : ℕ → CSrc
  v : ℕ → CSrc

/-- A source is legal for gate `i`. -/
def OrderedNorCircuit.SrcOK (C : OrderedNorCircuit) (i : ℕ) : CSrc → Prop
  | CSrc.inp ℓ => 1 ≤ ℓ ∧ ℓ ≤ C.t
  | CSrc.gate ℓ => 1 ≤ ℓ ∧ ℓ < i

/-- Well-formedness. -/
def OrderedNorCircuit.Valid (C : OrderedNorCircuit) : Prop :=
  ∀ i, 1 ≤ i → i ≤ C.G → C.SrcOK i (C.u i) ∧ C.SrcOK i (C.v i)

/-- Gate values. -/
def OrderedNorCircuit.gateVal (C : OrderedNorCircuit) : ℕ → Bool
  | 0 => false
  | i + 1 =>
      nor (match C.u (i + 1) with
            | CSrc.inp ℓ => C.a ℓ
            | CSrc.gate ℓ => if h : ℓ < i + 1 then C.gateVal ℓ else false)
          (match C.v (i + 1) with
            | CSrc.inp ℓ => C.a ℓ
            | CSrc.gate ℓ => if h : ℓ < i + 1 then C.gateVal ℓ else false)
termination_by i => i

/-- Value of a source. -/
def OrderedNorCircuit.srcVal (C : OrderedNorCircuit) : CSrc → Bool
  | CSrc.inp ℓ => C.a ℓ
  | CSrc.gate ℓ => C.gateVal ℓ

/-- Representative coordinate: `Rep(a_ℓ) = 2ℓ + 1`, `Rep(w_i) = 2t + 4i + 1`. -/
def OrderedNorCircuit.rep (C : OrderedNorCircuit) : CSrc → ℕ
  | CSrc.inp ℓ => 2 * ℓ + 1
  | CSrc.gate i => 2 * C.t + 4 * i + 1

/-- **Definition 5.1 of 006f.** `Embed(C)`: the permanent zero `j_1 = 0`, the input gadget
`j_{2ℓ} = 0`, `j_{2ℓ+1} = a_ℓ` at `(2ℓ, 2ℓ+1)`, and the NOR gadget
`j_s = 0, j_{s+1} = Rep(u_i), j_{s+2} = s + 1, j_{s+3} = Rep(v_i)` at `s = 2t + 4i - 2`. -/
def OrderedNorCircuit.embed (C : OrderedNorCircuit) (q : ℕ) : ℕ :=
  if q ≤ 1 then 0
  else if q ≤ 2 * C.t + 1 then
    (if q % 2 = 0 then 0 else if C.a (q / 2) then 1 else 0)
  else
    let i := (q - (2 * C.t + 2)) / 4 + 1
    let r := (q - (2 * C.t + 2)) % 4
    if r = 0 then 0
    else if r = 1 then C.rep (C.u i)
    else if r = 2 then q - 1
    else C.rep (C.v i)

/-- Length `n = 1 + 2t + 4G` of the embedding. -/
def OrderedNorCircuit.len (C : OrderedNorCircuit) : ℕ := 1 + 2 * C.t + 4 * C.G

section Embed

variable (C : OrderedNorCircuit)

end Embed

end GC.SeqNORNormalForms


/-!
# 006g: depth deletion is long-path hitting; the path formula

For a finite digraph `D = (V, Adj)` (a DAG in the paper), a directed path is a list of
vertices with consecutive arcs (`List.IsChain Adj`), and `depth(D - X) ≤ M` means that every
directed path avoiding `X` has at most `M` vertices. `δ_M(D)` is the least size of such an
`X`.
-/

namespace GC.SeqNORNormalForms

/-- `depth(D - X) ≤ M`. -/
def DepthLE {V : Type*} (Adj : V → V → Prop) (X : Finset V) (M : ℕ) : Prop :=
  ∀ p : List V, p.IsChain Adj → (∀ v ∈ p, v ∉ X) → p.length ≤ M

/-- `δ_M(D) = min {|X| : depth(D - X) ≤ M}`. -/
noncomputable def deletionNumber {V : Type*} (Adj : V → V → Prop) (M : ℕ) : ℕ :=
  sInf {k | ∃ X : Finset V, X.card = k ∧ DepthLE Adj X M}

section DAG

variable {V : Type*} [Fintype V] [DecidableEq V] (Adj : V → V → Prop)

/-- **Theorem 4.1 of 006g (path-hitting identity).** `depth(D - X) ≤ M` iff `X` meets every
directed path of `D` with exactly `M + 1` vertices. -/
theorem path_hitting (X : Finset V) (M : ℕ) :
    DepthLE Adj X M ↔ ∀ p : List V, p.IsChain Adj → p.length = M + 1 → ∃ v ∈ p, v ∈ X := by
  sorry

/-- **Theorem 4.3 of 006g (packing sandwich).** If `P_1, …, P_q` is a maximal family of
pairwise disjoint directed paths with `M + 1` vertices each, then
`q ≤ δ_M(D) ≤ (M+1) q`. -/
theorem packing_sandwich (M q : ℕ) (ps : Fin q → List V) (hc : ∀ t, (ps t).IsChain Adj)
    (hl : ∀ t, (ps t).length = M + 1) (hdisj : ∀ t t', t ≠ t' → ∀ v ∈ ps t, v ∉ ps t')
    (hmax : ∀ p : List V, p.IsChain Adj → p.length = M + 1 → ∃ t, ∃ v ∈ p, v ∈ ps t) :
    q ≤ deletionNumber Adj M ∧ deletionNumber Adj M ≤ (M + 1) * q := by
  sorry

end DAG

/-! ### The directed path `C_L` (Theorem 5.2) -/

/-- The directed path `C_L` on the vertices `0, …, L-1`. -/
def pathAdj (L : ℕ) (u v : Fin L) : Prop := v.val = u.val + 1

/-- The block path `a, a+1, …, a+len-1` in `C_L`. -/
def blockPath (L : ℕ) : (a len : ℕ) → a + len ≤ L → List (Fin L)
  | _, 0, _ => []
  | a, len + 1, h => ⟨a, by omega⟩ :: blockPath L (a + 1) len (by omega)

/-- **Theorem 5.2 of 006g (path formula).** For the directed path `C_L` and every `M`,
`δ_M(C_L) = ⌊L / (M+1)⌋`. -/
theorem path_formula (L M : ℕ) : deletionNumber (pathAdj L) M = L / (M + 1) := by
  sorry

end GC.SeqNORNormalForms
