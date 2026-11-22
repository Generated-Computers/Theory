import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Nat.Basic

/-! Comparator challenge for manuscript 006f (Sequential NOR Is Circuit Evaluation on Its Binary Core). -/


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

/-- **Lemma 2.2 of 006f (root classification).** A coordinate `1 ≤ q ≤ n` that is neither a
reset nor a core position has a predecessor `p(q) < q` with `x_q = ¬ x_{p(q)}`. -/
theorem root_classification (n : ℕ) (hj : IsParentArray n j) (q : ℕ) (hq : 1 ≤ q) (hqn : q ≤ n)
    (h0 : j q ≠ 0) (hc : ¬ IsCore j q) :
    corePred j q < q ∧ trace j q = !trace j (corePred j q) := by
  sorry

/-- **Section 3 of 006f (descriptor equation).** `x_q = ⟦δ(q)⟧(z)` for the true core vector `z` (`z_b = x_b`),
and `δ(q)` mentions only core positions `b ≤ q`. -/
theorem desc_correct (n : ℕ) (hj : IsParentArray n j) :
    ∀ q, q ≤ n → trace j q = (desc j q).sem (trace j) ∧
      ∀ b, (desc j q).Mentions b → IsCore j b ∧ 1 ≤ b ∧ b ≤ q := by
  sorry

/-- The core system (Definition 3.1 of 006f): `w_b = NOR(⟦L_b⟧ w, ⟦R_b⟧ w)` for every core position
`b ≤ n`, with `L_b = δ(b-1)` and `R_b = δ(j_b)`. -/
def CoreSystemHolds (n : ℕ) (w : ℕ → Bool) : Prop :=
  ∀ b, 1 ≤ b → b ≤ n → IsCore j b →
    w b = nor ((desc j (b - 1)).sem w) ((desc j (j b)).sem w)

/-- **Lemma 3.2 of 006f (triangularity).** The descriptors `L_b`, `R_b` of the equation of a
core position `b` mention only core positions `< b`. -/
theorem core_triangular (n : ℕ) (hj : IsParentArray n j) (b : ℕ) (hb : 1 ≤ b) (hbn : b ≤ n)
    (hc : IsCore j b) :
    (∀ b', (desc j (b - 1)).Mentions b' → IsCore j b' ∧ b' < b) ∧
    (∀ b', (desc j (j b)).Mentions b' → IsCore j b' ∧ b' < b) := by
  sorry

/-- **Lemma 3.2 of 006f (unique solution).** The true core vector solves the core system, and
every solution agrees with it on all core positions `≤ n`. -/
theorem core_system_unique (n : ℕ) (hj : IsParentArray n j) :
    CoreSystemHolds j n (trace j) ∧
    ∀ w, CoreSystemHolds j n w → ∀ b, 1 ≤ b → b ≤ n → IsCore j b → w b = trace j b := by
  sorry

/-- **Theorem 3.4 of 006f (retraction), mathematical content.** Substituting any solution of
the core system into the descriptors gives the whole trace. -/
theorem retraction (n : ℕ) (hj : IsParentArray n j) (w : ℕ → Bool)
    (hw : CoreSystemHolds j n w) : ∀ q, q ≤ n → (desc j q).sem w = trace j q := by
  sorry

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

/-- **Theorem 5.2 of 006f (four-coordinate universality).** For every ordered NOR circuit
with `t` inputs and `G` gates, `j = Embed(C)` is a parent array of length `1 + 2t + 4G` with
`x_{Rep(y)} = y` for every input and gate `y` (so `x_n = w_G`); its binary core is exactly
`{Rep(w_1) < … < Rep(w_G)}`; the descriptors are `δ(Rep(a_ℓ)) = a_ℓ` and
`δ(Rep(w_i)) = (Rep(w_i), 0)`; and the core equation of `Rep(w_i)` is
`L = δ(Rep(u_i))`, `R = δ(Rep(v_i))`, i.e. exactly the gate equation of `C`. -/
theorem embed_universal (hC : C.Valid) :
    IsParentArray C.len C.embed ∧
    (∀ ℓ, 1 ≤ ℓ → ℓ ≤ C.t → trace C.embed (C.rep (CSrc.inp ℓ)) = C.a ℓ ∧
      desc C.embed (C.rep (CSrc.inp ℓ)) = Desc.const (C.a ℓ)) ∧
    (∀ i, 1 ≤ i → i ≤ C.G → trace C.embed (C.rep (CSrc.gate i)) = C.gateVal i ∧
      desc C.embed (C.rep (CSrc.gate i)) = Desc.ref (C.rep (CSrc.gate i)) false ∧
      desc C.embed (C.rep (CSrc.gate i) - 1) = desc C.embed (C.rep (C.u i)) ∧
      desc C.embed (C.embed (C.rep (CSrc.gate i))) = desc C.embed (C.rep (C.v i))) ∧
    (∀ q, 1 ≤ q → q ≤ C.len → (IsCore C.embed q ↔ ∃ i, 1 ≤ i ∧ i ≤ C.G ∧ q = C.rep (CSrc.gate i)))
    ∧ (1 ≤ C.G → trace C.embed C.len = C.gateVal C.G) := by
  sorry

end Embed

end GC.SeqNORNormalForms
