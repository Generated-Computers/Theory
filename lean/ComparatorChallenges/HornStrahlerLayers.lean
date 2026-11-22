import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Log
import Mathlib.Data.Set.Card
import Mathlib.Logic.Relation

namespace GC.NewtonStrahler

/-- A Horn rule `P ⇒ q`; the premises form a set. -/
structure Rule (F : Type*) where
  prem : Finset F
  concl : F

/-- A Horn system `(𝓕, 𝓐, 𝓡)` over the facts `F`: a set of axioms and a finite list of rules
(Definition 2.1). -/
structure HornSystem (F : Type*) where
  axioms : Set F
  rules : List (Rule F)

variable {F : Type*}

/-- Derivation trees (Definition 2.2): an axiom leaf, or a rule `P ⇒ q` of the system with one
child derivation tree for each premise `p ∈ P`. -/
inductive Deriv (H : HornSystem F) : F → Type _ where
  | ax {q : F} (h : q ∈ H.axioms) : Deriv H q
  | node (r : Rule F) (hr : r ∈ H.rules) (sub : ∀ p ∈ r.prem, Deriv H p) : Deriv H r.concl

open Classical in
/-- The Horton–Strahler combination of the ranks `g a`, `a ∈ s`: `0` if `s = ∅`; otherwise the
largest rank `r₁` if it is attained only once, and `r₁ + 1` if it is attained at least twice. -/
noncomputable def hsMax {ι : Type*} (s : Finset ι) (g : ι → ℕ) : ℕ :=
  if ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ g a = s.sup g ∧ g b = s.sup g then s.sup g + 1 else s.sup g

/-- The Horton–Strahler rank of a derivation tree (Definition 2.2). -/
noncomputable def Deriv.rank {H : HornSystem F} : {q : F} → Deriv H q → ℕ
  | _, .ax _ => 0
  | _, .node r _ sub => hsMax r.prem.attach fun p => (sub p.1 p.2).rank

variable {H : HornSystem F}

/-- `S_k`: the facts with a derivation tree of rank at most `k`. -/
def rankLayer (H : HornSystem F) (k : ℕ) : Set F := {q | ∃ T : Deriv H q, T.rank ≤ k}

/-- `S_{k-1}`: the facts with a derivation tree of rank less than `k` (so `S_{-1} = ∅`). -/
def rankBelow (H : HornSystem F) (k : ℕ) : Set F := {q | ∃ T : Deriv H q, T.rank < k}

/-- The seed set `B_k = X ∪ 𝓐 ∪ {q : (P ⇒ q) ∈ 𝓡, P ⊆ X}` for `X = S_{k-1}`. -/
def seeds (H : HornSystem F) (X : Set F) : Set F :=
  X ∪ H.axioms ∪ {q | ∃ r ∈ H.rules, (↑r.prem : Set F) ⊆ X ∧ r.concl = q}

/-- The graph `G_k` for `X = S_{k-1}`: an edge `p → q` for every rule `P ⇒ q` with
`P \ X = {p}`. -/
def layerEdge (H : HornSystem F) (X : Set F) (p q : F) : Prop :=
  ∃ r ∈ H.rules, (↑r.prem : Set F) \ X = {p} ∧ r.concl = q

/-- `Ŝ_k`: the facts reachable from the seeds in the graph `G_k` (seeds included). -/
def reachLayer (H : HornSystem F) (X : Set F) : Set F :=
  {q | ∃ b ∈ seeds H X, Relation.ReflTransGen (layerEdge H X) b q}

/-- Strahler saturation: start from `∅` and apply one reachability layer per round. -/
def saturate (H : HornSystem F) : ℕ → Set F
  | 0 => ∅
  | t + 1 => reachLayer H (saturate H t)

/-- **Theorem 4.1 (exact Strahler layers).** For every `k ≥ 0`, the set of facts reachable in
`G_k` from the seeds `B_k`, both built from `S_{k-1}`, is exactly `S_k`. -/
theorem reachLayer_rankBelow (H : HornSystem F) (k : ℕ) :
    reachLayer H (rankBelow H k) = rankLayer H k := by
  sorry

/-- **Theorem 4.1 / Theorem 5.1 (round count).** `K + 1` reachability rounds of Strahler
saturation compute exactly the set `S_K` of facts of proof rank at most `K`. -/
theorem saturate_succ (H : HornSystem F) (K : ℕ) : saturate H (K + 1) = rankLayer H K := by
  sorry

/-- **Corollary 4.2 (stabilization).** If `S_k = S_{k-1}` then `S_j = S_k` for all `j ≥ k`
(stated with `rankBelow H (k+1) = S_k` and `rankBelow H k = S_{k-1}`). -/
theorem rankBelow_stable (H : HornSystem F) {k : ℕ}
    (h : rankBelow H (k + 1) = rankBelow H k) : ∀ j ≥ k, rankBelow H j = rankBelow H k := by
  sorry

/-- **Corollary 4.2, last claim.** Over a finite set of facts, every derivable fact has proof
rank at most `|𝓕| - 1`. -/
theorem derivable_mem_rankLayer [Fintype F] {q : F} (T : Deriv H q) :
    q ∈ rankLayer H (Fintype.card F - 1) := by
  sorry

/-- The one-step operator `f(X) = 𝓐 ∪ {q : (P ⇒ q) ∈ 𝓡, P ⊆ X}`. -/
def hornStep (H : HornSystem F) (X : Set F) : Set F :=
  H.axioms ∪ {q | ∃ r ∈ H.rules, (↑r.prem : Set F) ⊆ X ∧ r.concl = q}

/-- The graph `D_X` of the differential `Df_X`: an edge `p → q` whenever some rule `P ⇒ q`
has `p ∈ P` and `P \ {p} ⊆ X`. -/
def diffEdge (H : HornSystem F) (X : Set F) (p q : F) : Prop :=
  ∃ r ∈ H.rules, p ∈ r.prem ∧ (↑r.prem : Set F) \ {p} ⊆ X ∧ r.concl = q

/-- The Boolean Newton operator `N(X) = Df_X^*(f(X))`. -/
def hornNewton (H : HornSystem F) (X : Set F) : Set F :=
  {q | ∃ b ∈ hornStep H X, Relation.ReflTransGen (diffEdge H X) b q}

/-- **Proposition 6.1 (layers are Newton iterates).** `S_k = N(S_{k-1})`. -/
theorem hornNewton_rankBelow (H : HornSystem F) (k : ℕ) :
    hornNewton H (rankBelow H k) = rankLayer H k := by
  sorry

/-- **Proposition 6.1, second claim.** `S_k = N^{k+1}(∅)`. -/
theorem hornNewton_iterate (H : HornSystem F) (k : ℕ) :
    (hornNewton H)^[k + 1] ∅ = rankLayer H k := by
  sorry

/-- The number of leaves of a derivation tree (a node with no children is a leaf). -/
def Deriv.leaves : {q : F} → Deriv H q → ℕ
  | _, .ax _ => 1
  | _, .node r _ sub => max 1 (∑ p ∈ r.prem.attach, (sub p.1 p.2).leaves)

/-- **Lemma 2.3(b).** A derivation tree of rank `r` has at least `2^r` leaves. -/
theorem Deriv.two_pow_rank_le_leaves {q : F} (T : Deriv H q) : 2 ^ T.rank ≤ T.leaves := by
  sorry

/-- **Corollary 5.3 (few leaves), round part.** If every derivable fact has a derivation tree
with at most `L` leaves, then `⌊log₂ L⌋ + 1` rounds of Strahler saturation compute the set of
all derivable facts. -/
theorem saturate_eq_derivable_of_leaves {L : ℕ}
    (hL : ∀ q (_ : Deriv H q), ∃ T' : Deriv H q, T'.leaves ≤ L) :
    saturate H (Nat.log 2 L + 1) = {q | Nonempty (Deriv H q)} := by
  sorry

end GC.NewtonStrahler

namespace GC.NewtonStrahler

/-- A gate of a Boolean circuit of fan-in at most two with fixed inputs. -/
inductive BGate (n : ℕ) where
  | input (b : Bool)
  | unary (φ : Bool → Bool) (g₁ : Fin n)
  | binary (φ : Bool → Bool → Bool) (g₁ g₂ : Fin n)

/-- Well-formedness: inputs of gate `i` precede `i`, and the two inputs of a binary gate are
distinct. -/
def BGate.WF {n : ℕ} (i : Fin n) : BGate n → Prop
  | .input _ => True
  | .unary _ g₁ => g₁ < i
  | .binary _ g₁ g₂ => g₁ < i ∧ g₂ < i ∧ g₁ ≠ g₂

/-- A Boolean circuit of fan-in at most two with fixed inputs. -/
structure BCircuit (n : ℕ) where
  gate : Fin n → BGate n
  wf : ∀ i, (gate i).WF i

/-- The value of a gate given the values of all gates. -/
def BGate.eval {n : ℕ} : BGate n → (Fin n → Bool) → Bool
  | .input b, _ => b
  | .unary φ g₁, v => φ (v g₁)
  | .binary φ g₁ g₂, v => φ (v g₁) (v g₂)

variable {n : ℕ}

/-- `v` is the value vector of the circuit. -/
def BCircuit.IsValue (C : BCircuit n) (v : Fin n → Bool) : Prop :=
  ∀ i, v i = (C.gate i).eval v

/-- The depth of a gate: `0` for an input, one more than the largest depth of an input of the
gate otherwise. -/
def BCircuit.depth (C : BCircuit n) (i : Fin n) : ℕ :=
  match _h : C.gate i with
  | .input _ => 0
  | .unary _ g₁ => C.depth g₁ + 1
  | .binary _ g₁ g₂ => max (C.depth g₁) (C.depth g₂) + 1
termination_by i.val
decreasing_by
  all_goals
    have hw := C.wf i
    rw [_h] at hw
    simp only [BGate.WF] at hw
  · exact hw
  · exact hw.1
  · exact hw.2.1

/-- The rules of the truth-table system contributed by gate `g`. -/
def BCircuit.gateRules (C : BCircuit n) (g : Fin n) : List (Rule (Fin n × Bool)) :=
  match C.gate g with
  | .input _ => []
  | .unary φ g₁ => [false, true].map fun b₁ => ⟨{(g₁, b₁)}, (g, φ b₁)⟩
  | .binary φ g₁ g₂ =>
      [(false, false), (false, true), (true, false), (true, true)].map fun b =>
        ⟨{(g₁, b.1), (g₂, b.2)}, (g, φ b.1 b.2)⟩

/-- The truth-table Horn system (Lemma 7.2): facts `Val(g, b) = (g, b)`, axioms `Val(g, b)` for
input gates of value `b`, and for every gate and every pair of input values the rule
`{Val(g₁, b₁), Val(g₂, b₂)} ⇒ Val(g, φ_g(b₁, b₂))` (one premise for gates of fan-in one). -/
def BCircuit.truthTable (C : BCircuit n) : HornSystem (Fin n × Bool) where
  axioms := {f | C.gate f.1 = .input f.2}
  rules := (List.finRange n).flatMap C.gateRules

/-- **Lemma 7.2 (truth-table systems).** `Val(g, b)` is derivable if and only if `b` is the value
of `g`, and the true fact `Val(g, v g)` has proof rank at most the depth of `g`. -/
theorem BCircuit.truthTable_spec {C : BCircuit n} {v : Fin n → Bool} (hv : C.IsValue v)
    (g : Fin n) (b : Bool) :
    (Nonempty (Deriv C.truthTable (g, b)) ↔ b = v g) ∧
      (g, v g) ∈ rankLayer C.truthTable (C.depth g) := by
  sorry

end GC.NewtonStrahler
