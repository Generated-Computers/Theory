import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Powerset
import Mathlib.Logic.Relation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators

namespace GC.StructuralCompilers

/-- A tagged absorbing system (Definition 2.1): vertices `0, 1, 2, …`, each with a finite set of
earlier predecessors, a tag (exception or regular) and a constant `Y_v`. The exception truth
tables play no role in Lemma 2.2, whose statement holds for arbitrary exception values. -/
structure TaggedSystem where
  /-- `Pred(v)` -/
  pred : ℕ → Finset ℕ
  /-- predecessors are earlier vertices -/
  pred_lt : ∀ v, ∀ u ∈ pred v, u < v
  /-- the exception tag -/
  isExc : ℕ → Prop
  /-- the constants `Y_v` of the regular vertices -/
  Y : ℕ → Bool

/-- The regular rule: `V_v = Y_v` if `Pred(v) = ∅`, and `V_v = Y_v ∨ ⋀_{u ∈ Pred(v)} V_u`
otherwise. -/
def TaggedSystem.RegularRule (T : TaggedSystem) (V : ℕ → Bool) : Prop :=
  ∀ v, ¬ T.isExc v →
    (V v = true ↔ (T.Y v = true ∨ (T.pred v ≠ ∅ ∧ ∀ u ∈ T.pred v, V u = true)))

/-- The digraph `Γ` on the vertices and a new vertex `s` (encoded as `none`). -/
def TaggedSystem.arc (T : TaggedSystem) : Option ℕ → Option ℕ → Prop
  | none, some v => ¬ T.isExc v ∧ T.pred v = ∅ ∧ T.Y v = false
  | some u, some v => ¬ T.isExc v ∧ T.pred v ≠ ∅ ∧ T.Y v = false ∧ u ∈ T.pred v
  | _, none => False

/-- `Reach(y, v)`: a directed path of `Γ` from `y` to `v`. -/
def TaggedSystem.Reach (T : TaggedSystem) (y : Option ℕ) (v : ℕ) : Prop :=
  Relation.TransGen T.arc y (some v)

/-- **Lemma 2.2 (absorbing elimination).** For every regular vertex `v`,
`W_v = Reach(s, v) ∨ ⋁_{q ∈ Exc} (Reach(q, v) ∧ W_q)`, where `W = 1 - V`. -/
theorem absorbing_elimination (T : TaggedSystem) (V : ℕ → Bool) (hV : T.RegularRule V) :
    ∀ v, ¬ T.isExc v →
      (V v = false ↔ T.Reach none v ∨ ∃ q, T.isExc q ∧ T.Reach (some q) v ∧ V q = false) := by
  sorry

/-- An exception-port system (Definition 2.4) with at most `a` ports per exception (unused ports
are ignored by the truth table): port `i` of exception `e` has a constant `c e i` and a set
`B e i` of earlier exceptions; `g e` is the truth table of `e`. Here `W` (the complemented
exception value) is the computed quantity. -/
structure PortSystem (a : ℕ) where
  /-- the constants `c_p` -/
  c : ℕ → Fin a → Bool
  /-- the sets `B_p` -/
  B : ℕ → Fin a → Finset ℕ
  /-- `B_p ⊆ {0, …, e-1}` -/
  B_lt : ∀ e i, ∀ q ∈ B e i, q < e
  /-- the truth tables `g_e` -/
  g : ℕ → (Fin a → Bool) → Bool

variable {a : ℕ}

/-- The values of an exception-port system: `x_p = c_p ∨ ⋁_{q ∈ B_p} W_q`,
`W_e = g_e((x_p)_p)`, in increasing order of `e`. -/
def PortSystem.W (P : PortSystem a) (e : ℕ) : Bool :=
  P.g e (fun i => P.c e i || decide (∃ q ∈ (P.B e i).attach, P.W q.1 = true))
termination_by e
decreasing_by all_goals exact P.B_lt _ _ _ (Finset.coe_mem _)

/-- The local run of an interval starting at `l` on an input vector `α` (indexed by ports):
`x_p = c_p ∨ α_p ∨ ⋁_{q ∈ B_p ∩ [l, e)} W'_q`, `W'_e = g_e((x_p)_p)`. -/
def PortSystem.run (P : PortSystem a) (l : ℕ) (α : ℕ → Fin a → Bool) (e : ℕ) : Bool :=
  P.g e (fun i => P.c e i || α e i ||
    decide (∃ q ∈ (P.B e i).attach, l ≤ q.1 ∧ P.run l α q.1 = true))
termination_by e
decreasing_by all_goals exact P.B_lt _ _ _ (Finset.coe_mem _)

/-- The union of the incidence columns of a set `S` of exceptions: `p ↦ ⋁_{q ∈ S} [q ∈ B_p]`. -/
noncomputable def PortSystem.unionVec (P : PortSystem a) (S : Set ℕ) : ℕ → Fin a → Bool :=
  fun e i => by classical exact decide (∃ q ∈ P.B e i, q ∈ S)

/-- Restriction of a port vector to the ports owned by exceptions in `[l, r)` (other entries
are set to `0`). -/
def restrictTo (l r : ℕ) (α : ℕ → Fin a → Bool) : ℕ → Fin a → Bool :=
  fun e i => decide (l ≤ e ∧ e < r) && α e i

/-- Restriction to the ports owned by exceptions `e ≥ r` (the ports after `[l, r)`). -/
def restrictAfter (r : ℕ) (α : ℕ → Fin a → Bool) : ℕ → Fin a → Bool :=
  fun e i => decide (r ≤ e) && α e i

/-- The union closure `𝒰(A^in_I)` of the node `I = [l, r)`: rows are the ports of `I`, columns
the exceptions `q < l`. -/
def PortSystem.closureIn (P : PortSystem a) (l r : ℕ) : Set (ℕ → Fin a → Bool) :=
  {α | ∃ S : Set ℕ, (∀ q ∈ S, q < l) ∧ α = restrictTo l r (P.unionVec S)}

/-- The union closure `𝒰(A^out_I)`: rows are the ports after `I`, columns the exceptions in
`I`. -/
def PortSystem.closureOut (P : PortSystem a) (l r : ℕ) : Set (ℕ → Fin a → Bool) :=
  {β | ∃ S : Set ℕ, (∀ q ∈ S, l ≤ q ∧ q < r) ∧ β = restrictAfter r (P.unionVec S)}

/-- The response `ρ_I(α) = ⋁_{q ∈ I, W'_q = 1} a_q(A^out_I)`. -/
noncomputable def PortSystem.response (P : PortSystem a) (l r : ℕ) (α : ℕ → Fin a → Bool) :
    ℕ → Fin a → Bool :=
  restrictAfter r (P.unionVec {q | l ≤ q ∧ q < r ∧ P.run l α q = true})

/-- **Lemma 3.2 (composition).** Let `I = [l, r)` have children `L = [l, t)` and `R' = [t, r)`,
let `α ∈ 𝒰(A^in_I)`, `α_L = α|_L`, `u_L = ρ_L(α_L)`, `α_{R'} = (α ∨ u_L)|_{R'}`,
`u_{R'} = ρ_{R'}(α_{R'})`. Then `α_L ∈ 𝒰(A^in_L)`, `α_{R'} ∈ 𝒰(A^in_{R'})`, the local runs of
`L` and `R'` produce the values of the local run of `I`, and
`ρ_I(α) = u_L|_{after I} ∨ u_{R'}`. -/
theorem profile_composition (P : PortSystem a) (l t r : ℕ) (hlt : l ≤ t) (htr : t ≤ r)
    (α : ℕ → Fin a → Bool) (hα : α ∈ P.closureIn l r) :
    let αL := restrictTo l t α
    let uL := P.response l t αL
    let αR := restrictTo t r (fun e i => α e i || uL e i)
    let uR := P.response t r αR
    αL ∈ P.closureIn l t ∧ αR ∈ P.closureIn t r ∧
    (∀ e, l ≤ e → e < t → P.run l α e = P.run l αL e) ∧
    (∀ e, t ≤ e → e < r → P.run l α e = P.run t αR e) ∧
    P.response l r α = fun e i => restrictAfter r uL e i || uR e i := by
  sorry

/-- At the root, the local run on the zero vector is the true computation. -/
theorem localRun_root (P : PortSystem a) (e : ℕ) : P.run 0 (fun _ _ => false) e = P.W e := by
  sorry

/-- The true contribution vector at a node `[l, r)` lies in `𝒰(A^in_{[l,r)})`, and the local
run of `[l, r)` on it produces the true values `W_e`, `l ≤ e < r`. -/
theorem localRun_trueProfile (P : PortSystem a) (l r : ℕ) :
    restrictTo l r (P.unionVec {q | q < l ∧ P.W q = true}) ∈ P.closureIn l r ∧
    ∀ e, l ≤ e → e < r →
      P.run l (restrictTo l r (P.unionVec {q | q < l ∧ P.W q = true})) e = P.W e := by
  sorry

section Closure

variable {ρ κ : Type*} [Fintype ρ] [Fintype κ] [DecidableEq κ]

/-- The union of the columns `q ∈ S` of a Boolean matrix `A` (rows `ρ`, columns `κ`). -/
def unionOf (A : ρ → κ → Bool) (S : Finset κ) : ρ → Bool :=
  fun r => decide (∃ q ∈ S, A r q = true)

/-- The union closure `𝒰(A) = {⋁_{q ∈ S} a_q : S ⊆ cols(A)}`. -/
def unionClosure (A : ρ → κ → Bool) : Finset (ρ → Bool) :=
  (Finset.univ : Finset (Finset κ)).image (unionOf A)

omit [DecidableEq κ] in
/-- **Proposition 4.1 (1).** If `A` has at most `K` distinct rows, `|𝒰(A)| ≤ 2^K`. -/
theorem unionClosure_card_le_rows (A : ρ → κ → Bool) (K : ℕ)
    (hK : ((Finset.univ : Finset ρ).image A).card ≤ K) : (unionClosure A).card ≤ 2 ^ K := by
  sorry

omit [DecidableEq κ] in
/-- **Proposition 4.1 (2).** If `A` has at most `K` distinct columns, `|𝒰(A)| ≤ 2^K`. -/
theorem unionClosure_card_le_cols (A : ρ → κ → Bool) (K : ℕ)
    (hK : ((Finset.univ : Finset κ).image (fun q r => A r q)).card ≤ K) :
    (unionClosure A).card ≤ 2 ^ K := by
  sorry

/-- **Proposition 4.1 (3).** If every row of `A` has at most `d` zeros, then
`|𝒰(A)| ≤ 1 + ∑_{i=0}^{d} (c choose i)`, `c` the number of columns. -/
theorem unionClosure_card_le_zeros (A : ρ → κ → Bool) (d : ℕ)
    (hd : ∀ r, ((Finset.univ : Finset κ).filter (fun q => A r q = false)).card ≤ d) :
    (unionClosure A).card ≤ 1 + ∑ i ∈ Finset.range (d + 1), (Fintype.card κ).choose i := by
  sorry

end Closure

/-- **Example 4.3 (matching).** The union closure of the `w × w` identity matrix has all `2^w`
vectors. -/
theorem matching_unionClosure_card (w : ℕ) :
    (unionClosure (fun r q : Fin w => decide (r = q))).card = 2 ^ w := by
  sorry

end GC.StructuralCompilers
