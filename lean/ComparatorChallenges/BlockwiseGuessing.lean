import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fintype.Pi

/-! Comparator challenge for manuscript 006e (Blockwise Guessing Puts Low-Defect Sequential NOR in NC). -/


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
# 006e: blockwise causal recovery of the bad-shield values

Bad shields `H(j) = {h ∈ [1, n-1] : j_h ≠ 0, 1 ≤ j_{h+1} ≤ h - 1}` with ranks
`1, …, b`. For an assignment `γ` (indexed by rank) the candidate `Y(γ)` sets `y_0 = 1`,
`y_{h_k} = γ_k` and `y_q = NOR(y_{q-1}, y_{j_q})` elsewhere. Stage `s` (with `a = s g`)
tries all `2^g` branches `α` for the ranks `a+1, …, a+g`, keeps the valid ones (padding bits
`0`, deferred equations satisfied) and outputs `β_{a+t} = ⋁_α (V_α ∧ α_t)`.

The circuit size/depth bounds are not formalized; we formalize the correctness of this
explicitly defined schedule, including its number of stages `⌈r/g⌉`.
-/

namespace GC.SeqNORNormalForms

/-- `h` is a bad shield of the parent array `j` of length `n`. -/
def IsBad (n : ℕ) (j : ℕ → ℕ) (h : ℕ) : Prop :=
  1 ≤ h ∧ h + 1 ≤ n ∧ j h ≠ 0 ∧ 1 ≤ j (h + 1) ∧ j (h + 1) + 1 ≤ h

instance (n : ℕ) (j : ℕ → ℕ) (h : ℕ) : Decidable (IsBad n j h) := by
  unfold IsBad; infer_instance

/-- `badRank q = |H(j) ∩ [1, q]|`; the rank of a bad shield `h` is `badRank h`. -/
def badRank (n : ℕ) (j : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | q + 1 => badRank n j q + if IsBad n j (q + 1) then 1 else 0

/-- `b = |H(j)|`. -/
def numBad (n : ℕ) (j : ℕ → ℕ) : ℕ := badRank n j n

/-- The candidate `Y(γ)` for an assignment `γ` indexed by rank (Section 3 of 006e). -/
def cand (n : ℕ) (j : ℕ → ℕ) (γ : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | q + 1 =>
      if IsBad n j (q + 1) then γ (badRank n j (q + 1))
      else nor (cand n j γ q) (if h : j (q + 1) < q + 1 then cand n j γ (j (q + 1)) else true)
termination_by q => q

/-- The assignment `γ^{s,α}` of stage `s` (Section 5 of 006e), with `a = s g`. -/
def branchAssign (β : ℕ → Bool) (a g : ℕ) (α : Fin g → Bool) (k : ℕ) : Bool :=
  if h1 : k ≤ a then β k
  else if h2 : k ≤ a + g then α ⟨k - a - 1, by omega⟩
  else false

/-- The validity bit `V_{s,α}`: padding bits are `0` and the deferred equations of the
ranks `a+1, …, min(a+g, b)` hold (Section 5 of 006e). -/
def BranchValid (n : ℕ) (j : ℕ → ℕ) (β : ℕ → Bool) (a g : ℕ) (α : Fin g → Bool) : Prop :=
  (∀ t : Fin g, numBad n j < a + t.val + 1 → α t = false) ∧
  (∀ h, IsBad n j h → a < badRank n j h → badRank n j h ≤ a + g →
    branchAssign β a g α (badRank n j h) =
      nor (cand n j (branchAssign β a g α) (h - 1)) (cand n j (branchAssign β a g α) (j h)))

open Classical in
/-- Stage `s` of the blockwise compiler: `β_{a+t} = ⋁_α (V_{s,α} ∧ α_t)`. -/
noncomputable def stage (n : ℕ) (j : ℕ → ℕ) (g s : ℕ) (β : ℕ → Bool) : ℕ → Bool := fun k =>
  if h1 : k ≤ s * g then β k
  else if h : k ≤ s * g + g then
    decide (∃ α : Fin g → Bool, BranchValid n j β (s * g) g α ∧ α ⟨k - s * g - 1, by omega⟩ = true)
  else false

/-- The bits after `s` stages, starting from all zeros. -/
noncomputable def recover (n : ℕ) (j : ℕ → ℕ) (g : ℕ) : ℕ → ℕ → Bool
  | 0 => fun _ => false
  | s + 1 => stage n j g s (recover n j g s)

section

variable (n : ℕ) (j : ℕ → ℕ)

/-- **Corollary 4.2 of 006e (true-prefix recovery).** If `γ` gives the true value to every bad
shield `h ≤ t`, then `Y(γ)` agrees with the trace on `0, …, t`. -/
theorem cand_true_prefix (hj : IsParentArray n j) (γ : ℕ → Bool) (t : ℕ)
    (hγ : ∀ h, IsBad n j h → h ≤ t → γ (badRank n j h) = trace j h) :
    ∀ q, q ≤ t → q ≤ n → cand n j γ q = trace j q := by
  sorry

/-- **Lemma 4.1 of 006e (prefix locality).** If `γ` and `γ'` agree on the ranks of the bad
shields `≤ t`, then `Y(γ)` and `Y(γ')` agree on `0, …, t`. -/
theorem cand_prefix_locality (hj : IsParentArray n j) (γ γ' : ℕ → Bool) (t : ℕ)
    (hγ : ∀ h, IsBad n j h → h ≤ t → γ (badRank n j h) = γ' (badRank n j h)) :
    ∀ q, q ≤ t → q ≤ n → cand n j γ q = cand n j γ' q := by
  sorry

/-- The invariant before a stage with `a = s g`: `β` is correct on the ranks `≤ a` and `0`
on the padding ranks `b < k ≤ a`. -/
def StageInv (β : ℕ → Bool) (a : ℕ) : Prop :=
  (∀ h, IsBad n j h → badRank n j h ≤ a → β (badRank n j h) = trace j h) ∧
  (∀ k, numBad n j < k → k ≤ a → β k = false)

open Classical in
/-- The true branch: `α⋆_t = x_{h_{a+t+1}}` if that rank exists, `0` otherwise. -/
noncomputable def trueBranch (a g : ℕ) (t : Fin g) : Bool :=
  decide (∃ h, IsBad n j h ∧ badRank n j h = a + t.val + 1 ∧ trace j h = true)

/-- **Lemma 5.1 of 006e (unique valid branch).** Under the invariant, the valid branches of
stage `s` are exactly the true branch. -/
theorem unique_valid_branch (hj : IsParentArray n j) (β : ℕ → Bool) (a g : ℕ)
    (hinv : StageInv n j β a) (α : Fin g → Bool) :
    BranchValid n j β a g α ↔ α = trueBranch n j a g := by
  sorry

/-- **Theorem 5.2 of 006e (blockwise causal compiler), correctness.** On the promise
`|H(j)| ≤ r`, with block width `g ≥ 1`, after `T = ⌈r/g⌉` stages the recovered bits are the
true values of all bad shields, and the candidate `Y(β)` is the trace of `j`. -/
theorem blockwise_correct (hj : IsParentArray n j) (g r : ℕ) (hg : 1 ≤ g)
    (hr : numBad n j ≤ r) :
    let β := recover n j g ((r + g - 1) / g)
    (∀ h, IsBad n j h → β (badRank n j h) = trace j h) ∧
    ∀ q, q ≤ n → cand n j β q = trace j q := by
  sorry

end

end GC.SeqNORNormalForms
