import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Cases
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Fintype.Card


namespace GC.Portals

/-- A deterministic machine with a local step function: the configuration at step `t` is
determined by the configurations at the steps before `t`. -/
structure LocalMachine (C : Type*) where
  step : ℕ → (ℕ → C) → C
  isLocal : ∀ t (c c' : ℕ → C), (∀ s < t, c s = c' s) → step t c = step t c'

/-- `τ` is the first-failure boundary of the candidate `Z` from the exact boundary `g` (with
`τ = N + 1` if `Z` is correct through `N`). -/
def IsFirstFailure {C : Type*} (E Z : ℕ → C) (g N τ : ℕ) : Prop :=
  g < τ ∧ τ ≤ N + 1 ∧ (∀ t, g < t → t < τ → Z t = E t) ∧ (τ ≤ N → Z τ ≠ E τ)

/-- Lemma (first-failure validator). Let `E` be the exact execution (`E t = step t E` for
`t ≥ 1`), let the candidate `Z` agree with `E` through the exact boundary `g`, and let `t₀` be the
least `t ∈ (g, N]` at which the local check `Z t = step t Z` fails (`t₀ = N + 1` if none fails).
Then `t₀ = τ(Z)`, and if `t₀ ≤ N` the computed successor `step t₀ Z` is the exact `E t₀`. -/
theorem first_failure_validator {C : Type*} (M : LocalMachine C) (E Z : ℕ → C) (g N t₀ : ℕ)
    (hE : ∀ t, 1 ≤ t → E t = M.step t E) (hpre : ∀ t ≤ g, Z t = E t)
    (hg : g < t₀) (hN : t₀ ≤ N + 1)
    (hok : ∀ t, g < t → t < t₀ → Z t = M.step t Z) (hfail : t₀ ≤ N → Z t₀ ≠ M.step t₀ Z) :
    IsFirstFailure E Z g N t₀ ∧ (t₀ ≤ N → M.step t₀ Z = E t₀) := by
  sorry

/-- Theorem (same-anchor batch collapse). For a nonempty finite family of candidates from the
boundary `g` with first-failure boundaries `τ i`, the steps certified by validating all of them
are exactly the steps certified by a single candidate attaining the maximum. -/
theorem batch_collapse {ι : Type*} (F : Finset ι) (hF : F.Nonempty) (τ : ι → ℕ) (g N : ℕ) :
    ∃ i ∈ F, (∀ k ∈ F, τ k ≤ τ i) ∧
      F.biUnion (fun k => Finset.Ioc g (min (τ k) N)) = Finset.Ioc g (min (τ i) N) := by
  sorry

/-- Theorem (black-box two-round barrier). A one-round algorithm fixes in advance the points
`QL ⊆ X` at which it queries `L` and `QR ⊆ Y` at which it queries `R`, and outputs a function of
the answers. If it makes at most `q < |Y|` queries, some pair of oracles defeats it. -/
theorem blackbox_one_round {X Y : Type*} [Fintype Y] [DecidableEq Y] (x : X) (q : ℕ)
    (hq : q < Fintype.card Y) (QL : Finset X) (QR : Finset Y) (hQ : QL.card + QR.card ≤ q)
    (out : (QL → Y) → (QR → Bool) → Bool) :
    ∃ (L : X → Y) (R : Y → Bool), out (fun i => L i) (fun j => R j) ≠ R (L x) := by
  sorry

end GC.Portals
