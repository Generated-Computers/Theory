import GC.Computability.Portals.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Interval.Finset.Nat

/-!
# Batching first failures cannot beat one prefix (manuscript 005g)

* `LocalMachine`, `first_failure_validator`: Lemma "First-failure validator". For a step function
  whose value at step `t` depends only on the configurations before `t`, the least `t > g` at
  which a candidate fails the local check is its first-failure boundary `τ(Z)`, and the step
  function applied to the candidate there yields the exact configuration `C_{τ(Z)}`.
* `batch_collapse`: Theorem "Same-anchor batch collapse": the steps certified by validating a
  finite family of candidates from the same boundary `g` (the exact prefixes through
  `min(τ(Z), N)`) form the prefix certified by the candidate with the largest `τ`.
* `blackbox_one_round`: Theorem "Black-box two-round barrier": no one-round algorithm with fewer
  than `|Y|` non-adaptive queries computes `R(L(x))` for all oracles `L : X → Y`,
  `R : Y → Bool`.
* The round bound of Theorem "Low-junction transducer" is the generic `rounds_bound` of the file
  `FanoutHeight`, applied with `H` the set of junctions.

Not formalized: the depth and work bounds, the parametric cut composition (a statement about
depth only) and its conditional corollary.
-/

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
  have hagree : ∀ t, t < t₀ → Z t = E t := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro ht
      by_cases htg : t ≤ g
      · exact hpre t htg
      · rw [hok t (by omega) ht, hE t (by omega)]
        exact M.isLocal t Z E (fun s hs => ih s hs (by omega))
  have hstep : M.step t₀ Z = E t₀ := by
    rw [hE t₀ (by omega)]
    exact M.isLocal t₀ Z E (fun s hs => hagree s hs)
  refine ⟨⟨hg, hN, fun t _ ht => hagree t ht, fun h => ?_⟩, fun _ => hstep⟩
  rw [← hstep]
  exact hfail h

/-- Theorem (same-anchor batch collapse). For a nonempty finite family of candidates from the
boundary `g` with first-failure boundaries `τ i`, the steps certified by validating all of them
are exactly the steps certified by a single candidate attaining the maximum. -/
theorem batch_collapse {ι : Type*} (F : Finset ι) (hF : F.Nonempty) (τ : ι → ℕ) (g N : ℕ) :
    ∃ i ∈ F, (∀ k ∈ F, τ k ≤ τ i) ∧
      F.biUnion (fun k => Finset.Ioc g (min (τ k) N)) = Finset.Ioc g (min (τ i) N) := by
  obtain ⟨i, hi, hmax⟩ := F.exists_max_image τ hF
  refine ⟨i, hi, hmax, ?_⟩
  apply Finset.Subset.antisymm
  · intro t ht
    obtain ⟨k, hk, htk⟩ := Finset.mem_biUnion.mp ht
    simp only [Finset.mem_Ioc] at htk ⊢
    have := hmax k hk
    omega
  · exact Finset.subset_biUnion_of_mem (fun k => Finset.Ioc g (min (τ k) N)) hi

/-- Theorem (black-box two-round barrier). A one-round algorithm fixes in advance the points
`QL ⊆ X` at which it queries `L` and `QR ⊆ Y` at which it queries `R`, and outputs a function of
the answers. If it makes at most `q < |Y|` queries, some pair of oracles defeats it. -/
theorem blackbox_one_round {X Y : Type*} [Fintype Y] [DecidableEq Y] (x : X) (q : ℕ)
    (hq : q < Fintype.card Y) (QL : Finset X) (QR : Finset Y) (hQ : QL.card + QR.card ≤ q)
    (out : (QL → Y) → (QR → Bool) → Bool) :
    ∃ (L : X → Y) (R : Y → Bool), out (fun i => L i) (fun j => R j) ≠ R (L x) := by
  obtain ⟨y, hy⟩ : ∃ y, y ∉ QR := by
    by_contra h
    simp only [not_exists, not_not] at h
    have : Finset.univ ⊆ QR := fun y _ => h y
    have := Finset.card_le_card this
    rw [Finset.card_univ] at this
    omega
  have hsame : (fun j : QR => decide ((j : Y) = y)) = (fun _ => false) := by
    funext j
    simp only [decide_eq_false_iff_not]
    exact fun h => hy (h ▸ j.2)
  by_cases hout : out (fun _ => y) (fun _ => false) = true
  · exact ⟨fun _ => y, fun _ => false, by simp [hout]⟩
  · refine ⟨fun _ => y, fun z => decide (z = y), ?_⟩
    simp only [decide_true]
    rw [hsame]
    simpa using hout

end GC.Portals
