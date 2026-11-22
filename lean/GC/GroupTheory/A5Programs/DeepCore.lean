import GC.GroupTheory.A5Programs.TwoGen
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Group.Commutator

/-!
# P-complete `A₅` circuits invisible to solvable groups (manuscript 004b)

* `exists_commutator_A5`: every element of `A₅` is a commutator (Ore), with an explicit table.
* `tower_spec`: the commutator representatives `R g d` lie in the `d`-th derived subgroup of the
  free group `F = F(P, Q)` and evaluate to `g` (Theorem 4.2 (i), (ii)).
* `deep_reduction`: substituting `R g d` for the constants of an `A₅` circuit keeps all values and
  puts every node into `F^(d)` (Theorem 5.1, semantic part).
* `derivedSeries_le_lowerCentralSeries_two_pow`: `G^(d) ≤ γ_{2^d}(G)` (Lemma 2.1).
* `shadow_solvable`, `shadow_nilpotent`, `derivedSeries_eq_bot_of_card_lt`: homomorphisms to
  solvable groups of derived length `≤ d`, to nilpotent groups of class `< 2^d`, and to finite
  solvable groups of order `< 2^d` kill `F^(d)` (Theorem 6.1, Corollary 6.2, Remark 6.3(1)).
-/

namespace GC.A5Programs

open Equiv
open scoped commutatorElement

/-- The free group on the terminals `P, Q`. -/
abbrev F2 := FreeGroup (Fin 2)

/-- Evaluation `P ↦ p`, `Q ↦ q`. -/
def ev : F2 →* Perm (Fin 5) := FreeGroup.lift pq

/-! ## Every element of `A₅` is a commutator -/

/-- Positions in `A5list` of a first commutator factor of each element. -/
def commTabA : List ℕ := [1, 3, 3, 1, 0, 0, 3, 5, 3, 7, 6, 2, 1, 5, 1, 7, 6, 7, 1, 1, 3, 10, 2, 1,
  5, 0, 1, 3, 5, 3, 8, 1, 0, 0, 1, 2, 0, 0, 1, 0, 1, 2, 1, 7, 0, 1, 2, 1, 0, 2, 0, 0, 2, 10, 7, 7,
  1, 1, 10, 7]
/-- Positions in `A5list` of a second commutator factor of each element. -/
def commTabB : List ℕ := [41, 53, 48, 53, 0, 55, 24, 31, 5, 45, 7, 55, 24, 36, 11, 29, 5, 39, 8,
  5, 13, 18, 10, 48, 6, 36, 9, 11, 10, 14, 6, 17, 22, 7, 20, 36, 35, 1, 44, 3, 42, 23, 0, 10, 10,
  29, 1, 14, 23, 7, 6, 31, 22, 33, 22, 15, 18, 26, 20, 13]

/-- `α(g)` with `⁅α(g), β(g)⁆ = g`. -/
def alphaC (g : Perm (Fin 5)) : Perm (Fin 5) := A5list.getD (commTabA.getD (libIdx g) 0) 1
/-- `β(g)` with `⁅α(g), β(g)⁆ = g`. -/
def betaC (g : Perm (Fin 5)) : Perm (Fin 5) := A5list.getD (commTabB.getD (libIdx g) 0) 1

set_option maxRecDepth 100000 in
theorem commTab_spec : ∀ i < 60,
    ⁅A5list.getD (commTabA.getD i 0) 1, A5list.getD (commTabB.getD i 0) 1⁆ = A5list.getD i 1 ∧
      commTabA.getD i 0 < 60 ∧ commTabB.getD i 0 < 60 := by
  decide +kernel

theorem getD_A5list_mem {i : ℕ} (hi : i < 60) : A5list.getD i 1 ∈ alternatingGroup (Fin 5) := by
  rw [← mem_A5list_iff, List.getD_eq_getElem _ _ (by rw [A5list_length]; exact hi)]
  exact List.getElem_mem _

theorem getD_A5list_libIdx {g : Perm (Fin 5)} (hg : g ∈ alternatingGroup (Fin 5)) :
    A5list.getD (libIdx g) 1 = g := by
  have hm := (mem_A5list_iff g).2 hg
  rw [libIdx, List.getD_eq_getElem _ _ (List.idxOf_lt_length_of_mem hm)]
  exact List.getElem_idxOf _

theorem alphaC_betaC {g : Perm (Fin 5)} (hg : g ∈ alternatingGroup (Fin 5)) :
    ⁅alphaC g, betaC g⁆ = g ∧ alphaC g ∈ alternatingGroup (Fin 5) ∧
      betaC g ∈ alternatingGroup (Fin 5) := by
  obtain ⟨h1, h2, h3⟩ := commTab_spec _ (libIdx_lt hg)
  refine ⟨?_, getD_A5list_mem h2, getD_A5list_mem h3⟩
  rw [alphaC, betaC, h1, getD_A5list_libIdx hg]

/-- Every element of `A₅` is a commutator of two elements of `A₅` (Ore; 004b, Section 4). -/
theorem exists_commutator_A5 (g : Perm (Fin 5)) (hg : g ∈ alternatingGroup (Fin 5)) :
    ∃ x ∈ alternatingGroup (Fin 5), ∃ y ∈ alternatingGroup (Fin 5), ⁅x, y⁆ = g :=
  ⟨_, (alphaC_betaC hg).2.1, _, (alphaC_betaC hg).2.2, (alphaC_betaC hg).1⟩

/-! ## The shared commutator tower -/

/-- The library word `ω_g` (the formal word of the library node of `g`). -/
def omegaWord (g : Perm (Fin 5)) : F2 := val FreeGroup.of libOps (libIdx g)

/-- Commutator representatives: `R g 0 = ω_g`, `R g (d+1) = ⁅R (α g) d, R (β g) d⁆`. -/
def towerR : Perm (Fin 5) → ℕ → F2
  | g, 0 => omegaWord g
  | g, d + 1 => ⁅towerR (alphaC g) d, towerR (betaC g) d⁆

theorem ev_comp_of : ⇑ev ∘ (FreeGroup.of : Fin 2 → F2) = pq := by
  funext i; simp [ev]

theorem ev_omegaWord {g : Perm (Fin 5)} (hg : g ∈ alternatingGroup (Fin 5)) :
    ev (omegaWord g) = g := by
  rw [omegaWord, map_val ev, ev_comp_of, val_libOps_libIdx hg]

/-- **Shared tower** (004b, Theorem 4.2 (i), (ii)): for every `g ∈ A₅` and `d`,
`R g d` evaluates to `g` and lies in the `d`-th derived subgroup of `F(P, Q)`. -/
theorem tower_spec (d : ℕ) : ∀ g ∈ alternatingGroup (Fin 5),
    ev (towerR g d) = g ∧ towerR g d ∈ derivedSeries F2 d := by
  induction d with
  | zero => intro g hg; exact ⟨ev_omegaWord hg, by simp⟩
  | succ d ih =>
    intro g hg
    obtain ⟨hc, ha, hb⟩ := alphaC_betaC hg
    obtain ⟨ha1, ha2⟩ := ih _ ha
    obtain ⟨hb1, hb2⟩ := ih _ hb
    refine ⟨?_, ?_⟩
    · rw [towerR, map_commutatorElement, ha1, hb1, hc]
    · rw [towerR, derivedSeries_succ]
      exact Subgroup.commutator_mem_commutator ha2 hb2

/-- **Deep perfect reduction** (004b, Theorem 5.1, semantic part). Evaluate an `A₅` circuit `C`
(constants in `A₅`) in the free group with every constant `g` replaced by its representative
`R g d`. Then every node has formal word in `F^(d)`, and its value is the value of the same node
of `C`. -/
theorem deep_reduction (C : List (Op (Perm (Fin 5)))) (hC : ConstsInA5 C) (d k : ℕ) :
    val (fun g => towerR g d) C k ∈ derivedSeries F2 d ∧
      ev (val (fun g => towerR g d) C k) = val id C k := by
  refine ⟨val_mem_of_leaves _ _ _ (fun g hg => (tower_spec d g (hC g hg)).2) k, ?_⟩
  rw [map_val ev]
  exact val_congr_leaves _ _ _ (fun g hg => (tower_spec d g (hC g hg)).1) k

/-! ## Derived series versus lower central series -/

section Series

variable {G : Type*} [Group G]

/-- The three subgroup lemma modulo a normal subgroup. -/
theorem commutator_commutator_le_of_rotate (N : Subgroup G) [N.Normal] {A B C : Subgroup G}
    (h1 : ⁅⁅B, C⁆, A⁆ ≤ N) (h2 : ⁅⁅C, A⁆, B⁆ ≤ N) : ⁅⁅A, B⁆, C⁆ ≤ N := by
  let f := QuotientGroup.mk' N
  have key : ∀ X : Subgroup G, X ≤ N ↔ X.map f = ⊥ := by
    intro X; rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  rw [key, Subgroup.map_commutator, Subgroup.map_commutator]
  rw [key, Subgroup.map_commutator, Subgroup.map_commutator] at h1 h2
  exact Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2

/-- `[γ_{i+1}, γ_{j+1}] ≤ γ_{i+j+2}`; Mathlib's `(⊤ : Subgroup G).lowerCentralSeries n` is
`γ_{n+1}(G)`. -/
theorem commutator_lowerCentralSeries_le (i j : ℕ) :
    ⁅(⊤ : Subgroup G).lowerCentralSeries i, (⊤ : Subgroup G).lowerCentralSeries j⁆ ≤
      (⊤ : Subgroup G).lowerCentralSeries (i + j + 1) := by
  induction j generalizing i with
  | zero => simp [Subgroup.lowerCentralSeries_succ]
  | succ j ih =>
    rw [Subgroup.lowerCentralSeries_succ _ j, Subgroup.commutator_comm]
    apply commutator_commutator_le_of_rotate
    · rw [Subgroup.commutator_comm ⊤, ← Subgroup.lowerCentralSeries_succ]
      exact (ih (i + 1)).trans (le_of_eq (by congr 1; omega))
    · calc ⁅⁅(⊤ : Subgroup G).lowerCentralSeries i, (⊤ : Subgroup G).lowerCentralSeries j⁆, ⊤⁆
          ≤ ⁅(⊤ : Subgroup G).lowerCentralSeries (i + j + 1), ⊤⁆ :=
            Subgroup.commutator_mono (ih i) le_rfl
        _ = (⊤ : Subgroup G).lowerCentralSeries (i + (j + 1) + 1) := by
          rw [← Subgroup.lowerCentralSeries_succ]; congr 1

/-- **004b, Lemma 2.1**: `G^(d) ≤ γ_{2^d}(G)`. -/
theorem derivedSeries_le_lowerCentralSeries_two_pow (d : ℕ) :
    derivedSeries G d ≤ (⊤ : Subgroup G).lowerCentralSeries (2 ^ d - 1) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [derivedSeries_succ]
    refine (Subgroup.commutator_mono ih ih).trans
      ((commutator_lowerCentralSeries_le _ _).trans (le_of_eq ?_))
    congr 1
    have := Nat.one_le_two_pow (n := d)
    rw [pow_succ]; omega

/-- **Shadow annihilation, solvable case** (004b, Theorem 6.1(i)). -/
theorem shadow_solvable {F H : Type*} [Group F] [Group H] (φ : F →* H) {d : ℕ}
    (hH : derivedSeries H d = ⊥) {w : F} (hw : w ∈ derivedSeries F d) : φ w = 1 := by
  have : φ w ∈ derivedSeries H d := map_derivedSeries_le_derivedSeries φ d ⟨w, hw, rfl⟩
  rw [hH] at this; exact this

/-- **Shadow annihilation, nilpotent case** (004b, Theorem 6.1(ii)): a nilpotent group of class
less than `2^d` (that is, `γ_{2^d}(H) = 1`) kills `F^(d)`. -/
theorem shadow_nilpotent {F H : Type*} [Group F] [Group H] (φ : F →* H) {d : ℕ}
    (hH : (⊤ : Subgroup H).lowerCentralSeries (2 ^ d - 1) = ⊥) {w : F}
    (hw : w ∈ derivedSeries F d) :
    φ w = 1 := by
  have h1 : φ w ∈ derivedSeries H d := map_derivedSeries_le_derivedSeries φ d ⟨w, hw, rfl⟩
  have h2 := derivedSeries_le_lowerCentralSeries_two_pow (G := H) d h1
  rw [hH] at h2; exact h2

/-- In a finite solvable group each strict step of the derived series at least halves the
order; hence a finite solvable group of order `< 2^d` has `H^(d) = 1`
(004b, proof of Corollary 6.2 and Remark 6.3(1)). -/
theorem derivedSeries_eq_bot_of_card_lt {H : Type*} [Group H] [Finite H] [Group.IsSolvable H] {d : ℕ}
    (hcard : Nat.card H < 2 ^ d) : derivedSeries H d = ⊥ := by
  have claim : ∀ n, derivedSeries H n = ⊥ ∨
      2 ^ n * Nat.card (derivedSeries H n) ≤ Nat.card H := by
    intro n
    induction n with
    | zero => right; simp
    | succ n ih =>
      rcases ih with h | h
      · left; rw [derivedSeries_succ, h, Subgroup.commutator_bot_left]
      · by_cases hb : derivedSeries H (n + 1) = ⊥
        · exact Or.inl hb
        right
        have hle : derivedSeries H (n + 1) ≤ derivedSeries H n :=
          derivedSeries_antitone H (Nat.le_succ n)
        have hne : derivedSeries H (n + 1) ≠ derivedSeries H n := by
          intro heq
          have hstab : ∀ m, derivedSeries H (n + m) = derivedSeries H n := by
            intro m
            induction m with
            | zero => rfl
            | succ m ihm => rw [← add_assoc, derivedSeries_succ, ihm, ← derivedSeries_succ, heq]
          obtain ⟨m, hm⟩ := Group.IsSolvable.solvable (G := H)
          apply hb
          have h1 : derivedSeries H (n + m) = ⊥ :=
            le_bot_iff.1 (hm ▸ derivedSeries_antitone H (Nat.le_add_left m n))
          rw [hstab m] at h1; rw [heq]; exact h1
        have hdvd := Subgroup.card_dvd_of_le hle
        have hlt : Nat.card (derivedSeries H (n + 1)) ≠ Nat.card (derivedSeries H n) := by
          intro hc; exact hne (Subgroup.eq_of_le_of_card_ge hle hc.ge)
        obtain ⟨c, hc⟩ := hdvd
        have hpos : 0 < Nat.card (derivedSeries H (n + 1)) := Nat.card_pos
        have hc2 : 2 ≤ c := by
          rcases c with _ | _ | c
          · simp at hc; have := (Nat.card_pos (α := derivedSeries H n)); omega
          · simp at hc; exact absurd hc.symm hlt
          · omega
        calc 2 ^ (n + 1) * Nat.card (derivedSeries H (n + 1))
            = 2 ^ n * (2 * Nat.card (derivedSeries H (n + 1))) := by ring
          _ ≤ 2 ^ n * Nat.card (derivedSeries H n) := by
            apply Nat.mul_le_mul_left; rw [hc]; nlinarith
          _ ≤ Nat.card H := h
  rcases claim d with h | h
  · exact h
  · have : 0 < Nat.card (derivedSeries H d) := Nat.card_pos
    exfalso
    have : 2 ^ d ≤ 2 ^ d * Nat.card (derivedSeries H d) := Nat.le_mul_of_pos_right _ this
    omega

end Series

/-- Existential form of the shared tower (004b, Theorem 4.2 (i), (ii)): every element of `A₅`
has a representative in every term of the derived series of `F(P, Q)`. -/
theorem tower_exists (d : ℕ) : ∀ g ∈ alternatingGroup (Fin 5),
    ∃ w ∈ derivedSeries F2 d, ev w = g :=
  fun g hg => ⟨towerR g d, (tower_spec d g hg).2, (tower_spec d g hg).1⟩

/-- **No small solvable or nilpotent image can decide** (004b, Theorems 5.1, 6.1, Corollary 6.2,
Remark 6.3(1), combined). For every `A₅` circuit `C` with constants in `A₅` and every `d` there is
a substitution `ν` of the constants by words of `F^(d)` with `ev ∘ ν = id` on `A₅` (the tower
representatives) such that every node `w` of the substituted circuit satisfies: `ev w` is the
value of that node in `C`, while `φ w = 1` for every homomorphism `φ` from `F(P, Q)` to a finite
solvable group of order `< 2^d` and to any group that is nilpotent of class `< 2^d`. -/
theorem deep_core_invisible (C : List (Op (Perm (Fin 5)))) (hC : ConstsInA5 C) (d : ℕ) :
    ∃ ν : Perm (Fin 5) → F2,
      (∀ g ∈ alternatingGroup (Fin 5), ν g ∈ derivedSeries F2 d ∧ ev (ν g) = g) ∧
      ∀ k, ev (val ν C k) = val id C k ∧
      (∀ (H : Type) [Group H] [Finite H] [Group.IsSolvable H], Nat.card H < 2 ^ d →
        ∀ φ : F2 →* H, φ (val ν C k) = 1) ∧
      (∀ (H : Type) [Group H], (⊤ : Subgroup H).lowerCentralSeries (2 ^ d - 1) = ⊥ →
        ∀ φ : F2 →* H, φ (val ν C k) = 1) := by
  refine ⟨fun g => towerR g d, fun g hg => ⟨(tower_spec d g hg).2, (tower_spec d g hg).1⟩,
    fun k => ?_⟩
  obtain ⟨hmem, hval⟩ := deep_reduction C hC d k
  refine ⟨hval, fun H _ _ _ hcard φ => ?_, fun H _ hH φ => shadow_nilpotent φ hH hmem⟩
  exact shadow_solvable φ (derivedSeries_eq_bot_of_card_lt hcard) hmem

end GC.A5Programs
