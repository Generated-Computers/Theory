import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.Group
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Polynomial completeness of finite simple nonabelian groups (Maurer–Rhodes)

A *polynomial function* `G^k → G` is one given by a group term in `k` variables with constants
from `G`. We prove the theorem of Maurer and Rhodes (1965): if `G` is a finite simple nonabelian
group, every function `G^k → G` is a polynomial function. The papers of family 004 quote this
theorem; here it is proved.

The proof: a commutator `[t(x), c s(x) c⁻¹]` vanishes where `t` or `s` vanishes and, for a
suitable constant `c`, does not vanish at the identity (`exists_conj_not_commute`). By induction
this gives a polynomial that vanishes everywhere except at the identity tuple. The set of `h`
for which the "delta function" with value `h` at `1` is polynomial is a nontrivial normal
subgroup, hence everything; translating and multiplying delta functions interpolates any `f`.
-/

namespace GC.A5Programs

/-- Group terms in `k` variables with constants from `G`. -/
inductive GTerm (G : Type*) (k : ℕ) where
  | var : Fin k → GTerm G k
  | const : G → GTerm G k
  | mul : GTerm G k → GTerm G k → GTerm G k
  | inv : GTerm G k → GTerm G k

variable {G : Type*} [Group G] {k : ℕ}

/-- Evaluation of a group term. -/
def GTerm.eval : GTerm G k → (Fin k → G) → G
  | .var i, x => x i
  | .const g, _ => g
  | .mul s t, x => s.eval x * t.eval x
  | .inv t, x => (t.eval x)⁻¹

/-- Substitution of terms for the variables. -/
def GTerm.subst {m : ℕ} (σ : Fin k → GTerm G m) : GTerm G k → GTerm G m
  | .var i => σ i
  | .const g => .const g
  | .mul s t => .mul (s.subst σ) (t.subst σ)
  | .inv t => .inv (t.subst σ)

theorem GTerm.eval_subst {m : ℕ} (σ : Fin k → GTerm G m) (t : GTerm G k) (x : Fin m → G) :
    (t.subst σ).eval x = t.eval (fun i => (σ i).eval x) := by
  induction t with
  | var i => rfl
  | const g => rfl
  | mul s t hs ht => simp [GTerm.subst, GTerm.eval, hs, ht]
  | inv t ht => simp [GTerm.subst, GTerm.eval, ht]

/-- A function `G^k → G` is polynomial if some group term with constants computes it. -/
def IsPolynomial (f : (Fin k → G) → G) : Prop := ∃ t : GTerm G k, ∀ x, t.eval x = f x

namespace IsPolynomial

theorem const (g : G) : IsPolynomial (fun _ : Fin k → G => g) := ⟨.const g, fun _ => rfl⟩

theorem var (i : Fin k) : IsPolynomial (fun x : Fin k → G => x i) := ⟨.var i, fun _ => rfl⟩

theorem mul {f g : (Fin k → G) → G} (hf : IsPolynomial f) (hg : IsPolynomial g) :
    IsPolynomial (fun x => f x * g x) := by
  obtain ⟨s, hs⟩ := hf; obtain ⟨t, ht⟩ := hg
  exact ⟨.mul s t, fun x => by simp [GTerm.eval, hs, ht]⟩

theorem inv {f : (Fin k → G) → G} (hf : IsPolynomial f) : IsPolynomial (fun x => (f x)⁻¹) := by
  obtain ⟨s, hs⟩ := hf
  exact ⟨.inv s, fun x => by simp [GTerm.eval, hs]⟩

theorem comp {m : ℕ} {f : (Fin k → G) → G} (hf : IsPolynomial f) {σ : Fin k → (Fin m → G) → G}
    (hσ : ∀ i, IsPolynomial (σ i)) : IsPolynomial (fun x => f (fun i => σ i x)) := by
  obtain ⟨t, ht⟩ := hf
  choose τ hτ using hσ
  exact ⟨t.subst τ, fun x => by rw [GTerm.eval_subst]; simp [hτ, ht]⟩

theorem commutator {f g : (Fin k → G) → G} (hf : IsPolynomial f) (hg : IsPolynomial g) :
    IsPolynomial (fun x => f x * g x * (f x)⁻¹ * (g x)⁻¹) :=
  ((hf.mul hg).mul hf.inv).mul hg.inv

theorem list_prod {ι : Type*} (L : List ι) (F : ι → (Fin k → G) → G)
    (hF : ∀ i ∈ L, IsPolynomial (F i)) : IsPolynomial (fun x => (L.map (fun i => F i x)).prod) := by
  induction L with
  | nil => simpa using const (1 : G)
  | cons a L ih =>
    simp only [List.map_cons, List.prod_cons]
    exact (hF a (by simp)).mul (ih fun i hi => hF i (by simp [hi]))

end IsPolynomial

section Simple

variable [IsSimpleGroup G]

/-- In a simple nonabelian group, a nontrivial element does not commute with some conjugate of
any other nontrivial element. -/
theorem exists_conj_not_commute (hG : ∃ a b : G, a * b ≠ b * a) {h g : G} (hh : h ≠ 1)
    (hg : g ≠ 1) : ∃ c : G, h * (c * g * c⁻¹) ≠ (c * g * c⁻¹) * h := by
  by_contra hcon
  push Not at hcon
  -- the normal closure of `g` is everything and centralizes `h`
  have hN : Subgroup.normalClosure ({g} : Set G) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal _
        (Subgroup.normalClosure_normal (s := ({g} : Set G))) with h1 | h1
    · exfalso; apply hg
      have : g ∈ Subgroup.normalClosure ({g} : Set G) := Subgroup.subset_normalClosure rfl
      rw [h1] at this; simpa using this
    · exact h1
  have hle : Subgroup.normalClosure ({g} : Set G) ≤ Subgroup.centralizer {h} := by
    refine Subgroup.closure_le _ |>.2 ?_
    intro x hx
    rw [Group.mem_conjugatesOfSet_iff] at hx
    obtain ⟨a, ha, hconj⟩ := hx
    rw [Set.mem_singleton_iff] at ha; subst ha
    obtain ⟨c, rfl⟩ := isConj_iff.1 hconj
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro y hy; rw [Set.mem_singleton_iff] at hy; subst hy
    exact hcon c
  have hcent : h ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro y
    have : y ∈ Subgroup.centralizer ({h} : Set G) := hle (hN ▸ Subgroup.mem_top y)
    rw [Subgroup.mem_centralizer_iff] at this
    exact (this h rfl).symm
  have hZ : Subgroup.center G = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal _ (Subgroup.center G).normal_of_characteristic
      with h1 | h1
    · rw [h1] at hcent; exact absurd (by simpa using hcent) hh
    · exact h1
  obtain ⟨a, b, hab⟩ := hG
  apply hab
  have : b ∈ Subgroup.center G := hZ ▸ Subgroup.mem_top b
  exact (Subgroup.mem_center_iff.1 this a)

variable [Fintype G] [DecidableEq G]

omit [Fintype G] in
/-- For every finite set `Z` of tuples avoiding the identity tuple, some polynomial vanishes on
`Z` and not at the identity tuple. -/
theorem exists_vanishing (hG : ∃ a b : G, a * b ≠ b * a) (Z : Finset (Fin k → G))
    (hZ : (1 : Fin k → G) ∉ Z) :
    ∃ t : (Fin k → G) → G, IsPolynomial t ∧ t 1 ≠ 1 ∧ ∀ z ∈ Z, t z = 1 := by
  induction Z using Finset.induction_on with
  | empty =>
    obtain ⟨a, b, hab⟩ := hG
    have : a ≠ 1 := by rintro rfl; simp at hab
    exact ⟨fun _ => a, IsPolynomial.const a, this, by simp⟩
  | @insert z Z hzZ ih =>
    obtain ⟨t, ht, ht1, htZ⟩ := ih (fun h => hZ (Finset.mem_insert_of_mem h))
    have hz : z ≠ 1 := fun h => hZ (h ▸ Finset.mem_insert_self _ _)
    obtain ⟨i, hi⟩ : ∃ i, z i ≠ 1 := by
      by_contra hcon; push Not at hcon; exact hz (funext hcon)
    obtain ⟨c, hc⟩ := exists_conj_not_commute hG ht1 (inv_ne_one.2 hi)
    refine ⟨fun x => t x * (c * (x i * (z i)⁻¹) * c⁻¹) * (t x)⁻¹ *
      (c * (x i * (z i)⁻¹) * c⁻¹)⁻¹, ?_, ?_, ?_⟩
    · exact IsPolynomial.commutator ht
        (((IsPolynomial.const c).mul ((IsPolynomial.var i).mul (IsPolynomial.const _))).mul
          (IsPolynomial.const _))
    · simp only [Pi.one_apply, one_mul]
      intro h
      apply hc
      have := mul_inv_eq_one.1 h
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this
    · intro w hw
      rcases Finset.mem_insert.1 hw with rfl | hw
      · simp
      · show t w * _ * (t w)⁻¹ * _ = 1
        rw [htZ w hw]; group

/-- The delta function with value `h` at `g`. -/
def delta (g : Fin k → G) (h : G) (x : Fin k → G) : G := if x = g then h else 1

theorem isPolynomial_delta_one (hG : ∃ a b : G, a * b ≠ b * a) (h : G) :
    IsPolynomial (delta (1 : Fin k → G) h) := by
  classical
  -- the set of good values is a normal subgroup
  let N : Subgroup G :=
    { carrier := {h | IsPolynomial (delta (1 : Fin k → G) h)}
      one_mem' := by
        show IsPolynomial _
        have : delta (1 : Fin k → G) (1 : G) = fun _ => 1 := by
          funext x; simp [delta]
        rw [this]; exact IsPolynomial.const 1
      mul_mem' := by
        intro a b ha hb
        show IsPolynomial _
        have : delta (1 : Fin k → G) (a * b) = fun x => delta 1 a x * delta 1 b x := by
          funext x; by_cases hx : x = 1 <;> simp [delta, hx]
        rw [this]; exact IsPolynomial.mul ha hb
      inv_mem' := by
        intro a ha
        show IsPolynomial _
        have : delta (1 : Fin k → G) a⁻¹ = fun x => (delta 1 a x)⁻¹ := by
          funext x; by_cases hx : x = 1 <;> simp [delta, hx]
        rw [this]; exact IsPolynomial.inv ha }
  have hNn : N.Normal := ⟨by
    intro a ha c
    show IsPolynomial _
    have : delta (1 : Fin k → G) (c * a * c⁻¹) = fun x => c * delta 1 a x * c⁻¹ := by
      funext x; by_cases hx : x = 1 <;> simp [delta, hx]
    rw [this]
    exact ((IsPolynomial.const c).mul ha).mul (IsPolynomial.const _)⟩
  -- a nontrivial element of `N`
  obtain ⟨t, ht, ht1, htZ⟩ := exists_vanishing hG (Finset.univ.erase (1 : Fin k → G)) (by simp)
  have hmem : t 1 ∈ N := by
    show IsPolynomial _
    have : delta (1 : Fin k → G) (t 1) = t := by
      funext x; by_cases hx : x = 1
      · simp [delta, hx]
      · simp [delta, hx, htZ x (by simp [hx])]
    rw [this]; exact ht
  have hN : N = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N hNn with h1 | h1
    · exfalso; rw [h1] at hmem; exact ht1 (by simpa using hmem)
    · exact h1
  have : h ∈ N := hN ▸ Subgroup.mem_top h
  exact this

theorem isPolynomial_delta (hG : ∃ a b : G, a * b ≠ b * a) (g : Fin k → G) (h : G) :
    IsPolynomial (delta g h) := by
  have hd := (isPolynomial_delta_one hG h (k := k)).comp
    (σ := fun i x => x i * (g i)⁻¹)
    (fun i => (IsPolynomial.var i).mul (IsPolynomial.const _))
  have : delta g h = fun x => delta (1 : Fin k → G) h (fun i => x i * (g i)⁻¹) := by
    funext x
    have : ((fun i => x i * (g i)⁻¹) = 1) ↔ x = g := by
      constructor
      · intro hx; funext i; have := congrFun hx i; simpa [mul_inv_eq_one] using this
      · rintro rfl; funext i; simp
    by_cases hx : x = g
    · simp only [delta, if_pos hx]; rw [if_pos (this.2 hx)]
    · simp only [delta, hx, if_false]; rw [if_neg (fun h' => hx (this.1 h'))]
  rw [this]; exact hd

omit [IsSimpleGroup G] [Fintype G] in
theorem prod_delta (f : (Fin k → G) → G) (L : List (Fin k → G)) (hL : L.Nodup)
    (x : Fin k → G) : (L.map (fun g => delta g (f g) x)).prod = if x ∈ L then f x else 1 := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.nodup_cons] at hL
    simp only [List.map_cons, List.prod_cons, ih hL.2, List.mem_cons]
    by_cases hxa : x = a
    · subst hxa; simp [delta, hL.1]
    · simp only [delta, hxa, if_false, one_mul]
      by_cases hxL : x ∈ L <;> simp [hxL]

/-- **Maurer–Rhodes.** In a finite simple nonabelian group every function `G^k → G` is a
polynomial function. -/
theorem maurer_rhodes (hG : ∃ a b : G, a * b ≠ b * a) (f : (Fin k → G) → G) :
    IsPolynomial f := by
  classical
  have h := IsPolynomial.list_prod (Finset.univ : Finset (Fin k → G)).toList
    (fun g => delta g (f g)) (fun g _ => isPolynomial_delta hG g (f g))
  obtain ⟨t, ht⟩ := h
  refine ⟨t, fun x => ?_⟩
  rw [ht]
  show (List.map (fun g => delta g (f g) x) Finset.univ.toList).prod = f x
  rw [prod_delta f _ (Finset.nodup_toList _)]
  simp

end Simple

end GC.A5Programs
