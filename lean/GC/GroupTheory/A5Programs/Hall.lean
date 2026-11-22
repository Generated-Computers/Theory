import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Data.Fintype.Basic

/-!
# P. Hall's theorem on generating pairs of powers of a simple group

Let `T` be a simple nonabelian group and `(x_i, y_i)` a family of generating pairs of `T`, no two
of which are related by an automorphism. Then the elements `(x_i)_i` and `(y_i)_i` generate the
direct power `T^ι` (P. Hall, 1936; manuscript 004c, Lemma 5.1 and Theorem 5.2).

The proof follows the paper: for two coordinates the projection is a subgroup of `T × T` whose
projections are onto, hence (Goursat) either `T × T` or the graph of an automorphism; then a
commutator argument (`T` is perfect) upgrades pairwise surjectivity to all of `T^ι`.
-/

namespace GC.A5Programs

open scoped commutatorElement

variable {T : Type*} [Group T] [IsSimpleGroup T]

/-- A simple nonabelian group is perfect: its commutator subgroup is everything. -/
theorem commutator_eq_top_of_simple (hT : ∃ a b : T, a * b ≠ b * a) :
    _root_.commutator T = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (_root_.commutator T) inferInstance with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hT
    have : ⁅a, b⁆ ∈ _root_.commutator T :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact hab this
  · exact h

/-- **Subdirect powers of a perfect group** (004c, Lemma 5.1, in the form used): if a subgroup `S`
of `T^ι` (`ι` finite) contains, for all `i ≠ j` and all `t`, an element with `i`-th coordinate
`t` and `j`-th coordinate `1`, and its projection to every coordinate is onto, then `S` is
everything. -/
theorem subdirect_eq_top {ι : Type*} [Finite ι] [DecidableEq ι] (hT : ∃ a b : T, a * b ≠ b * a)
    (S : Subgroup (ι → T)) (hproj : ∀ i t, ∃ s ∈ S, s i = t)
    (hpair : ∀ i j, i ≠ j → ∀ t, ∃ s ∈ S, s i = t ∧ s j = 1) : S = ⊤ := by
  classical
  have := Fintype.ofFinite ι
  -- for every finite set `J` avoiding `i`, coordinate `i` is free while `J` is trivial
  have key : ∀ i (J : Finset ι), i ∉ J → ∀ t, ∃ s ∈ S, s i = t ∧ ∀ j ∈ J, s j = 1 := by
    intro i J
    induction J using Finset.induction_on with
    | empty => intro _ t; obtain ⟨s, hs, hst⟩ := hproj i t; exact ⟨s, hs, hst, by simp⟩
    | @insert l J hlJ ih =>
      intro hi
      have hiJ : i ∉ J := fun h => hi (Finset.mem_insert_of_mem h)
      have hil : i ≠ l := fun h => hi (h ▸ Finset.mem_insert_self _ _)
      let K : Subgroup T :=
        { carrier := {t | ∃ s ∈ S, s i = t ∧ ∀ j ∈ insert l J, s j = 1}
          one_mem' := ⟨1, S.one_mem, rfl, fun _ _ => rfl⟩
          mul_mem' := by
            rintro a b ⟨s, hs, rfl, hsj⟩ ⟨s', hs', rfl, hsj'⟩
            exact ⟨s * s', S.mul_mem hs hs', rfl, fun j hj => by simp [hsj j hj, hsj' j hj]⟩
          inv_mem' := by
            rintro a ⟨s, hs, rfl, hsj⟩
            exact ⟨s⁻¹, S.inv_mem hs, rfl, fun j hj => by simp [hsj j hj]⟩ }
      have hK : _root_.commutator T ≤ K := by
        rw [_root_.commutator, Subgroup.commutator_le]
        intro a _ b _
        obtain ⟨s, hs, hsa, hsJ⟩ := ih hiJ a
        obtain ⟨s', hs', hsb, hsl⟩ := hpair i l hil b
        refine ⟨⁅s, s'⁆, Subgroup.commutator_mem_commutator hs hs' |> fun h => ?_, ?_, ?_⟩
        · exact S.mul_mem (S.mul_mem (S.mul_mem hs hs') (S.inv_mem hs)) (S.inv_mem hs')
        · simp [commutatorElement_def, hsa, hsb]
        · intro j hj
          rcases Finset.mem_insert.1 hj with rfl | hj
          · simp [commutatorElement_def, hsl]
          · simp [commutatorElement_def, hsJ j hj]
      rw [commutator_eq_top_of_simple hT] at hK
      intro t
      exact hK (Subgroup.mem_top t)
  -- every single-coordinate element lies in `S`
  have hsingle : ∀ i t, Pi.mulSingle i t ∈ S := by
    intro i t
    obtain ⟨s, hs, hst, hsj⟩ := key i (Finset.univ.erase i) (by simp) t
    convert hs using 1
    funext j
    by_cases hj : j = i
    · subst hj; simp [hst]
    · rw [Pi.mulSingle_eq_of_ne hj, hsj j (by simp [hj])]
  rw [eq_top_iff, ← Subgroup.pi_top Set.univ, Subgroup.pi_le_iff]
  rintro i _ ⟨t, -, rfl⟩
  exact hsingle i t

/-- Goursat step for a pair of coordinates: a subgroup of `T × T` with both projections onto is
either the graph of an automorphism or contains all `(t, 1)`. -/
theorem pair_step (D : Subgroup (T × T)) (h1 : ∀ a, ∃ b, (a, b) ∈ D) (h2 : ∀ b, ∃ a, (a, b) ∈ D) :
    (∀ t, (t, 1) ∈ D) ∨ ∃ φ : T ≃* T, ∀ a b, (a, b) ∈ D → b = φ a := by
  classical
  -- `N₁ = {t | (t, 1) ∈ D}` is normal
  let N₁ : Subgroup T := D.comap (MonoidHom.inl T T)
  let N₂ : Subgroup T := D.comap (MonoidHom.inr T T)
  have hN₁ : N₁.Normal := ⟨by
    intro t ht g
    obtain ⟨b, hb⟩ := h1 g
    have : (g, b) * (t, 1) * (g, b)⁻¹ ∈ D := D.mul_mem (D.mul_mem hb ht) (D.inv_mem hb)
    simpa [N₁] using this⟩
  have hN₂ : N₂.Normal := ⟨by
    intro t ht g
    obtain ⟨a, ha⟩ := h2 g
    have : (a, g) * (1, t) * (a, g)⁻¹ ∈ D := D.mul_mem (D.mul_mem ha ht) (D.inv_mem ha)
    simpa [N₂] using this⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N₁ hN₁ with hb1 | ht1
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N₂ hN₂ with hb2 | ht2
    · -- `D` is the graph of an automorphism
      right
      have huniq : ∀ a b b', (a, b) ∈ D → (a, b') ∈ D → b = b' := by
        intro a b b' hb hb'
        have : (a, b)⁻¹ * (a, b') ∈ D := D.mul_mem (D.inv_mem hb) hb'
        have h' : b⁻¹ * b' ∈ N₂ := by simpa [N₂] using this
        rw [hb2, Subgroup.mem_bot, inv_mul_eq_one] at h'
        exact h'
      choose f hf using h1
      have fmul : ∀ a a', f (a * a') = f a * f a' := fun a a' =>
        (huniq _ _ _ (hf (a * a')) (D.mul_mem (hf a) (hf a'))).trans rfl
      let φ : T →* T := { toFun := f, map_one' := (huniq 1 _ 1 (hf 1) D.one_mem),
                           map_mul' := fmul }
      have hinj : Function.Injective φ := by
        rw [injective_iff_map_eq_one]
        intro a ha
        have : (a, 1) ∈ D := by have := hf a; simpa [φ, show f a = 1 from ha] using this
        have h' : a ∈ N₁ := by simpa [N₁] using this
        rwa [hb1, Subgroup.mem_bot] at h'
      have hsurj : Function.Surjective φ := by
        intro b
        obtain ⟨a, ha⟩ := h2 b
        exact ⟨a, (huniq a _ _ (hf a) ha)⟩
      refine ⟨MulEquiv.ofBijective φ ⟨hinj, hsurj⟩, fun a b hab => ?_⟩
      exact (huniq a _ _ (hf a) hab).symm
    · -- `D ⊇ 1 × T`, so `(t, 1) ∈ D` for all `t`
      left
      intro t
      obtain ⟨b, hb⟩ := h1 t
      have : (1, b) ∈ D := by
        have : b ∈ N₂ := ht2 ▸ Subgroup.mem_top _
        simpa [N₂] using this
      simpa using D.mul_mem hb (D.inv_mem this)
  · left; intro t
    have : t ∈ N₁ := ht1 ▸ Subgroup.mem_top t
    simpa [N₁] using this

/-- **P. Hall's theorem** (004c, Theorem 5.2, in general form). If `T` is simple nonabelian and
`(x i, y i)` are generating pairs of `T`, no two related by an automorphism, then `x, y`
generate `T^ι`. -/
theorem hall_generation {ι : Type*} [Finite ι] [DecidableEq ι] (hT : ∃ a b : T, a * b ≠ b * a)
    (x y : ι → T) (hgen : ∀ i, Subgroup.closure {x i, y i} = ⊤)
    (hdist : ∀ i j, i ≠ j → ¬ ∃ φ : T ≃* T, φ (x i) = x j ∧ φ (y i) = y j) :
    Subgroup.closure {x, y} = ⊤ := by
  classical
  set S := Subgroup.closure ({x, y} : Set (ι → T)) with hS
  -- projections of `S`
  have hmapi : ∀ i, S.map (Pi.evalMonoidHom (fun _ => T) i) = ⊤ := by
    intro i
    rw [hS, MonoidHom.map_closure, ← hgen i]
    congr 1
    ext t; simp [Set.image_insert_eq]
  have hproj : ∀ i t, ∃ s ∈ S, s i = t := by
    intro i t
    have : t ∈ S.map (Pi.evalMonoidHom (fun _ => T) i) := (hmapi i) ▸ Subgroup.mem_top t
    obtain ⟨s, hs, rfl⟩ := this
    exact ⟨s, hs, rfl⟩
  apply subdirect_eq_top hT S hproj
  intro i j hij t
  let π : (ι → T) →* T × T :=
    MonoidHom.prod (Pi.evalMonoidHom (fun _ => T) i) (Pi.evalMonoidHom (fun _ => T) j)
  let D := S.map π
  have hD1 : ∀ a, ∃ b, (a, b) ∈ D := by
    intro a; obtain ⟨s, hs, rfl⟩ := hproj i a; exact ⟨s j, s, hs, rfl⟩
  have hD2 : ∀ b, ∃ a, (a, b) ∈ D := by
    intro b; obtain ⟨s, hs, rfl⟩ := hproj j b; exact ⟨s i, s, hs, rfl⟩
  rcases pair_step D hD1 hD2 with h | ⟨φ, hφ⟩
  · obtain ⟨s, hs, hst⟩ := h t
    exact ⟨s, hs, (Prod.ext_iff.1 hst).1, (Prod.ext_iff.1 hst).2⟩
  · exfalso
    apply hdist i j hij
    refine ⟨φ, ?_, ?_⟩
    · exact (hφ (x i) (x j) ⟨x, Subgroup.subset_closure (by simp), rfl⟩).symm
    · exact (hφ (y i) (y j) ⟨y, Subgroup.subset_closure (by simp), rfl⟩).symm

end GC.A5Programs
