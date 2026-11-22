import GC.Computability.SCLadder.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Manuscript 008c: inner product has affine-cover number `2^m`

`H m = {(a, b, z) ∈ 𝔽₂^m × 𝔽₂^m × 𝔽₂ : z = a ⬝ b}` is the graph of the inner product.
We prove Theorem `thm:ip` of the paper:

* every affine subspace contained in `H m` has at most `2^m` points;
* the `2^m` affine subspaces `fiber a = {(a, b, a ⬝ b) : b ∈ 𝔽₂^m}` partition `H m`;
* the affine-cover number of `H m` is exactly `2^m`.
-/

namespace GC.SCLadder

open Module Matrix

/-- Vectors of `𝔽₂^m`. -/
abbrev Vec (m : ℕ) := Fin m → F

/-- Points of `𝔽₂^m × 𝔽₂^m × 𝔽₂`. -/
abbrev Pt (m : ℕ) := Vec m × Vec m × F

/-- The graph `H_m = {(a, b, z) : z = a ⬝ b}` of the inner product. -/
def H (m : ℕ) : Set (Pt m) := {p | p.2.2 = p.1 ⬝ᵥ p.2.1}

/-- The affine-cover number of a set `S` of a vector space: the least number of affine subspaces
contained in `S` whose union is `S`. -/
noncomputable def affineCoverNumber {k V : Type*} [Ring k] [AddCommGroup V] [Module k V]
    (S : Set V) : ℕ :=
  sInf {n | ∃ A : Fin n → AffineSubspace k V, (∀ i, (A i : Set V) ⊆ S) ∧ ⋃ i, (A i : Set V) = S}

/-- The linear part of `b ↦ (a, b, a ⬝ b)`. -/
noncomputable def fiberLin {m : ℕ} (a : Vec m) : Vec m →ₗ[F] Pt m :=
  LinearMap.prod 0 (LinearMap.prod LinearMap.id ((dotProductEquiv F (Fin m)) a))

/-- The affine subspace `{(a, b, a ⬝ b) : b ∈ 𝔽₂^m}`. -/
noncomputable def fiber {m : ℕ} (a : Vec m) : AffineSubspace F (Pt m) :=
  AffineSubspace.mk' (a, 0, 0) (LinearMap.range (fiberLin a))

lemma mem_fiber {m : ℕ} (a : Vec m) (p : Pt m) :
    p ∈ fiber a ↔ p.1 = a ∧ p.2.2 = a ⬝ᵥ p.2.1 := by
  rcases p with ⟨x, y, z⟩
  simp only [fiber, AffineSubspace.mem_mk', LinearMap.mem_range, fiberLin, vsub_eq_sub]
  constructor
  · rintro ⟨b, hb⟩
    have h1 := congrArg Prod.fst hb
    have h2 := congrArg (fun q => q.2.1) hb
    have h3 := congrArg (fun q => q.2.2) hb
    simp at h1 h2 h3
    refine ⟨(sub_eq_zero.mp h1.symm), ?_⟩
    rw [← h3, h2]
  · rintro ⟨h1, h2⟩
    refine ⟨y, ?_⟩
    simp [h1, h2]

lemma fiber_subset_H {m : ℕ} (a : Vec m) : (fiber a : Set (Pt m)) ⊆ H m := by
  intro p hp
  rw [SetLike.mem_coe, mem_fiber] at hp
  simp only [H, Set.mem_ofPred_eq, hp.1, hp.2]

lemma iUnion_fiber (m : ℕ) : ⋃ a : Vec m, (fiber a : Set (Pt m)) = H m := by
  ext p
  simp only [Set.mem_iUnion, SetLike.mem_coe, mem_fiber]
  constructor
  · rintro ⟨a, h1, h2⟩
    simp [H, h1, h2]
  · intro h
    exact ⟨p.1, rfl, h⟩

lemma pairwise_disjoint_fiber (m : ℕ) :
    Pairwise (fun a a' : Vec m => Disjoint (fiber a : Set (Pt m)) (fiber a')) := by
  intro a a' hne
  rw [Set.disjoint_left]
  intro p hp hp'
  rw [SetLike.mem_coe, mem_fiber] at hp hp'
  exact hne (hp.1.symm.trans hp'.1)

/-- If `p₀ ∈ H` and `p₀ + w ∈ H`, then the `z`-coordinate of `w` is determined. -/
lemma H_add_identity {m : ℕ} {p w : Pt m} (hp : p ∈ H m) (hw : w + p ∈ H m) :
    w.2.2 = p.1 ⬝ᵥ w.2.1 + w.1 ⬝ᵥ p.2.1 + w.1 ⬝ᵥ w.2.1 := by
  rcases p with ⟨a, b, z⟩
  rcases w with ⟨α, β, γ⟩
  simp only [H, Set.mem_ofPred_eq, Prod.mk_add_mk] at hp hw ⊢
  rw [add_dotProduct, dotProduct_add, dotProduct_add] at hw
  rw [hp] at hw
  linear_combination hw

/-- The direction of an affine subspace inside `H m` is totally isotropic for the polar form
`ω((α,β),(α',β')) = α ⬝ β' + α' ⬝ β`. -/
lemma isotropic_of_subset_H {m : ℕ} {A : AffineSubspace F (Pt m)} (hA : (A : Set (Pt m)) ⊆ H m)
    {p : Pt m} (hp : p ∈ A) {w w' : Pt m} (hw : w ∈ A.direction) (hw' : w' ∈ A.direction) :
    w.1 ⬝ᵥ w'.2.1 + w'.1 ⬝ᵥ w.2.1 = 0 := by
  have h0 : p ∈ H m := hA hp
  have h1 := H_add_identity h0 (hA (AffineSubspace.vadd_mem_of_mem_direction hw hp))
  have h2 := H_add_identity h0 (hA (AffineSubspace.vadd_mem_of_mem_direction hw' hp))
  have h3 := H_add_identity h0 (hA (AffineSubspace.vadd_mem_of_mem_direction
    (A.direction.add_mem hw hw') hp))
  simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add] at h3
  have hc : (2 : F) = 0 := rfl
  linear_combination h3 - h1 - h2 + (w.1 ⬝ᵥ w'.2.1 + w'.1 ⬝ᵥ w.2.1) * hc

/-- Key dimension bound: the direction of a nonempty affine subspace inside `H m`
has dimension at most `m`. -/
lemma finrank_direction_le {m : ℕ} {A : AffineSubspace F (Pt m)} (hA : (A : Set (Pt m)) ⊆ H m)
    {p : Pt m} (hp : p ∈ A) : finrank F A.direction ≤ m := by
  set D := A.direction
  -- projection to the `a`-coordinate
  let φ : D →ₗ[F] Vec m := (LinearMap.fst F (Vec m) (Vec m × F)).comp D.subtype
  set P := LinearMap.range φ
  -- on the kernel, the `b`-coordinate
  let ψ : LinearMap.ker φ →ₗ[F] Vec m :=
    ((LinearMap.fst F (Vec m) F).comp (LinearMap.snd F (Vec m) (Vec m × F))).comp
      (D.subtype.comp (LinearMap.ker φ).subtype)
  have hker : ∀ w : LinearMap.ker φ, (w : D).1.1 = 0 := fun w => w.2
  have hψrange : ∀ w : LinearMap.ker φ, ψ w ∈ dotOrth P := by
    intro w
    rw [mem_dotOrth]
    rintro x ⟨w', rfl⟩
    have := isotropic_of_subset_H hA hp (w : D).2 w'.2
    simp only [hker w, zero_dotProduct, zero_add] at this
    simpa [φ, ψ] using this
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    have hb : (w : D).1.2.1 = 0 := by simpa [ψ] using hw
    have ha : (w : D).1.1 = 0 := hker w
    have hz := H_add_identity (hA hp)
      (hA (AffineSubspace.vadd_mem_of_mem_direction (w : D).2 hp))
    rw [ha, hb] at hz
    simp only [dotProduct_zero, zero_dotProduct, add_zero] at hz
    ext <;> simp [ha, hb, hz]
  let ψ' : LinearMap.ker φ →ₗ[F] dotOrth P := LinearMap.codRestrict _ ψ hψrange
  have hψ'inj : Function.Injective ψ' := by
    intro x y hxy
    apply hψinj
    have := congrArg Subtype.val hxy
    simpa [ψ'] using this
  have h1 : finrank F P + finrank F (LinearMap.ker φ) = finrank F D :=
    LinearMap.finrank_range_add_finrank_ker φ
  have h2 := LinearMap.finrank_le_finrank_of_injective hψ'inj
  have h3 := finrank_add_finrank_dotOrth P
  simp only [Fintype.card_fin] at h3
  calc finrank F D = _ := h1.symm
    _ ≤ _ := Nat.add_le_add_left h2 _
    _ = m := h3

/-- First part of Theorem `thm:ip`: every affine subspace contained in `H m` has at most
`2^m` points. -/
theorem ncard_le_of_subset_H {m : ℕ} (A : AffineSubspace F (Pt m))
    (hA : (A : Set (Pt m)) ⊆ H m) : (A : Set (Pt m)).ncard ≤ 2 ^ m := by
  rcases (A : Set (Pt m)).eq_empty_or_nonempty with h | ⟨p, hp⟩
  · simp [h]
  have e : (A : Set (Pt m)) ≃ A.direction :=
    { toFun := fun q => ⟨q.1 -ᵥ p, AffineSubspace.vsub_mem_direction q.2 hp⟩
      invFun := fun w => ⟨w.1 +ᵥ p, AffineSubspace.vadd_mem_of_mem_direction w.2 hp⟩
      left_inv := fun q => by ext1; simp
      right_inv := fun w => by ext1; simp }
  rw [← Nat.card_coe_set_eq, Nat.card_congr e, Module.natCard_eq_pow_finrank (K := F),
    Nat.card_zmod]
  exact Nat.pow_le_pow_right (by norm_num) (finrank_direction_le hA hp)

/-- `|H_m| = 2^{2m}`. -/
theorem ncard_H (m : ℕ) : (H m).ncard = 2 ^ (2 * m) := by
  have e : H m ≃ Vec m × Vec m :=
    { toFun := fun p => (p.1.1, p.1.2.1)
      invFun := fun x => ⟨(x.1, x.2, x.1 ⬝ᵥ x.2), rfl⟩
      left_inv := fun p => by
        rcases p with ⟨⟨a, b, z⟩, hp⟩
        simp only [H, Set.mem_ofPred_eq] at hp
        simp [hp]
      right_inv := fun x => rfl }
  rw [← Nat.card_coe_set_eq, Nat.card_congr e, Nat.card_prod, Nat.card_fun]
  simp [two_mul, pow_add]

/-- Theorem `thm:ip` (lower bound): any cover of `H m` by `n` affine subspaces contained in
`H m` has `n ≥ 2^m`. -/
theorem le_of_affine_cover {m n : ℕ} (A : Fin n → AffineSubspace F (Pt m))
    (hsub : ∀ i, (A i : Set (Pt m)) ⊆ H m) (hcov : ⋃ i, (A i : Set (Pt m)) = H m) :
    2 ^ m ≤ n := by
  have h1 := Set.ncard_iUnion_le_of_fintype (fun i => (A i : Set (Pt m)))
  rw [hcov, ncard_H] at h1
  have h2 : ∑ i, (A i : Set (Pt m)).ncard ≤ ∑ _i : Fin n, 2 ^ m :=
    Finset.sum_le_sum fun i _ => ncard_le_of_subset_H (A i) (hsub i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h2
  have h3 : 2 ^ m * 2 ^ m ≤ n * 2 ^ m := by
    rw [← pow_add, ← two_mul]; omega
  exact Nat.le_of_mul_le_mul_right h3 (by positivity)

/-- Theorem `thm:ip` (upper bound): `H m` is the union of `2^m` affine subspaces inside it. -/
theorem exists_affine_cover (m : ℕ) : ∃ A : Fin (2 ^ m) → AffineSubspace F (Pt m),
    (∀ i, (A i : Set (Pt m)) ⊆ H m) ∧ ⋃ i, (A i : Set (Pt m)) = H m := by
  have hc : Fintype.card (Vec m) = 2 ^ m := by simp [ZMod.card]
  let e : Vec m ≃ Fin (2 ^ m) := Fintype.equivFinOfCardEq hc
  refine ⟨fun i => fiber (e.symm i), fun i => fiber_subset_H _, ?_⟩
  rw [← iUnion_fiber m]
  exact e.symm.surjective.iUnion_comp (fun a => (fiber a : Set (Pt m)))

/-- **Theorem `thm:ip` of 008c.** Every affine subspace contained in `H_m` has at most `2^m`
points, `cov(H_m) = 2^m`, and `H_m` is partitioned by the `2^m` affine subspaces
`{(a, b, a ⬝ b) : b ∈ 𝔽₂^m}`, `a ∈ 𝔽₂^m`. -/
theorem inner_product_affine_cover_number (m : ℕ) :
    (∀ A : AffineSubspace F (Pt m), (A : Set (Pt m)) ⊆ H m → (A : Set (Pt m)).ncard ≤ 2 ^ m) ∧
    affineCoverNumber (k := F) (H m) = 2 ^ m ∧
    (∀ a : Vec m, (fiber a : Set (Pt m)) ⊆ H m) ∧
    ⋃ a : Vec m, (fiber a : Set (Pt m)) = H m ∧
    Pairwise (fun a a' : Vec m => Disjoint (fiber a : Set (Pt m)) (fiber a')) := by
  refine ⟨ncard_le_of_subset_H, ?_, fiber_subset_H, iUnion_fiber m, pairwise_disjoint_fiber m⟩
  unfold affineCoverNumber
  apply le_antisymm
  · exact Nat.sInf_le (exists_affine_cover m)
  · apply le_csInf ⟨2 ^ m, exists_affine_cover m⟩
    intro n hn
    obtain ⟨A, hsub, hcov⟩ := hn
    exact le_of_affine_cover A hsub hcov

/-! ## Exact projection (Lemma `lem:proj`) and the INDEX state bound (Proposition `prop:index`) -/

lemma dotForm_nondegenerate (p : ℕ) : (dotForm F (Fin p)).Nondegenerate := by
  constructor
  · intro x hx
    funext i
    simpa [dotProduct_single] using hx (Pi.single i 1)
  · intro y hy
    funext i
    simpa [single_dotProduct] using hy (Pi.single i 1)

lemma dotForm_isRefl (p : ℕ) : (dotForm F (Fin p)).IsRefl := by
  intro x y h
  simpa [dotProduct_comm] using h

lemma dotOrth_dotOrth {p : ℕ} (W : Submodule F (Fin p → F)) : dotOrth (dotOrth W) = W :=
  LinearMap.BilinForm.orthogonal_orthogonal (dotForm_nondegenerate p) (dotForm_isRefl p) W

/-- **Lemma `lem:proj` (008c).** Let the rows of `L` span the left nullspace `{ℓ : ℓ A_y = 0}`
(and lie in it). Then `∃ y, A_x x + A_y y = b` holds if and only if `L A_x x = L b`. -/
theorem exact_projection {p nx ny k : ℕ} (Ax : Matrix (Fin p) (Fin nx) F)
    (Ay : Matrix (Fin p) (Fin ny) F) (b : Fin p → F) (L : Matrix (Fin k) (Fin p) F)
    (hL0 : L * Ay = 0) (hLspan : ∀ ℓ : Fin p → F, ℓ ᵥ* Ay = 0 → ℓ ∈ Submodule.span F (Set.range L))
    (x : Fin nx → F) :
    (∃ y, Ax *ᵥ x + Ay *ᵥ y = b) ↔ L *ᵥ (Ax *ᵥ x) = L *ᵥ b := by
  constructor
  · rintro ⟨y, rfl⟩
    rw [mulVec_add, mulVec_mulVec y L Ay, hL0, zero_mulVec, add_zero]
  · intro h
    set w := b - Ax *ᵥ x
    have hLw : L *ᵥ w = 0 := by simp [w, mulVec_sub, h]
    have hspanw : ∀ a ∈ Submodule.span F (Set.range L), a ⬝ᵥ w = 0 := by
      intro a ha
      induction ha using Submodule.span_induction with
      | mem a ha =>
        obtain ⟨i, rfl⟩ := ha
        exact congrFun hLw i
      | zero => simp
      | add a a' _ _ h₁ h₂ => rw [add_dotProduct, h₁, h₂, add_zero]
      | smul t a _ h₁ => rw [smul_dotProduct, h₁, smul_zero]
    -- `w` is orthogonal to the left nullspace, which is the orthogonal of the column space
    have hw : w ∈ dotOrth (dotOrth (LinearMap.range (Matrix.mulVecLin Ay))) := by
      rw [mem_dotOrth]
      intro ℓ hℓ
      have hℓ0 : ℓ ᵥ* Ay = 0 := by
        rw [mem_dotOrth] at hℓ
        ext j
        have := hℓ (Ay *ᵥ Pi.single j 1) ⟨_, rfl⟩
        rw [dotProduct_comm, dotProduct_mulVec, dotProduct_single, mul_one] at this
        simpa using this
      exact hspanw ℓ (hLspan ℓ hℓ0)
    rw [dotOrth_dotOrth] at hw
    obtain ⟨y, hy⟩ := hw
    refine ⟨y, ?_⟩
    simp only [Matrix.mulVecLin_apply] at hy
    rw [hy]
    simp only [w]
    abel

/-- **Proposition `prop:index` (008c), core.** Suppose the payload `y ∈ 𝔽₂^m` reaches a state
`σ y` at a vtree node whose subtree contains all payload slots and none of the address and output
slots, so that acceptance of `(y, i, z)` is a function `acc (σ y) i z` of that state and the outside
slots. If the automaton accepts exactly `z = y_i`, then `σ` is injective, so the node has at least
`2^m` states. -/
theorem index_state_lower_bound {m : ℕ} {St : Type*} [Finite St] (σ : Vec m → St) (acc : St → Fin m → F → Prop)
    (h : ∀ y i z, acc (σ y) i z ↔ z = y i) : Function.Injective σ ∧ 2 ^ m ≤ Nat.card St := by
  have hinj : Function.Injective σ := by
    intro y y' hyy'
    funext i
    have := (h y' i (y i)).mp (by rw [← hyy']; exact (h y i (y i)).mpr rfl)
    exact this
  refine ⟨hinj, ?_⟩
  have hfin : Nat.card (Vec m) = 2 ^ m := by simp
  rw [← hfin]
  exact Nat.card_le_card_of_injective σ hinj

end GC.SCLadder
