import GC.Computability.SCLadder.Basic
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Algebra.CharP.Two
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Manuscript 008b: knowledge compilation — exactness lemmas and representation barriers

Exactness of the operations on affine atoms and decomposable diagrams:

* `leaf_pullback` (Lemma `lem:leafpull`) and `leaf_conj` (Lemma `lem:leafand`): pulling back an atom
  `{y : B y ∈ R}` by an affine map, or intersecting two atoms, gives an atom `{x : D x ∈ R'}` over
  any matrix `D` whose row space contains the relevant rows (singular `M` allowed);
* `conj_iUnion_prod`, `conj_pairwise_disjoint` (Lemma `lem:vtops`): conjunction of decomposable
  nodes and preservation of determinism;
* `transfer_pullback` (Lemma `lem:transfer`): the transfer-syndrome decomposition of the preimage of a
  decomposable set under a block affine map, with pairwise disjoint terms.

Barriers:

* `rect_subset_diag_subsingleton`, `piece_injective`, `diag_cover_card` (Proposition `prop:pfeq`);
* `rect_card_le` (Lemma `lem:rect`): a rectangle on which `a ⬝ b = 1` has `|A| |B| ≤ 2^{n-1}`;
* `card_ip_eq_one` and `ip_rect_cover_card` (Proposition `prop:vtip`): every cover of
  `{(a,b) : a ⬝ b = 1}` by rectangles inside it has at least `2^n - 1` rectangles.

The class theorems (`NC^3`, `NC^{k+1}`, `NC^2`) and the cap-checked algorithms are not formalized.
-/

namespace GC.SCLadder

open Matrix Module

/-! ## Atoms: pullback and conjunction -/

section Atoms

variable {n k k' r : ℕ}

/-- **Lemma `lem:leafpull` (008b).** Let `y = M x + c` be an affine map (possibly singular) and
`(B, R)` an atom. If every row of `B M` lies in the row space of `D` and `rep` is a right inverse
of `x ↦ D x` (e.g. `σ` placed on the pivot columns of an RREF `D`), then
`{x : B (M x + c) ∈ R} = {x : D x ∈ R'}` with `R' = {σ : B (M x_σ + c) ∈ R}`. -/
theorem leaf_pullback (B : Matrix (Fin k) (Fin n) F) (R : Set (Fin k → F))
    (M : Matrix (Fin n) (Fin n) F) (c : Fin n → F) (D : Matrix (Fin r) (Fin n) F)
    (rep : (Fin r → F) → Fin n → F) (hrep : ∀ σ, D *ᵥ rep σ = σ)
    (hrows : ∀ i, (B * M) i ∈ Submodule.span F (Set.range D)) :
    {x | B *ᵥ (M *ᵥ x + c) ∈ R} = {x | D *ᵥ x ∈ {σ | B *ᵥ (M *ᵥ rep σ + c) ∈ R}} := by
  ext x
  simp only [Set.mem_ofPred_eq]
  have h := mulVec_eq_of_rows_mem_span D (B * M) hrows (hrep (D *ᵥ x)).symm
  rw [← mulVec_mulVec, ← mulVec_mulVec] at h
  rw [mulVec_add, mulVec_add, h]

/-- The rank of the pulled-back atom does not exceed the rank of `B`. -/
lemma rank_pullback_le (B : Matrix (Fin k) (Fin n) F) (M : Matrix (Fin n) (Fin n) F) :
    Matrix.rank (B * M) ≤ Matrix.rank B :=
  Matrix.rank_mul_le_left B M

/-- **Lemma `lem:leafand` (008b).** The intersection of the atoms `(B, R)` and `(C, R'')` is the atom
`(D, {σ : B x_σ ∈ R, C x_σ ∈ R''})` whenever the rows of `B` and `C` lie in the row space of
`D`. -/
theorem leaf_conj (B : Matrix (Fin k) (Fin n) F) (R : Set (Fin k → F))
    (C : Matrix (Fin k') (Fin n) F) (R'' : Set (Fin k' → F)) (D : Matrix (Fin r) (Fin n) F)
    (rep : (Fin r → F) → Fin n → F) (hrep : ∀ σ, D *ᵥ rep σ = σ)
    (hB : ∀ i, B i ∈ Submodule.span F (Set.range D))
    (hC : ∀ i, C i ∈ Submodule.span F (Set.range D)) :
    {x | B *ᵥ x ∈ R} ∩ {x | C *ᵥ x ∈ R''} =
      {x | D *ᵥ x ∈ {σ | B *ᵥ rep σ ∈ R ∧ C *ᵥ rep σ ∈ R''}} := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  rw [mulVec_eq_of_rows_mem_span D B hB (hrep (D *ᵥ x)).symm,
    mulVec_eq_of_rows_mem_span D C hC (hrep (D *ᵥ x)).symm]

end Atoms

/-! ## Decomposable nodes: conjunction and determinism (Lemma `lem:vtops`) -/

section Decomposable

variable {α β ι ι' : Type*}

/-- Conjunction of two decomposable nodes `⋃ᵢ Pᵢ × Qᵢ` and `⋃ⱼ P'ⱼ × Q'ⱼ`. -/
theorem conj_iUnion_prod (P : ι → Set α) (Q : ι → Set β) (P' : ι' → Set α) (Q' : ι' → Set β) :
    (⋃ i, P i ×ˢ Q i) ∩ (⋃ j, P' j ×ˢ Q' j) =
      ⋃ p : ι × ι', (P p.1 ∩ P' p.2) ×ˢ (Q p.1 ∩ Q' p.2) := by
  ext ⟨a, b⟩
  simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_prod, Prod.exists]
  constructor
  · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    exact ⟨i, j, ⟨hi.1, hj.1⟩, ⟨hi.2, hj.2⟩⟩
  · rintro ⟨i, j, ⟨h1, h2⟩, ⟨h3, h4⟩⟩
    exact ⟨⟨i, h1, h3⟩, ⟨j, h2, h4⟩⟩

/-- Conjunction preserves determinism (pairwise disjoint terms). -/
theorem conj_pairwise_disjoint (P : ι → Set α) (Q : ι → Set β) (P' : ι' → Set α)
    (Q' : ι' → Set β) (h : Pairwise fun i i' => Disjoint (P i ×ˢ Q i) (P i' ×ˢ Q i'))
    (h' : Pairwise fun j j' => Disjoint (P' j ×ˢ Q' j) (P' j' ×ˢ Q' j')) :
    Pairwise fun p p' : ι × ι' => Disjoint ((P p.1 ∩ P' p.2) ×ˢ (Q p.1 ∩ Q' p.2))
      ((P p'.1 ∩ P' p'.2) ×ˢ (Q p'.1 ∩ Q' p'.2)) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ hne
  rw [Set.disjoint_left]
  rintro ⟨a, b⟩ ⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩⟩ ⟨⟨ha1', ha2'⟩, ⟨hb1', hb2'⟩⟩
  by_cases hi : i = i'
  · subst hi
    have hj : j ≠ j' := fun hj => hne (by rw [hj])
    exact Set.disjoint_left.mp (h' hj) ⟨ha2, hb2⟩ ⟨ha2', hb2'⟩
  · exact Set.disjoint_left.mp (h hi) ⟨ha1, hb1⟩ ⟨ha1', hb1'⟩

/-- Pullback by a leaf-local (product) map is the product of the preimages. -/
theorem preimage_prod_map {α' β' : Type*} (f : α' → α) (g : β' → β) (P : Set α) (Q : Set β) :
    Prod.map f g ⁻¹' (P ×ˢ Q) = (f ⁻¹' P) ×ˢ (g ⁻¹' Q) := rfl

end Decomposable

/-! ## Transfer pullback (Lemma `lem:transfer`) -/

section Transfer

variable {nL nR rL rR : ℕ} {ι : Type*}

/-- **Lemma `lem:transfer` (008b).** Let an affine map on `𝔽₂^{X_L} × 𝔽₂^{X_R}` have blocks
`A_LL, A_LR = U_LR V_LR, A_RL = U_RL V_RL, A_RR` and offsets `b_L, b_R`, and let
`H = ⋃ᵢ Pᵢ × Qᵢ`. Then the preimage of `H` is the union over `i` and the transfer syndromes
`α = V_RL x_L`, `β = V_LR x_R` of the products displayed, and the terms are pairwise disjoint when
the terms of `H` are. -/
theorem transfer_pullback (ALL : Matrix (Fin nL) (Fin nL) F) (ARR : Matrix (Fin nR) (Fin nR) F)
    (ULR : Matrix (Fin nL) (Fin rR) F) (VLR : Matrix (Fin rR) (Fin nR) F)
    (URL : Matrix (Fin nR) (Fin rL) F) (VRL : Matrix (Fin rL) (Fin nL) F)
    (bL : Fin nL → F) (bR : Fin nR → F) (P : ι → Set (Fin nL → F)) (Q : ι → Set (Fin nR → F)) :
    let T : (Fin nL → F) × (Fin nR → F) → (Fin nL → F) × (Fin nR → F) := fun x =>
      (ALL *ᵥ x.1 + (ULR * VLR) *ᵥ x.2 + bL, (URL * VRL) *ᵥ x.1 + ARR *ᵥ x.2 + bR)
    let term : ι × (Fin rL → F) × (Fin rR → F) → Set ((Fin nL → F) × (Fin nR → F)) := fun t =>
      {xL | VRL *ᵥ xL = t.2.1 ∧ ALL *ᵥ xL + ULR *ᵥ t.2.2 + bL ∈ P t.1} ×ˢ
        {xR | VLR *ᵥ xR = t.2.2 ∧ ARR *ᵥ xR + URL *ᵥ t.2.1 + bR ∈ Q t.1}
    (T ⁻¹' ⋃ i, P i ×ˢ Q i = ⋃ t, term t) ∧
      ((Pairwise fun i j => Disjoint (P i ×ˢ Q i) (P j ×ˢ Q j)) →
        Pairwise fun t t' => Disjoint (term t) (term t')) := by
  intro T term
  have hT : ∀ x : (Fin nL → F) × (Fin nR → F), T x =
      (ALL *ᵥ x.1 + ULR *ᵥ (VLR *ᵥ x.2) + bL, ARR *ᵥ x.2 + URL *ᵥ (VRL *ᵥ x.1) + bR) := by
    intro x
    simp only [T, ← mulVec_mulVec]
    congr 1
    abel
  refine ⟨?_, ?_⟩
  · ext ⟨xL, xR⟩
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_prod, hT, term, Set.mem_ofPred_eq,
      Prod.exists]
    constructor
    · rintro ⟨i, hP, hQ⟩
      exact ⟨i, _, _, ⟨rfl, hP⟩, ⟨rfl, hQ⟩⟩
    · rintro ⟨i, α, β, ⟨rfl, hP⟩, ⟨rfl, hQ⟩⟩
      exact ⟨i, hP, hQ⟩
  · intro hdisj ⟨i, α, β⟩ ⟨i', α', β'⟩ hne
    rw [Set.disjoint_left]
    rintro ⟨xL, xR⟩ ⟨⟨hα, hP⟩, ⟨hβ, hQ⟩⟩ ⟨⟨hα', hP'⟩, ⟨hβ', hQ'⟩⟩
    simp only at hα hP hβ hQ hα' hP' hβ' hQ'
    have e1 : α = α' := hα.symm.trans hα'
    have e2 : β = β' := hβ.symm.trans hβ'
    subst e1 e2
    have hi : i ≠ i' := fun h => hne (by rw [h])
    exact Set.disjoint_left.mp (hdisj hi) (Set.mk_mem_prod hP hQ) (Set.mk_mem_prod hP' hQ')

end Transfer

/-! ## The equality barrier (Proposition `prop:pfeq`) -/

section Equality

variable {α : Type*}

/-- A rectangle `A × B` inside the diagonal with `B` nonempty has at most one point in `A`. -/
theorem rect_subset_diag_subsingleton {A B : Set α} (h : A ×ˢ B ⊆ {p | p.1 = p.2})
    (hB : B.Nonempty) : A.Subsingleton := by
  obtain ⟨y, hy⟩ := hB
  intro a ha a' ha'
  have h1 : a = y := h (Set.mk_mem_prod ha hy)
  have h2 : a' = y := h (Set.mk_mem_prod ha' hy)
  rw [h1, h2]

/-- An affine set `{x : B x = s}` with at most one point forces `x ↦ B x` to be injective
(`B` has full column rank `n`). -/
theorem injective_of_coset_subsingleton {n r : ℕ} (B : Matrix (Fin r) (Fin n) F) (s : Fin r → F)
    (hne : {x | B *ᵥ x = s}.Nonempty) (hsub : {x | B *ᵥ x = s}.Subsingleton) :
    Function.Injective B.mulVec := by
  obtain ⟨x0, hx0⟩ := hne
  intro x x' hxx'
  have hmem : x0 + (x - x') ∈ {x | B *ᵥ x = s} := by
    simp only [Set.mem_ofPred_eq] at hx0 ⊢
    rw [mulVec_add, mulVec_sub, hxx', sub_self, add_zero, hx0]
  have := hsub hmem hx0
  have h2 : x - x' = 0 := by simpa using this
  exact sub_eq_zero.mp h2

/-- **Proposition `prop:pfeq` (008b), rank part.** If a nonempty accepting piece row
`{x₁ : B₁ x₁ = s₁} × {x₂ : B₂ x₂ = s₂}` lies inside `{x₁ = x₂}`, then both `B₁` and `B₂` are
injective, i.e. `r₁ = r₂ = n`. -/
theorem piece_injective {n r₁ r₂ : ℕ} (B₁ : Matrix (Fin r₁) (Fin n) F)
    (B₂ : Matrix (Fin r₂) (Fin n) F) (s₁ : Fin r₁ → F) (s₂ : Fin r₂ → F)
    (h : {x | B₁ *ᵥ x = s₁} ×ˢ {x | B₂ *ᵥ x = s₂} ⊆ {p | p.1 = p.2})
    (hne : ({x | B₁ *ᵥ x = s₁} ×ˢ {x | B₂ *ᵥ x = s₂}).Nonempty) :
    Function.Injective B₁.mulVec ∧ Function.Injective B₂.mulVec := by
  obtain ⟨⟨a, b⟩, ha, hb⟩ := hne
  refine ⟨injective_of_coset_subsingleton B₁ s₁ ⟨a, ha⟩
    (rect_subset_diag_subsingleton h ⟨b, hb⟩), ?_⟩
  apply injective_of_coset_subsingleton B₂ s₂ ⟨b, hb⟩
  have h' : {x | B₂ *ᵥ x = s₂} ×ˢ {x | B₁ *ᵥ x = s₁} ⊆ {p | p.1 = p.2} := by
    rintro ⟨y, x⟩ ⟨hy, hx⟩
    exact (h (Set.mk_mem_prod hx hy)).symm
  exact rect_subset_diag_subsingleton h' ⟨a, ha⟩

/-- **Proposition `prop:pfeq` (008b), counting part.** Covering the diagonal of `α × α` by
rectangles contained in it needs at least `|α|` rectangles (for `α = 𝔽₂^n`: `2^n` relation rows). -/
theorem diag_cover_card [Fintype α] {ι : Type*} [Fintype ι] (A B : ι → Set α)
    (hsub : ∀ i, A i ×ˢ B i ⊆ {p | p.1 = p.2})
    (hcov : {p : α × α | p.1 = p.2} ⊆ ⋃ i, A i ×ˢ B i) : Fintype.card α ≤ Fintype.card ι := by
  classical
  have hchoose : ∀ a : α, ∃ i, a ∈ A i ∧ a ∈ B i := by
    intro a
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov (show (a, a) ∈ {p : α × α | p.1 = p.2} from rfl))
    exact ⟨i, hi.1, hi.2⟩
  choose f hf using hchoose
  apply Fintype.card_le_of_injective f
  intro a a' h
  have h1 := (hf a).1
  have h2 := (hf a').2
  rw [h] at h1
  exact hsub (f a') (Set.mk_mem_prod h1 h2)

/-- **Proposition `prop:ordeq` (008b), core.** If a bank automaton is in state `σ a` after reading
the first half `a` (layer `j`), and acceptance is a function `acc (σ a) b` of that state and the
second half `b`, and the automaton accepts exactly when `a = b`, then `σ` is injective: layer `j`
has at least `2^n` states. -/
theorem ordered_equality_states {n : ℕ} {St : Type*} [Finite St] (σ : (Fin n → F) → St)
    (acc : St → (Fin n → F) → Prop) (h : ∀ a b, acc (σ a) b ↔ a = b) :
    Function.Injective σ ∧ 2 ^ n ≤ Nat.card St := by
  have hinj : Function.Injective σ := by
    intro a a' haa'
    exact (h a' a).mp (by rw [← haa']; exact (h a a).mpr rfl) |>.symm
  refine ⟨hinj, ?_⟩
  have hfin : Nat.card (Fin n → F) = 2 ^ n := by simp
  rw [← hfin]
  exact Nat.card_le_card_of_injective σ hinj

end Equality

/-! ## The inner-product barrier (Lemma `lem:rect`, Proposition `prop:vtip`) -/

section InnerProduct

variable {n : ℕ}

lemma ncard_submodule (U : Submodule F (Fin n → F)) :
    (U : Set (Fin n → F)).ncard = 2 ^ finrank F U := by
  rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe, Module.natCard_eq_pow_finrank (K := F),
    Nat.card_zmod]

/-- **Lemma `lem:rect` (008b).** If `a ⬝ b = 1` for all `a ∈ A`, `b ∈ B` (subsets of `𝔽₂^n`), then
`|A| |B| ≤ 2^{n-1}`. -/
theorem rect_card_le (A B : Set (Fin n → F)) (h : ∀ a ∈ A, ∀ b ∈ B, a ⬝ᵥ b = 1) :
    A.ncard * B.ncard ≤ 2 ^ (n - 1) := by
  rcases A.eq_empty_or_nonempty with hA | ⟨a0, ha0⟩
  · simp [hA]
  rcases B.eq_empty_or_nonempty with hB | ⟨b0, hb0⟩
  · simp [hB]
  set U := Submodule.span F ((fun a => a - a0) '' A)
  set W := Submodule.span F A
  -- every element of `U` is orthogonal to `b0`
  have hUb0 : ∀ u ∈ U, u ⬝ᵥ b0 = 0 := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      rw [sub_dotProduct, h a ha b0 hb0, h a0 ha0 b0 hb0, sub_self]
    | zero => simp
    | add x y _ _ hx hy => rw [add_dotProduct, hx, hy, add_zero]
    | smul t x _ hx => rw [smul_dotProduct, hx, smul_zero]
  have ha0U : a0 ∉ U := by
    intro hmem
    have := hUb0 a0 hmem
    rw [h a0 ha0 b0 hb0] at this
    exact one_ne_zero this
  have hUW : U < W := by
    refine lt_of_le_of_ne (Submodule.span_le.mpr ?_) ?_
    · rintro _ ⟨a, ha, rfl⟩
      exact W.sub_mem (Submodule.subset_span ha) (Submodule.subset_span ha0)
    · intro hEq
      exact ha0U (hEq ▸ Submodule.subset_span ha0)
  have hdim : finrank F U < finrank F W := Submodule.finrank_lt_finrank_of_lt hUW
  -- |A| ≤ |U|
  have hA : A.ncard ≤ 2 ^ finrank F U := by
    rw [← ncard_submodule U]
    apply Set.ncard_le_ncard_of_injOn (fun a => a - a0)
    · intro a ha
      exact Submodule.subset_span ⟨a, ha, rfl⟩
    · intro a _ a' _ haa'
      simpa using haa'
  -- |B| ≤ |W^⊥|
  have hB : B.ncard ≤ 2 ^ finrank F (dotOrth W) := by
    rw [← ncard_submodule (dotOrth W)]
    apply Set.ncard_le_ncard_of_injOn (fun b => b - b0)
    · intro b hb
      simp only [SetLike.mem_coe, mem_dotOrth]
      intro w hw
      induction hw using Submodule.span_induction with
      | mem x hx => rw [dotProduct_sub, h x hx b hb, h x hx b0 hb0, sub_self]
      | zero => simp
      | add x y _ _ hx hy => rw [add_dotProduct, hx, hy, add_zero]
      | smul t x _ hx => rw [smul_dotProduct, hx, smul_zero]
    · intro b _ b' _ hbb'
      simpa using hbb'
  have hsum := finrank_add_finrank_dotOrth W
  simp only [Fintype.card_fin] at hsum
  calc A.ncard * B.ncard ≤ 2 ^ finrank F U * 2 ^ finrank F (dotOrth W) := Nat.mul_le_mul hA hB
    _ = 2 ^ (finrank F U + finrank F (dotOrth W)) := (pow_add _ _ _).symm
    _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- For `a ≠ 0` exactly half of the vectors `b` have `a ⬝ b = 1`. -/
theorem card_dot_eq_one {a : Fin n → F} (ha : a ≠ 0) :
    (Finset.univ.filter fun b : Fin n → F => a ⬝ᵥ b = 1).card = 2 ^ (n - 1) := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra hc
    push Not at hc
    exact ha (funext hc)
  have hai : a i = 1 := by
    rcases F_cases (a i) with h | h
    · exact absurd h hi
    · exact h
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.2
  set e : Fin n → F := Pi.single i 1
  have hae : a ⬝ᵥ e = 1 := by simp [e, dotProduct_single, hai]
  have hee : ∀ b : Fin n → F, b + e + e = b := by
    intro b
    rw [add_assoc, show e + e = 0 from funext fun j => CharTwo.add_self_eq_zero (e j), add_zero]
  -- the involution `b ↦ b + e` swaps the two classes
  have hswap : (Finset.univ.filter fun b : Fin n → F => a ⬝ᵥ b = 1).card =
      (Finset.univ.filter fun b : Fin n → F => ¬ a ⬝ᵥ b = 1).card := by
    apply Finset.card_nbij' (fun b => b + e) (fun b => b + e)
    · intro b hb
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hb ⊢
      rw [dotProduct_add, hb, hae]
      decide
    · intro b hb
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hb ⊢
      rw [dotProduct_add, hae]
      rcases F_cases (a ⬝ᵥ b) with h | h
      · rw [h]; decide
      · exact absurd h hb
    · intro b _; exact hee b
    · intro b _; exact hee b
  have htot := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n → F))) (fun b => a ⬝ᵥ b = 1)
  rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin, ← hswap] at htot
  have : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']; congr 1; omega
  omega

/-- The number of pairs with `a ⬝ b = 1` is `(2^n - 1) 2^{n-1}`. -/
theorem card_ip_eq_one :
    (Finset.univ.filter fun p : (Fin n → F) × (Fin n → F) => p.1 ⬝ᵥ p.2 = 1).card =
      (2 ^ n - 1) * 2 ^ (n - 1) := by
  classical
  rw [Finset.card_filter, Fintype.sum_prod_type]
  simp only [← Finset.card_filter]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : Fin n → F))]
  have h0 : (Finset.univ.filter fun b : Fin n → F => (0 : Fin n → F) ⬝ᵥ b = 1).card = 0 := by
    simp
  rw [h0, add_zero, Finset.sum_congr rfl (fun a ha => card_dot_eq_one (Finset.ne_of_mem_erase ha)),
    Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fun, ZMod.card, Fintype.card_fin, smul_eq_mul]

/-- **Proposition `prop:vtip` (008b).** If the root of the vtree separates `a` from `b`, the root
terms of a VT-diagram for `{(a, b) : a ⬝ b = 1}` are rectangles contained in this set and covering
it; any such cover has at least `2^n - 1` rectangles. -/
theorem ip_rect_cover_card {ι : Type*} [Fintype ι] (A B : ι → Set (Fin n → F))
    (hsub : ∀ i, A i ×ˢ B i ⊆ {p | p.1 ⬝ᵥ p.2 = 1})
    (hcov : {p : (Fin n → F) × (Fin n → F) | p.1 ⬝ᵥ p.2 = 1} ⊆ ⋃ i, A i ×ˢ B i) :
    2 ^ n - 1 ≤ Fintype.card ι := by
  classical
  have hS : {p : (Fin n → F) × (Fin n → F) | p.1 ⬝ᵥ p.2 = 1}.ncard = (2 ^ n - 1) * 2 ^ (n - 1) := by
    rw [← card_ip_eq_one, ← Set.ncard_coe_finset]
    congr 1
    ext p
    simp
  have h1 : (2 ^ n - 1) * 2 ^ (n - 1) ≤ ∑ i, (A i ×ˢ B i).ncard := by
    rw [← hS]
    exact le_trans (Set.ncard_le_ncard hcov (Set.toFinite _))
      (Set.ncard_iUnion_le_of_fintype _)
  have h2 : ∀ i, (A i ×ˢ B i).ncard ≤ 2 ^ (n - 1) := by
    intro i
    rw [Set.ncard_prod]
    exact rect_card_le (A i) (B i) fun a ha b hb => hsub i (Set.mk_mem_prod ha hb)
  have h3 : ∑ i, (A i ×ˢ B i).ncard ≤ Fintype.card ι * 2 ^ (n - 1) := by
    calc _ ≤ ∑ _i : ι, 2 ^ (n - 1) := Finset.sum_le_sum fun i _ => h2 i
      _ = _ := by simp
  exact Nat.le_of_mul_le_mul_right (h1.trans h3) (by positivity)

end InnerProduct

end GC.SCLadder
