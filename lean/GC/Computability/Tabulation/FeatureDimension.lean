import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Perm.Closure
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.GroupTheory.OrderOfElement

/-!
# Barriers: extensional summaries and feature dimension (manuscript 010e, Sections 4 and 5)

The state set is `X = Fin m` with `m = n + 2 ≥ 2` (the paper takes `m = 2^q`, `q ≥ 1`), the
cycle `c = finRotate m` (`x ↦ x + 1 mod m`) and the transposition `τ = (0 1)`.
-/

namespace GC.Tabulation

open Module Matrix

/-- **Proposition 5.1 (independent-interface injectivity).** If a summary `E : {0,1}^q → Σ` has
a decoder `D` with `D(E(u)) = u` for all `u`, then `|Σ| ≥ 2^q`. -/
theorem summary_card_ge {q : ℕ} {S : Type*} [Fintype S] (E : (Fin q → Bool) → S)
    (D : S → (Fin q → Bool)) (hDE : ∀ u, D (E u) = u) : 2 ^ q ≤ Fintype.card S := by
  have hinj : Function.Injective E := fun u v h => by rw [← hDE u, ← hDE v, h]
  have := Fintype.card_le_of_injective E hinj
  simpa [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using this

/-- The cycle `c(x) = x + 1 mod m` on `Fin (n + 2)`. -/
def cyc (n : ℕ) : Equiv.Perm (Fin (n + 2)) := finRotate (n + 2)

/-- The transposition `τ` of `0` and `1`. -/
def tau (n : ℕ) : Equiv.Perm (Fin (n + 2)) := Equiv.swap 0 1

/-- **Lemma 4.2 (generation).** `c` and `τ` generate the symmetric group. -/
theorem cyc_tau_generate (n : ℕ) :
    Subgroup.closure ({cyc n, tau n} : Set (Equiv.Perm (Fin (n + 2)))) = ⊤ := by
  have h := Equiv.Perm.closure_cycle_adjacent_swap (isCycle_finRotate (n := n))
    (support_finRotate (n := n)) 0
  have h1 : finRotate (n + 2) 0 = 1 := by
    ext; simp
  rw [h1] at h
  exact h

section Observable

variable {K : Type*} [Field K] {n : ℕ}

/-- Indicator vectors `e_a`. -/
def ind (a : Fin (n + 2)) : Fin (n + 2) → K := fun x => if x = a then 1 else 0

lemma ind_comp (a : Fin (n + 2)) (σ : Equiv.Perm (Fin (n + 2))) :
    (fun x => (ind a : Fin (n + 2) → K) (σ x)) = ind (σ⁻¹ a) := by
  funext x
  simp only [ind]
  congr 1
  apply propext
  rw [Equiv.Perm.eq_inv_iff_eq]

/-- If a subspace of `K^X` is invariant under `f ↦ f ∘ c` and `f ↦ f ∘ τ`, it is invariant under
`f ↦ f ∘ π` for every permutation `π`. -/
lemma invariant_all (V : Submodule K (Fin (n + 2) → K))
    (hc : ∀ f ∈ V, (fun x => f (cyc n x)) ∈ V) (hτ : ∀ f ∈ V, (fun x => f (tau n x)) ∈ V)
    (π : Equiv.Perm (Fin (n + 2))) : ∀ f ∈ V, (fun x => f (π x)) ∈ V := by
  let S : Submonoid (Equiv.Perm (Fin (n + 2))) :=
    { carrier := {π | ∀ f ∈ V, (fun x => f (π x)) ∈ V}
      mul_mem' := by
        intro a b ha hb f hf
        exact hb _ (ha f hf)
      one_mem' := by
        intro f hf
        simpa using hf }
  have hS : ∀ σ ∈ Subgroup.closure ({cyc n, tau n} : Set (Equiv.Perm (Fin (n + 2)))), σ ∈ S := by
    intro σ hσ
    induction hσ using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact hc
      · exact hτ
    | one => exact S.one_mem
    | mul x y _ _ hx hy => exact S.mul_mem hx hy
    | inv x _ hx =>
      have hpos : 0 < orderOf x := orderOf_pos x
      have hinv : x⁻¹ = x ^ (orderOf x - 1) := by
        rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel hpos,
          pow_orderOf_eq_one]
      rw [hinv]
      exact S.pow_mem hx _
  exact hS π (by rw [cyc_tau_generate]; trivial)

variable (K n) in
/-- The sum functional `f ↦ ∑_x f(x)`. -/
def sumFun : (Fin (n + 2) → K) →ₗ[K] K where
  toFun f := ∑ i, f i
  map_add' f g := by simp [Finset.sum_add_distrib]
  map_smul' c f := by simp [Finset.mul_sum]

/-- The sum-zero hyperplane has dimension `m - 1`. -/
lemma finrank_sumZero : finrank K (LinearMap.ker (sumFun K n)) = n + 1 := by
  set s := sumFun K n
  have hs : ∀ f, s f = ∑ i, f i := fun f => rfl
  have hsurj : LinearMap.range s = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro k
    refine ⟨fun x => if x = 0 then k else 0, ?_⟩
    rw [hs]; simp
  have := LinearMap.finrank_range_add_finrank_ker s
  rw [hsurj, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at this
  omega

/-- **Theorem 4.4 (observable features).** Let `V ⊆ K^X` be invariant under `f ↦ f ∘ c` and
`f ↦ f ∘ τ`. If `V` contains a nonconstant function, then `dim V ≥ m - 1`. -/
theorem observable_dim (V : Submodule K (Fin (n + 2) → K))
    (hc : ∀ f ∈ V, (fun x => f (cyc n x)) ∈ V) (hτ : ∀ f ∈ V, (fun x => f (tau n x)) ∈ V)
    (hnc : ∃ f ∈ V, ∃ i j, f i ≠ f j) : n + 1 ≤ finrank K V := by
  obtain ⟨f, hfV, i, j, hij⟩ := hnc
  have hinv := invariant_all V hc hτ
  have hne : i ≠ j := fun h => hij (h ▸ rfl)
  -- `e_i - e_j ∈ V`
  have hdiff : (ind i - ind j : Fin (n + 2) → K) ∈ V := by
    have h1 : (f - fun x => f (Equiv.swap i j x)) ∈ V := V.sub_mem hfV (hinv _ f hfV)
    have h2 : (f - fun x => f (Equiv.swap i j x)) = (f i - f j) • (ind i - ind j) := by
      funext x
      simp only [Pi.sub_apply, Pi.smul_apply, ind, smul_eq_mul]
      by_cases hxi : x = i
      · subst hxi; simp [hne]
      · by_cases hxj : x = j
        · subst hxj; simp [hne.symm, Equiv.swap_apply_right]
        · simp [hxi, hxj, Equiv.swap_apply_of_ne_of_ne hxi hxj]
    rw [h2] at h1
    have := V.smul_mem (f i - f j)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hij), one_smul] at this
  -- all `e_a - e_b ∈ V`
  have hall : ∀ a b : Fin (n + 2), a ≠ b → (ind a - ind b : Fin (n + 2) → K) ∈ V := by
    intro a b hab
    -- a permutation sending `a ↦ i` and `b ↦ j`
    obtain ⟨σ, hσa, hσb⟩ : ∃ σ : Equiv.Perm (Fin (n + 2)), σ a = i ∧ σ b = j := by
      have hb' : Equiv.swap a i b ≠ i := by
        intro h
        have := congrArg (Equiv.swap a i) h
        rw [Equiv.swap_apply_self, Equiv.swap_apply_right] at this
        exact hab this.symm
      refine ⟨Equiv.swap (Equiv.swap a i b) j * Equiv.swap a i, ?_, ?_⟩
      · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
        exact Equiv.swap_apply_of_ne_of_ne hb'.symm hne
      · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    have := hinv σ _ hdiff
    have e : (fun x => (ind i - ind j : Fin (n + 2) → K) (σ x)) = ind a - ind b := by
      have h1 := ind_comp (K := K) i σ
      have h2 := ind_comp (K := K) j σ
      funext x
      simp only [Pi.sub_apply]
      rw [congrFun h1 x, congrFun h2 x, ← hσa, ← hσb]
      simp
    rwa [e] at this
  -- the sum-zero hyperplane lies in `V`
  have hle : LinearMap.ker (sumFun K n) ≤ V := by
    intro g hg
    have hsum : ∑ x, g x = 0 := LinearMap.mem_ker.mp hg
    have hg' : g = ∑ a, g a • (ind a - ind 0 : Fin (n + 2) → K) := by
      funext x
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
      rw [← Finset.sum_mul, hsum, zero_mul, sub_zero]
      simp [ind]
    rw [hg']
    refine V.sum_mem fun a _ => V.smul_mem _ ?_
    by_cases ha : a = 0
    · subst ha; simp
    · exact hall a 0 ha
  have := Submodule.finrank_mono hle
  rw [finrank_sumZero] at this
  exact this

/-- The span of a finite family is invariant under `f ↦ f ∘ π` as soon as each member is mapped
into the span. -/
lemma span_invariant {s : ℕ} (ψ : Fin s → Fin (n + 2) → K) (π : Equiv.Perm (Fin (n + 2)))
    (h : ∀ k, (fun x => ψ k (π x)) ∈ Submodule.span K (Set.range ψ)) :
    ∀ f ∈ Submodule.span K (Set.range ψ), (fun x => f (π x)) ∈ Submodule.span K (Set.range ψ) := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem g hg => obtain ⟨k, rfl⟩ := hg; exact h k
  | zero => exact Submodule.zero_mem _
  | add f g _ _ hf hg => exact Submodule.add_mem _ hf hg
  | smul a f _ hf => exact Submodule.smul_mem _ a hf

/-- **Theorem 4.3 (injective features), linear case.** If `Φ : X → K^r` is injective and there
are matrices `M_c, M_τ` with `Φ(c x) = M_c Φ(x)` and `Φ(τ x) = M_τ Φ(x)`, then `r ≥ m - 1`. -/
theorem features_dim_linear {r : ℕ} (Φ : Fin (n + 2) → Fin r → K) (hΦ : Function.Injective Φ)
    (Mc Mτ : Matrix (Fin r) (Fin r) K) (hc : ∀ x, Φ (cyc n x) = Mc *ᵥ Φ x)
    (hτ : ∀ x, Φ (tau n x) = Mτ *ᵥ Φ x) : n + 1 ≤ r := by
  let ψ : Fin r → Fin (n + 2) → K := fun k x => Φ x k
  let V := Submodule.span K (Set.range ψ)
  have hmap : ∀ (M : Matrix (Fin r) (Fin r) K) (π : Equiv.Perm (Fin (n + 2))),
      (∀ x, Φ (π x) = M *ᵥ Φ x) → ∀ k, (fun x => ψ k (π x)) ∈ V := by
    intro M π hM k
    have : (fun x => ψ k (π x)) = ∑ l, M k l • ψ l := by
      funext x
      simp only [ψ, hM, Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [this]
    exact Submodule.sum_mem _ fun l _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
  have hnc : ∃ f ∈ V, ∃ i j, f i ≠ f j := by
    have h01 : Φ 0 ≠ Φ 1 := fun h => by
      have := hΦ h
      simp at this
    obtain ⟨k, hk⟩ := Function.ne_iff.mp h01
    exact ⟨ψ k, Submodule.subset_span ⟨k, rfl⟩, 0, 1, hk⟩
  have h1 := observable_dim V (span_invariant ψ _ (hmap Mc _ hc))
    (span_invariant ψ _ (hmap Mτ _ hτ)) hnc
  have h2 : finrank K V ≤ r := by
    exact (finrank_range_le_card (R := K) (b := ψ)).trans_eq (Fintype.card_fin r)
  omega

/-- **Theorem 4.3 (injective features), affine case.** With affine updates
`Φ(c x) = M_c Φ(x) + u_c` and `Φ(τ x) = M_τ Φ(x) + u_τ`, `r ≥ m - 2`. -/
theorem features_dim_affine {r : ℕ} (Φ : Fin (n + 2) → Fin r → K) (hΦ : Function.Injective Φ)
    (Mc Mτ : Matrix (Fin r) (Fin r) K) (uc uτ : Fin r → K)
    (hc : ∀ x, Φ (cyc n x) = Mc *ᵥ Φ x + uc) (hτ : ∀ x, Φ (tau n x) = Mτ *ᵥ Φ x + uτ) :
    n ≤ r := by
  -- adjoin the constant coordinate `1`
  let Φ' : Fin (n + 2) → Fin (r + 1) → K := fun x => Fin.lastCases 1 (Φ x)
  have hΦ' : Function.Injective Φ' := by
    intro x y h
    apply hΦ
    funext k
    have := congrFun h k.castSucc
    simpa [Φ'] using this
  let M' : Matrix (Fin r) (Fin r) K → (Fin r → K) → Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
    fun M u i j => Fin.lastCases (Fin.lastCases 1 (fun _ => 0) j)
      (fun i' => Fin.lastCases (u i') (fun j' => M i' j') j) i
  have hM' : ∀ (M : Matrix (Fin r) (Fin r) K) (u : Fin r → K) (π : Equiv.Perm (Fin (n + 2))),
      (∀ x, Φ (π x) = M *ᵥ Φ x + u) → ∀ x, Φ' (π x) = M' M u *ᵥ Φ' x := by
    intro M u π hM x
    funext i
    induction i using Fin.lastCases with
    | last => simp [Φ', M', Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]
    | cast i =>
      simp [Φ', M', Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, hM, add_comm]
  have := features_dim_linear Φ' hΦ' (M' Mc uc) (M' Mτ uτ) (hM' _ _ _ hc) (hM' _ _ _ hτ)
  omega

end Observable

end GC.Tabulation
