import GC.Computability.Portals.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Every hypergraph is an A5 proof-support system (manuscript 005b)

* `selector_exists`, `a5_selector`: Lemma "61-probe collision selector". For every finite group
  `G` with `n` elements there are `n + 1` unary maps `T₀, …, Tₙ`, each the identity or a
  constant (so each is induced by a group term), whose values at every `g` contain exactly one
  colliding pair, and that pair determines `g`. For `A₅` this gives 61 probes.
* `realization`: Theorem "Arbitrary support-hypergraph realization". For a selector `T`, a
  nontrivial group and any hyperedge `e`, the block `T_k(a_e)`, `a_e = ∏_{i ∈ e} h_i` (in
  increasing order of `i`), has exactly one colliding pair, that pair determines `a_e`, and the
  essential support of the colliding-pair function is exactly `e`.
* `star_block_values`: Theorem "Star-transversal barrier" (i): for a fixed context the colliding
  pair of a block takes `|G|` distinct values as a single anchor of its edge varies.
* `charging`: Lemma "Charging", with the bound on the number of phases and on the total depth.

The size count `O(∑|e| + |E|)` and the complexity statements are not formalized. Terms are
replaced by the functions they induce (as in the paper's own checks); our selector uses only the
identity and constants, so polynomial completeness (Maurer–Rhodes) is not needed for it.
-/

namespace GC.Portals

section Hypergraph

variable {G : Type*} [Group G] [DecidableEq G]

set_option linter.unusedSectionVars false

/-- The colliding pairs `i < j` with `z i = z j` of a block of `k` values. -/
def collisions {k : ℕ} (z : Fin k → G) : Finset (Fin k × Fin k) :=
  Finset.univ.filter (fun p => p.1 < p.2 ∧ z p.1 = z p.2)

/-- A collision selector: for every `g` the block `(T i g)_i` has exactly one colliding pair,
and the set of colliding pairs determines `g`. -/
def IsSelector {k : ℕ} (T : Fin k → G → G) : Prop :=
  (∀ g, (collisions (fun i => T i g)).card = 1) ∧
    Function.Injective (fun g => collisions (fun i => T i g))

/-- The product `a_e = h_{i₁} ⋯ h_{i_r}` of the anchors of the edge `e = {i₁ < ⋯ < i_r}`. -/
def edgeProduct {t : ℕ} (e : Finset (Fin t)) (h : Fin t → G) : G :=
  ((e.sort (· ≤ ·)).map h).prod

/-- The colliding pairs of the selector block of the edge `e`: the function `F_e`. -/
def blockCollisions {k t : ℕ} (T : Fin k → G → G) (e : Finset (Fin t)) (h : Fin t → G) :
    Finset (Fin k × Fin k) :=
  collisions (fun i => T i (edgeProduct e h))

/-- Anchor `i` is essential for `F` if two assignments that differ only at `i` give different
values of `F`. -/
def Essential {t : ℕ} {β : Type*} (F : (Fin t → G) → β) (i : Fin t) : Prop :=
  ∃ h h' : Fin t → G, (∀ j, j ≠ i → h j = h' j) ∧ F h ≠ F h'

/-- The probes of the explicit selector: `T₀ = id` and `T_{j+1}` is the constant `σ⁻¹ j`. -/
def probe {n : ℕ} (σ : G ≃ Fin n) (i : Fin (n + 1)) (g : G) : G :=
  Fin.cases g (fun j => σ.symm j) i

theorem collisions_probe {n : ℕ} (σ : G ≃ Fin n) (g : G) :
    collisions (fun i => probe σ i g) = {(0, (σ g).succ)} := by
  ext ⟨a, b⟩
  simp only [collisions, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
    Prod.mk.injEq]
  constructor
  · rintro ⟨hab, he⟩
    cases a using Fin.cases with
    | zero =>
      cases b using Fin.cases with
      | zero => exact absurd hab (lt_irrefl _)
      | succ j =>
        simp only [probe, Fin.cases_zero, Fin.cases_succ] at he
        refine ⟨rfl, ?_⟩
        rw [he, Equiv.apply_symm_apply]
    | succ j₁ =>
      cases b using Fin.cases with
      | zero => exact absurd hab (Fin.not_lt_zero _)
      | succ j₂ =>
        simp only [probe, Fin.cases_succ] at he
        have := σ.symm.injective he
        subst this
        exact absurd hab (lt_irrefl _)
  · rintro ⟨rfl, rfl⟩
    refine ⟨Fin.succ_pos _, ?_⟩
    simp [probe]

/-- Lemma (collision selector) for an arbitrary finite group with `n` elements: `n + 1` probes,
each the identity or a constant. -/
theorem selector_exists {n : ℕ} (σ : G ≃ Fin n) :
    IsSelector (probe σ) ∧ ∀ i, probe σ i = id ∨ ∃ c, probe σ i = fun _ => c := by
  refine ⟨⟨fun g => by rw [collisions_probe]; rfl, fun g g' hgg' => ?_⟩, fun i => ?_⟩
  · simp only [collisions_probe, Finset.singleton_inj, Prod.mk.injEq, true_and] at hgg'
    exact σ.injective (Fin.succ_injective _ hgg')
  · cases i using Fin.cases with
    | zero => left; funext g; rfl
    | succ j => right; exact ⟨σ.symm j, rfl⟩

theorem card_alternatingGroup_five : Fintype.card (alternatingGroup (Fin 5)) = 60 := by
  rw [card_alternatingGroup, Fintype.card_fin]
  rfl

/-- Lemma (61-probe collision selector) for `A₅`. -/
theorem a5_selector :
    ∃ T : Fin 61 → alternatingGroup (Fin 5) → alternatingGroup (Fin 5),
      IsSelector T ∧ ∀ i, T i = id ∨ ∃ c, T i = fun _ => c :=
  ⟨probe (Fintype.equivFinOfCardEq card_alternatingGroup_five),
    selector_exists (Fintype.equivFinOfCardEq card_alternatingGroup_five)⟩

/-- Changing a single anchor `i ∈ e` acts on `a_e` by `x ↦ L x R`. -/
theorem edgeProduct_update {t : ℕ} (e : Finset (Fin t)) (h : Fin t → G) {i : Fin t}
    (hi : i ∈ e) : ∃ L R : G, ∀ x, edgeProduct e (Function.update h i x) = L * x * R := by
  have hmem : i ∈ e.sort (· ≤ ·) := (Finset.mem_sort _).mpr hi
  obtain ⟨l₁, l₂, hl⟩ := List.append_of_mem hmem
  have hnd := Finset.sort_nodup e (· ≤ ·)
  rw [hl, List.nodup_append, List.nodup_cons] at hnd
  obtain ⟨_, ⟨hi2, _⟩, hsep⟩ := hnd
  have hi1 : i ∉ l₁ := fun h1 => hsep i h1 i List.mem_cons_self rfl
  refine ⟨(l₁.map h).prod, (l₂.map h).prod, fun x => ?_⟩
  unfold edgeProduct
  rw [hl, List.map_append, List.map_cons, List.prod_append, List.prod_cons,
    Function.update_self]
  have e1 : l₁.map (Function.update h i x) = l₁.map h :=
    List.map_congr_left (fun a ha => Function.update_of_ne (fun hai : a = i => hi1 (hai ▸ ha)) _ _)
  have e2 : l₂.map (Function.update h i x) = l₂.map h :=
    List.map_congr_left (fun a ha => Function.update_of_ne (fun hai : a = i => hi2 (hai ▸ ha)) _ _)
  rw [e1, e2, mul_assoc]

/-- `a_e` depends only on the anchors in `e`. -/
theorem edgeProduct_congr {t : ℕ} (e : Finset (Fin t)) (h h' : Fin t → G)
    (hh : ∀ j ∈ e, h j = h' j) : edgeProduct e h = edgeProduct e h' := by
  unfold edgeProduct
  rw [List.map_congr_left (fun a ha => hh a ((Finset.mem_sort _).mp ha))]

/-- For a selector, the block of `e` is injective in every single anchor of `e`. -/
theorem block_injective_anchor {k t : ℕ} {T : Fin k → G → G} (hT : IsSelector T)
    (e : Finset (Fin t)) (h : Fin t → G) {i : Fin t} (hi : i ∈ e) :
    Function.Injective (fun x => blockCollisions T e (Function.update h i x)) := by
  obtain ⟨L, R, hLR⟩ := edgeProduct_update e h hi
  intro x y hxy
  have := hT.2 hxy
  simp only [hLR] at this
  simpa using this

/-- Theorem (arbitrary support-hypergraph realization). -/
theorem realization {k t : ℕ} [Nontrivial G] (T : Fin k → G → G) (hT : IsSelector T)
    (e : Finset (Fin t)) :
    (∀ h, (blockCollisions T e h).card = 1) ∧
    (∀ h h', blockCollisions T e h = blockCollisions T e h' →
      edgeProduct e h = edgeProduct e h') ∧
    (∀ i, Essential (blockCollisions T e) i ↔ i ∈ e) := by
  refine ⟨fun h => hT.1 _, fun h h' hh => hT.2 hh, fun i => ⟨?_, ?_⟩⟩
  · rintro ⟨h, h', hhh', hne⟩
    by_contra hi
    apply hne
    unfold blockCollisions
    rw [edgeProduct_congr e h h' (fun j hj => hhh' j (fun hji => hi (hji ▸ hj)))]
  · intro hi
    obtain ⟨g, hg⟩ := exists_ne (1 : G)
    let h₀ : Fin t → G := fun _ => 1
    refine ⟨Function.update h₀ i 1, Function.update h₀ i g, fun j hj => ?_, fun heq => ?_⟩
    · simp [Function.update_of_ne hj]
    · exact hg (block_injective_anchor hT e h₀ hi heq).symm

/-- Theorem (star-transversal barrier) (i): in the star `e = {0, i}`, for every fixed context,
the colliding pair of the block takes `|G|` distinct values as `h_i` varies. -/
theorem star_block_values [Fintype G] {k t : ℕ} {T : Fin k → G → G} (hT : IsSelector T)
    (i₀ i : Fin t) (h : Fin t → G) :
    (Finset.univ.image (fun x => blockCollisions T {i₀, i} (Function.update h i x))).card =
      Fintype.card G := by
  rw [Finset.card_image_of_injective _ (block_injective_anchor hT _ h (by simp))]
  rfl

end Hypergraph

section Charging

theorem rpow_sub_le_aux {p x y : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hx : 0 < x) (hy : 0 ≤ y)
    (_hyx : y ≤ x) : p * (x - y) * x ^ (p - 1) ≤ x ^ p - y ^ p := by
  have hs : (-1 : ℝ) ≤ y / x - 1 := by
    have : 0 ≤ y / x := div_nonneg hy hx.le
    linarith
  have key := rpow_one_add_le_one_add_mul_self hs hp0 hp1
  rw [show 1 + (y / x - 1) = y / x by ring, Real.div_rpow hy hx.le] at key
  have hxp : 0 < x ^ p := Real.rpow_pos_of_pos hx p
  rw [div_le_iff₀ hxp] at key
  rw [Real.rpow_sub_one hx.ne']
  have : x ^ p / x * (x - y) = x ^ p - y / x * x ^ p := by
    field_simp
  nlinarith [this]

/-- Lemma (charging). Phases on integer sizes `n = x₀ > x₁ > ⋯ > x_k ≥ 1`: phase `i + 1` has depth
`D (i+1) > 0` and reduces the size from `x i` to at most `x i - D (i+1) · (x i)^ε / λ`. Then there
are fewer than `n` reducing phases and their total depth is at most `λ n^{1-ε} / (1 - ε)`; adding
the final phase of depth `D₀` gives the paper's bound. -/
theorem charging (ε lam D₀ : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hlam : 0 < lam) (n k : ℕ)
    (x : ℕ → ℕ) (D : ℕ → ℝ) (hx0 : x 0 = n) (hpos : ∀ i ≤ k, 1 ≤ x i)
    (hD : ∀ i < k, 0 < D (i + 1))
    (hstep : ∀ i < k, (x (i + 1) : ℝ) ≤ x i - D (i + 1) * (x i : ℝ) ^ ε / lam) :
    k < n ∧ ∑ i ∈ Finset.range k, D (i + 1) + D₀ ≤ lam * (n : ℝ) ^ (1 - ε) / (1 - ε) + D₀ := by
  have hdec : ∀ i < k, x (i + 1) < x i := by
    intro i hi
    have h1 := hstep i hi
    have h2 : 0 < D (i + 1) * (x i : ℝ) ^ ε / lam :=
      div_pos (mul_pos (hD i hi) (Real.rpow_pos_of_pos (by exact_mod_cast hpos i hi.le) ε)) hlam
    have : (x (i + 1) : ℝ) < x i := by linarith
    exact_mod_cast this
  refine ⟨?_, ?_⟩
  · have : ∀ i ≤ k, x i + i ≤ n := by
      intro i hi
      induction i with
      | zero => simp [hx0]
      | succ j ih => have := hdec j hi; have := ih (by omega); omega
    have := this k le_rfl
    have := hpos k le_rfl
    omega
  · have hp : 0 < 1 - ε := by linarith
    have hterm : ∀ i < k, D (i + 1) ≤
        lam / (1 - ε) * ((x i : ℝ) ^ (1 - ε) - (x (i + 1) : ℝ) ^ (1 - ε)) := by
      intro i hi
      have hxi : (0 : ℝ) < x i := by exact_mod_cast hpos i hi.le
      have hxi1 : (0 : ℝ) ≤ x (i + 1) := Nat.cast_nonneg _
      have hle : (x (i + 1) : ℝ) ≤ x i := by exact_mod_cast (hdec i hi).le
      have aux := rpow_sub_le_aux hp.le (by linarith) hxi hxi1 hle
      have hxe : 0 < (x i : ℝ) ^ ε := Real.rpow_pos_of_pos hxi ε
      have e1 : (x i : ℝ) ^ (1 - ε - 1) = ((x i : ℝ) ^ ε)⁻¹ := by
        rw [show 1 - ε - 1 = -ε by ring, Real.rpow_neg hxi.le]
      rw [e1] at aux
      have h1 := hstep i hi
      -- D ≤ lam (x_i - x_{i+1}) / x_i^ε
      have h2 : D (i + 1) ≤ lam * ((x i : ℝ) - x (i + 1)) * ((x i : ℝ) ^ ε)⁻¹ := by
        have : D (i + 1) * (x i : ℝ) ^ ε ≤ lam * ((x i : ℝ) - x (i + 1)) := by
          have h3 : D (i + 1) * (x i : ℝ) ^ ε / lam ≤ (x i : ℝ) - x (i + 1) := by linarith
          rw [div_le_iff₀ hlam] at h3
          linarith
        rw [← div_eq_mul_inv, le_div_iff₀ hxe]
        exact this
      rw [div_mul_eq_mul_div, le_div_iff₀ hp]
      have : (1 - ε) * ((x i : ℝ) - x (i + 1)) * ((x i : ℝ) ^ ε)⁻¹ * lam ≤
          ((x i : ℝ) ^ (1 - ε) - (x (i + 1) : ℝ) ^ (1 - ε)) * lam :=
        mul_le_mul_of_nonneg_right aux hlam.le
      nlinarith [this, h2, hp]
    have hsum : ∑ i ∈ Finset.range k, D (i + 1) ≤
        ∑ i ∈ Finset.range k, lam / (1 - ε) *
          ((x i : ℝ) ^ (1 - ε) - (x (i + 1) : ℝ) ^ (1 - ε)) :=
      Finset.sum_le_sum (fun i hi => hterm i (Finset.mem_range.mp hi))
    rw [← Finset.mul_sum, Finset.sum_range_sub' (fun i => (x i : ℝ) ^ (1 - ε)), hx0] at hsum
    have hxk : 0 ≤ (x k : ℝ) ^ (1 - ε) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hc : 0 ≤ lam / (1 - ε) := div_nonneg hlam.le hp.le
    have : lam / (1 - ε) * ((n : ℝ) ^ (1 - ε) - (x k : ℝ) ^ (1 - ε)) ≤
        lam * (n : ℝ) ^ (1 - ε) / (1 - ε) := by
      rw [mul_sub, div_mul_eq_mul_div]
      nlinarith [mul_nonneg hc hxk]
    linarith

end Charging

end GC.Portals
