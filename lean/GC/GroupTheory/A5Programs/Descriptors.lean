import GC.GroupTheory.A5Programs.Nineteen

/-!
# Latin descriptors, cycle monodromy and the `A₅` root domains (manuscripts 004e, 004f)

* `latin_relations`: a Latin factor `z = x y` is equivalent to each of the six oriented
  relations (004e, Lemma 5.1; 004f, Section 3).
* `descriptor_comp_pos`, `descriptor_comp_neg`, `descriptor_inv_pos`, `descriptor_inv_neg`:
  the descriptor algebra `x ↦ a x^ε b` (004e, Lemma 5.1; 004f, Lemma 3.1).
* `cycle_monodromy`: assignments of a cycle of relations `q_{i+1} = Φ_i(q_i)` correspond
  bijectively, via the prefix compositions, to the roots of the return map
  (004e, Theorem 5.2; 004f, Theorem 3.3); `comp_descriptors`: the return map of a cycle of
  descriptors is again a descriptor `r ↦ A r^ε B`.
* `root_domain_pos`, `root_domain_neg`: the classification of the root domains over `A₅`
  (004e, Theorem 5.3).
-/

namespace GC.A5Programs

open Equiv

section Descriptors

variable {G : Type*} [Group G]

/-- A Latin factor `z = x y` can be solved for each of its variables, which gives the six
oriented forms `y = x⁻¹ z`, `x = z y⁻¹`, `z = x y` (with the known third value as a coefficient)
of 004e, Lemma 5.1. -/
theorem latin_relations (x y z : G) :
    (z = x * y ↔ y = x⁻¹ * z) ∧ (z = x * y ↔ x = z * y⁻¹) := by
  have h1 : z = x * y ↔ y = x⁻¹ * z := by
    constructor <;> intro h <;> subst h <;> group
  have h2 : z = x * y ↔ x = z * y⁻¹ := by
    constructor <;> intro h <;> subst h <;> group
  exact ⟨h1, h2⟩

/-- The descriptor `x ↦ a x^ε b`, with sign `ε = true` for `+1` and `false` for `-1`. -/
def descr (a b : G) : Bool → G → G
  | true, x => a * x * b
  | false, x => a * x⁻¹ * b

theorem descriptor_comp_pos (a b c d : G) (ε : Bool) (x : G) :
    descr c d true (descr a b ε x) = descr (c * a) (b * d) ε x := by
  cases ε <;> simp [descr, mul_assoc]

theorem descriptor_comp_neg (a b c d : G) (ε : Bool) (x : G) :
    descr c d false (descr a b ε x) = descr (c * b⁻¹) (a⁻¹ * d) (!ε) x := by
  cases ε <;> simp [descr, mul_assoc]

theorem descriptor_inv_pos (a b x : G) :
    descr a⁻¹ b⁻¹ true (descr a b true x) = x := by simp [descr, mul_assoc]

theorem descriptor_inv_neg (a b x : G) :
    descr b a false (descr a b false x) = x := by simp [descr, mul_assoc]

/-- Composition of descriptors is a descriptor (with explicit new coefficients). -/
theorem comp_descriptors (Φ : ℕ → G × G × Bool) (m : ℕ) :
    ∃ A B : G, ∃ ε : Bool, ∀ x,
      (List.range m).foldl (fun y i => descr (Φ i).1 (Φ i).2.1 (Φ i).2.2 y) x = descr A B ε x := by
  induction m with
  | zero => exact ⟨1, 1, true, fun x => by simp [descr]⟩
  | succ m ih =>
    obtain ⟨A, B, ε, h⟩ := ih
    rcases hΦ : (Φ m).2.2 with _ | _
    · refine ⟨(Φ m).1 * B⁻¹, A⁻¹ * (Φ m).2.1, !ε, fun x => ?_⟩
      rw [List.range_succ, List.foldl_append, h x]
      simp only [List.foldl_cons, List.foldl_nil, hΦ]
      exact descriptor_comp_neg _ _ _ _ _ _
    · refine ⟨(Φ m).1 * A, B * (Φ m).2.1, ε, fun x => ?_⟩
      rw [List.range_succ, List.foldl_append, h x]
      simp only [List.foldl_cons, List.foldl_nil, hΦ]
      exact descriptor_comp_pos _ _ _ _ _ _

end Descriptors

section Monodromy

variable {X : Type*}

/-- The prefix compositions `Ψ_i = Φ_{i-1} ∘ ⋯ ∘ Φ_0`. -/
def prefixMap (Φ : ℕ → X → X) : ℕ → X → X
  | 0, x => x
  | i + 1, x => Φ i (prefixMap Φ i x)

/-- **Cycle monodromy** (004e, Theorem 5.2; 004f, Theorem 3.3). For relations
`q_{i+1} = Φ_i(q_i)` (`0 ≤ i < m - 1`) closed by `q_0 = Φ_{m-1}(q_{m-1})`, an assignment
`q_0, …, q_{m-1}` satisfies all `m` relations iff `q_i = Ψ_i(q_0)` for all `i < m` and `q_0` is a
root of the return map `Ψ_m`. Hence `r ↦ (Ψ_i r)_i` is a bijection from the roots of
`r = Ψ_m(r)` onto the solutions. -/
theorem cycle_monodromy (Φ : ℕ → X → X) (m : ℕ) (hm : 0 < m) (q : ℕ → X) :
    ((∀ i, i + 1 < m → q (i + 1) = Φ i (q i)) ∧ q 0 = Φ (m - 1) (q (m - 1))) ↔
    ((∀ i, i < m → q i = prefixMap Φ i (q 0)) ∧ q 0 = prefixMap Φ m (q 0)) := by
  constructor
  · rintro ⟨h1, h2⟩
    have hp : ∀ i, i < m → q i = prefixMap Φ i (q 0) := by
      intro i hi
      induction i with
      | zero => rfl
      | succ i ih => rw [h1 i hi, ih (by omega)]; rfl
    refine ⟨hp, ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    calc q 0 = Φ k (q k) := by simpa using h2
      _ = Φ k (prefixMap Φ k (q 0)) := by rw [hp k (by omega)]
      _ = prefixMap Φ (k + 1) (q 0) := rfl
  · rintro ⟨h1, h2⟩
    refine ⟨fun i hi => ?_, ?_⟩
    · rw [h1 (i + 1) hi, h1 i (by omega)]; rfl
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      rw [h1 k (by omega)]
      exact h2

end Monodromy

/-! ## Root domains over `A₅` -/

/-- `D₊(A, B) = {r ∈ A₅ : r = A r B}`. -/
def rootPos (A B : Perm (Fin 5)) : Finset (Perm (Fin 5)) := A5set.filter fun r => r = A * r * B
/-- `D₋(A, B) = {r ∈ A₅ : r = A r⁻¹ B}`. -/
def rootNeg (A B : Perm (Fin 5)) : Finset (Perm (Fin 5)) := A5set.filter fun r => r = A * r⁻¹ * B

theorem card_filter_A5set (p : Perm (Fin 5) → Prop) [DecidablePred p] (b : Perm (Fin 5) → Bool)
    (hb : ∀ x, b x = true ↔ p x) : (A5set.filter p).card = (A5list.filter b).length := by
  have : A5set.filter p = (A5list.filter b).toFinset := by
    ext x; simp [A5set, hb]
  rw [this, List.toFinset_card_of_nodup (A5list_nodup.filter _)]

set_option maxRecDepth 100000 in
theorem sqrt_counts : ∀ g ∈ A5list,
    let c := (A5list.filter fun x => peq (x * x) g).length
    (c = 0 ∨ c = 1 ∨ c = 16) ∧ (c = 16 ↔ peq g 1 = true) ∧
      (c = 0 ↔ (peq (g * g) 1 && !peq g 1) = true) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cent_counts : ∀ g ∈ A5list,
    let c := (A5list.filter fun x => peq (x * g) (g * x)).length
    (c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 60) ∧ (c = 60 ↔ peq g 1 = true) := by
  decide +kernel

theorem conj_inv_mem {A r : Perm (Fin 5)} (hA : A ∈ alternatingGroup (Fin 5)) :
    A⁻¹ * r ∈ alternatingGroup (Fin 5) ↔ r ∈ alternatingGroup (Fin 5) := by
  constructor
  · intro h; have := Subgroup.mul_mem _ hA h; simpa using this
  · intro h; exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hA) h

/-- **Root domains for `ε = -1`** (004e, Theorem 5.3(ii)): `|D₋(A, B)| ∈ {0, 1, 16}`; it is `16`
exactly when `A = B`, and `0` exactly when `A⁻¹ B` is a double transposition (an element of
order 2). -/
theorem root_domain_neg {A B : Perm (Fin 5)} (hA : A ∈ alternatingGroup (Fin 5))
    (hB : B ∈ alternatingGroup (Fin 5)) :
    ((rootNeg A B).card = 0 ∨ (rootNeg A B).card = 1 ∨ (rootNeg A B).card = 16) ∧
    ((rootNeg A B).card = 16 ↔ A = B) ∧
    ((rootNeg A B).card = 0 ↔ (A⁻¹ * B) * (A⁻¹ * B) = 1 ∧ A⁻¹ * B ≠ 1) := by
  set g := A⁻¹ * B with hg
  have hgm : g ∈ alternatingGroup (Fin 5) := Subgroup.mul_mem _ (Subgroup.inv_mem _ hA) hB
  -- `r ↦ A⁻¹ r` maps `D₋(A, B)` onto the square roots of `g`
  have hcard : (rootNeg A B).card = (A5set.filter fun x => x * x = g).card := by
    have himg : (rootNeg A B).image (fun r => A⁻¹ * r) = A5set.filter fun x => x * x = g := by
      ext x
      simp only [rootNeg, Finset.mem_image, Finset.mem_filter, mem_A5set]
      constructor
      · rintro ⟨r, ⟨hr, hr2⟩, rfl⟩
        refine ⟨(conj_inv_mem hA).2 hr, ?_⟩
        have hB' : B = r * A⁻¹ * r := by
          calc B = (A * r⁻¹)⁻¹ * (A * r⁻¹ * B) := by group
            _ = (A * r⁻¹)⁻¹ * r := by rw [← hr2]
            _ = r * A⁻¹ * r := by group
        rw [hg, hB']; group
      · rintro ⟨hx, hx2⟩
        refine ⟨A * x, ⟨?_, ?_⟩, by group⟩
        · exact Subgroup.mul_mem _ hA hx
        · have : B = A * (x * x) := by rw [hx2, hg]; group
          rw [this]; group
    rw [← himg, Finset.card_image_of_injective _ (mul_right_injective A⁻¹)]
  have hc : (A5set.filter fun x => x * x = g).card =
      (A5list.filter fun x => peq (x * x) g).length :=
    card_filter_A5set _ _ (fun x => peq_iff)
  obtain ⟨h1, h2, h3⟩ := sqrt_counts g ((mem_A5list_iff g).2 hgm)
  rw [hcard, hc]
  refine ⟨h1, ?_, ?_⟩
  · rw [h2, peq_iff, hg, inv_mul_eq_one]
  · rw [h3]
    simp only [Bool.and_eq_true, Bool.not_eq_true', peq_iff]
    constructor
    · rintro ⟨h, h'⟩; exact ⟨h, fun e => by rw [peq_iff.2 e] at h'; exact absurd h' (by decide)⟩
    · rintro ⟨h, h'⟩; refine ⟨h, ?_⟩
      cases hp : peq g 1
      · rfl
      · exact absurd (peq_iff.1 hp) h'

/-- **Root domains for `ε = 1`** (004e, Theorem 5.3(i)): `|D₊(A, B)| ∈ {0, 3, 4, 5, 60}`; it is
nonzero exactly when `A` is conjugate in `A₅` to `B⁻¹`, it then equals the order of the
centralizer of `B` in `A₅`, and `60` occurs only for `A = B = e`. -/
theorem root_domain_pos {A B : Perm (Fin 5)} (hA : A ∈ alternatingGroup (Fin 5))
    (hB : B ∈ alternatingGroup (Fin 5)) :
    ((rootPos A B).card = 0 ∨ (rootPos A B).card = 3 ∨ (rootPos A B).card = 4 ∨
      (rootPos A B).card = 5 ∨ (rootPos A B).card = 60) ∧
    ((rootPos A B).card ≠ 0 ↔ ∃ r ∈ alternatingGroup (Fin 5), r * B⁻¹ * r⁻¹ = A) ∧
    ((rootPos A B).card ≠ 0 →
      (rootPos A B).card = (A5set.filter fun r => r * B = B * r).card) ∧
    ((rootPos A B).card = 60 ↔ A = 1 ∧ B = 1) := by
  have hmem : ∀ r, r ∈ rootPos A B ↔ r ∈ alternatingGroup (Fin 5) ∧ r * B⁻¹ * r⁻¹ = A := by
    intro r
    simp only [rootPos, Finset.mem_filter, mem_A5set]
    constructor
    · rintro ⟨h1, h2⟩; refine ⟨h1, ?_⟩
      calc r * B⁻¹ * r⁻¹ = (A * r * B) * B⁻¹ * r⁻¹ := by rw [← h2]
        _ = A := by group
    · rintro ⟨h1, h2⟩; refine ⟨h1, ?_⟩; rw [← h2]; group
  have hcent : (A5set.filter fun r => r * B = B * r).card =
      (A5list.filter fun x => peq (x * B) (B * x)).length :=
    card_filter_A5set _ _ (fun x => peq_iff)
  obtain ⟨hc1, hc2⟩ := cent_counts B ((mem_A5list_iff B).2 hB)
  -- if nonempty, `D₊` is a coset of the centralizer
  have hcoset : ∀ r₀ ∈ rootPos A B,
      (rootPos A B).card = (A5set.filter fun r => r * B = B * r).card := by
    intro r₀ hr₀
    obtain ⟨hr₀m, hr₀e⟩ := (hmem r₀).1 hr₀
    have himg : (A5set.filter fun r => r * B = B * r).image (fun c => r₀ * c) = rootPos A B := by
      ext r
      rw [hmem]
      simp only [Finset.mem_image, Finset.mem_filter, mem_A5set]
      constructor
      · rintro ⟨c, ⟨hc, hcB⟩, rfl⟩
        refine ⟨Subgroup.mul_mem _ hr₀m hc, ?_⟩
        rw [← hr₀e]
        have : c * B⁻¹ = B⁻¹ * c := by
          calc c * B⁻¹ = B⁻¹ * (B * c) * B⁻¹ := by group
            _ = B⁻¹ * (c * B) * B⁻¹ := by rw [hcB]
            _ = B⁻¹ * c := by group
        calc r₀ * c * B⁻¹ * (r₀ * c)⁻¹ = r₀ * (c * B⁻¹) * c⁻¹ * r₀⁻¹ := by group
          _ = r₀ * (B⁻¹ * c) * c⁻¹ * r₀⁻¹ := by rw [this]
          _ = r₀ * B⁻¹ * r₀⁻¹ := by group
      · rintro ⟨hr, hre⟩
        refine ⟨r₀⁻¹ * r, ⟨(conj_inv_mem hr₀m).2 hr, ?_⟩, by group⟩
        have e : r * B⁻¹ * r⁻¹ = r₀ * B⁻¹ * r₀⁻¹ := hre.trans hr₀e.symm
        have : r₀⁻¹ * r * B⁻¹ = B⁻¹ * (r₀⁻¹ * r) := by
          calc r₀⁻¹ * r * B⁻¹ = r₀⁻¹ * (r * B⁻¹ * r⁻¹) * r := by group
            _ = r₀⁻¹ * (r₀ * B⁻¹ * r₀⁻¹) * r := by rw [e]
            _ = B⁻¹ * (r₀⁻¹ * r) := by group
        calc r₀⁻¹ * r * B = B * (B⁻¹ * (r₀⁻¹ * r)) * B := by group
          _ = B * (r₀⁻¹ * r * B⁻¹) * B := by rw [this]
          _ = B * (r₀⁻¹ * r) := by group
    rw [← himg, Finset.card_image_of_injective _ (mul_right_injective r₀)]
  have hne : (rootPos A B).card ≠ 0 ↔ ∃ r ∈ alternatingGroup (Fin 5), r * B⁻¹ * r⁻¹ = A := by
    rw [Ne, Finset.card_eq_zero, ← Ne, ← Finset.nonempty_iff_ne_empty]
    constructor
    · rintro ⟨r, hr⟩; exact ⟨r, (hmem r).1 hr⟩
    · rintro ⟨r, hr, he⟩; exact ⟨r, (hmem r).2 ⟨hr, he⟩⟩
  have hcoset' : (rootPos A B).card ≠ 0 →
      (rootPos A B).card = (A5set.filter fun r => r * B = B * r).card := by
    intro h
    obtain ⟨r₀, hr₀⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero h)
    exact hcoset r₀ hr₀
  refine ⟨?_, hne, hcoset', ?_⟩
  · by_cases h0 : (rootPos A B).card = 0
    · exact Or.inl h0
    · right; rw [hcoset' h0, hcent]; exact hc1
  · constructor
    · intro h60
      have hB1 : B = 1 := by
        rw [hcoset' (by omega), hcent] at h60
        exact peq_iff.1 (hc2.1 h60)
      refine ⟨?_, hB1⟩
      obtain ⟨r, _, hr⟩ := hne.1 (by omega)
      rw [← hr, hB1]; group
    · rintro ⟨rfl, rfl⟩
      rw [hcoset' ?_, hcent]
      · exact hc2.2 (by simp [peq])
      · exact hne.2 ⟨1, Subgroup.one_mem _, by group⟩

end GC.A5Programs
