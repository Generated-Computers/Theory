import GC.Computability.Portals.Horn

/-!
# Menger's theorem inside one Strahler layer (manuscript 005d)

* `HornSystem.rank_layer` (in `Horn`): Lemma "Rank-layer reachability",
  `𝓕_{≤k} = 𝓕_{<k} ∪ Reach_{G_k}(S_k)` for `k ≥ 1`, including the case that the source's proof
  skipped (`HornSystem.mem_seeds_of_binary`).
* `closure_determines_region`, `lfpRegion_closed`: Lemma "Closure determines the region": if `H`
  is a closed boundary of `R`, then `D ∩ R = lfp_R(D ∩ H)`, where `lfp_R(X)` is the least set
  `Y ⊆ R` such that every rule with conclusion in `R` and premises in `X ∪ Y` concludes in `Y`.
* `side_premise_star`: Theorem "Side-premise star": with `A` derivable and `B_i` derivable
  exactly for `i ∈ P`, the conclusions `C_i` of `A ∧ B_i ⇒ C_i` are derivable exactly for
  `i ∈ P`, so the conclusion vector takes all `2^t` patterns.

Not formalized: the vertex form of Menger's theorem (not available in Mathlib) and hence the
unary-spine Menger portal and its corollary; the forest-mass lemma; the A5 realization of the
star; the complexity bounds of the portal theorems.
-/

namespace GC.Portals

namespace HornSystem

variable {α : Type*} (S : HornSystem α)

/-- The derivable facts `D`. -/
def derivable : Set α := {f | ∃ r, S.Proves f r}

/-- `H` is a closed boundary of the region `R`: every premise outside `R` of every rule with
conclusion in `R` lies in `H`. -/
def ClosedBoundary (H R : Set α) : Prop :=
  (∀ f g, S.unary f g → g ∈ R → f ∉ R → f ∈ H) ∧
    (∀ f f' g, S.binary f f' g → g ∈ R → (f ∉ R → f ∈ H) ∧ (f' ∉ R → f' ∈ H))

/-- `Y` is closed for the region `R` over `X`: `Y ⊆ R`, and every rule with conclusion in `R`
whose premises lie in `X ∪ Y` has its conclusion in `Y`. -/
def RegionClosed (R X Y : Set α) : Prop :=
  Y ⊆ R ∧ (∀ g ∈ R, S.ax g → g ∈ Y) ∧
    (∀ f g, g ∈ R → S.unary f g → f ∈ X ∪ Y → g ∈ Y) ∧
    (∀ f f' g, g ∈ R → S.binary f f' g → f ∈ X ∪ Y → f' ∈ X ∪ Y → g ∈ Y)

/-- `lfp_R(X)`: the least set closed for the region `R` over `X`. -/
def lfpRegion (R X : Set α) : Set α := ⋂₀ {Y | S.RegionClosed R X Y}

/-- `lfp_R(X)` is itself closed (so it is the least closed set). -/
theorem lfpRegion_closed (R X : Set α) : S.RegionClosed R X (S.lfpRegion R X) := by
  refine ⟨fun g hg => Set.mem_sInter.mp hg R ⟨le_rfl, fun g hg _ => hg,
    fun _ g hg _ _ => hg, fun _ _ g hg _ _ _ => hg⟩, ?_, ?_, ?_⟩
  · intro g hg ha
    exact Set.mem_sInter.mpr fun Y hY => hY.2.1 g hg ha
  · intro f g hg hu hf
    refine Set.mem_sInter.mpr fun Y hY => hY.2.2.1 f g hg hu ?_
    rcases hf with hf | hf
    · exact Or.inl hf
    · exact Or.inr (Set.mem_sInter.mp hf Y hY)
  · intro f f' g hg hb hf hf'
    refine Set.mem_sInter.mpr fun Y hY => hY.2.2.2 f f' g hg hb ?_ ?_
    · rcases hf with hf | hf
      · exact Or.inl hf
      · exact Or.inr (Set.mem_sInter.mp hf Y hY)
    · rcases hf' with hf' | hf'
      · exact Or.inl hf'
      · exact Or.inr (Set.mem_sInter.mp hf' Y hY)

/-- Lemma (closure determines the region): if `H` is a closed boundary of `R`, then
`D ∩ R = lfp_R(D ∩ H)`. -/
theorem closure_determines_region {H R : Set α} (hH : S.ClosedBoundary H R) :
    S.derivable ∩ R = S.lfpRegion R (S.derivable ∩ H) := by
  apply Set.Subset.antisymm
  · rintro g ⟨⟨r, hp⟩, hg⟩
    refine Set.mem_sInter.mpr fun Y hY => ?_
    induction hp with
    | ax h => exact hY.2.1 _ hg h
    | @unary f g r hu hpf ih =>
      refine hY.2.2.1 f g hg hu ?_
      by_cases hfR : f ∈ R
      · exact Or.inr (ih hfR)
      · exact Or.inl ⟨⟨r, hpf⟩, hH.1 f g hu hg hfR⟩
    | @binary f f' g r r' hb hpf hpf' ih ih' =>
      refine hY.2.2.2 f f' g hg hb ?_ ?_
      · by_cases hfR : f ∈ R
        · exact Or.inr (ih hfR)
        · exact Or.inl ⟨⟨r, hpf⟩, (hH.2 f f' g hb hg).1 hfR⟩
      · by_cases hfR : f' ∈ R
        · exact Or.inr (ih' hfR)
        · exact Or.inl ⟨⟨r', hpf'⟩, (hH.2 f f' g hb hg).2 hfR⟩
  · refine Set.sInter_subset_of_mem ⟨Set.inter_subset_right, ?_, ?_, ?_⟩
    · intro g hg ha
      exact ⟨⟨0, Proves.ax ha⟩, hg⟩
    · intro f g hg hu hf
      have hfD : f ∈ S.derivable := hf.elim (fun h => h.1) (fun h => h.1)
      obtain ⟨r, hp⟩ := hfD
      exact ⟨⟨r, Proves.unary hu hp⟩, hg⟩
    · intro f f' g hg hb hf hf'
      obtain ⟨r, hp⟩ : f ∈ S.derivable := hf.elim (fun h => h.1) (fun h => h.1)
      obtain ⟨r', hp'⟩ : f' ∈ S.derivable := hf'.elim (fun h => h.1) (fun h => h.1)
      exact ⟨⟨_, Proves.binary hb hp hp'⟩, hg⟩

end HornSystem

/-- Facts of the side-premise star: `A`, `B_i`, `C_i`. -/
inductive StarFact (t : ℕ) where
  | A : StarFact t
  | B : Fin t → StarFact t
  | C : Fin t → StarFact t

/-- The side-premise star: `A` is an axiom (it is derivable), `B_i` is an axiom exactly for
`i ∈ P` (its derivability is controlled from outside), and the only rules concluding `C_i` are
`A ∧ B_i ⇒ C_i`. -/
def starSystem (t : ℕ) (P : Set (Fin t)) : HornSystem (StarFact t) where
  ax f := f = StarFact.A ∨ ∃ i ∈ P, f = StarFact.B i
  unary _ _ := False
  binary f f' g := ∃ i, f = StarFact.A ∧ f' = StarFact.B i ∧ g = StarFact.C i

theorem starSystem_proves_B {t : ℕ} {P : Set (Fin t)} {i : Fin t} {r : ℕ}
    (h : (starSystem t P).Proves (StarFact.B i) r) : i ∈ P := by
  generalize hf : StarFact.B i = f at h
  cases h with
  | ax h =>
    rcases h with h | ⟨j, hj, h⟩
    · subst hf; cases h
    · subst hf; cases h; exact hj
  | unary h _ => exact h.elim
  | binary h _ _ =>
    obtain ⟨j, _, _, h⟩ := h
    subst hf; cases h

/-- Theorem (side-premise star): the conclusion `C_i` is derivable exactly when `B_i` is, so the
conclusion vector equals the pattern `P`, which ranges over all `2^t` subsets. -/
theorem side_premise_star (t : ℕ) (P : Set (Fin t)) :
    {i | StarFact.C i ∈ (starSystem t P).derivable} = P := by
  ext i
  simp only [Set.mem_setOf_eq, HornSystem.derivable]
  constructor
  · rintro ⟨r, h⟩
    generalize hf : StarFact.C i = f at h
    cases h with
    | ax h =>
      rcases h with h | ⟨j, _, h⟩
      · subst hf; cases h
      · subst hf; cases h
    | unary h _ => exact h.elim
    | binary h _ hB =>
      obtain ⟨j, rfl, rfl, h⟩ := h
      subst hf; cases h
      exact starSystem_proves_B hB
  · intro hi
    exact ⟨_, HornSystem.Proves.binary ⟨i, rfl, rfl, rfl⟩
      (HornSystem.Proves.ax (Or.inl rfl)) (HornSystem.Proves.ax (Or.inr ⟨i, hi, rfl⟩))⟩

/-- The `2^t` derivability patterns are all realized: the pattern map is injective. -/
theorem side_premise_star_injective (t : ℕ) :
    Function.Injective (fun P : Set (Fin t) => {i | StarFact.C i ∈ (starSystem t P).derivable}) := by
  intro P Q h
  simpa only [side_premise_star] using h

end GC.Portals
