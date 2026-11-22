import GC.Computability.Portals.Horn
import GC.Computability.Portals.HypergraphA5

/-!
# Exponential-state portals with constant-depth transfer (manuscript 005c)

* `full_capacity_portal`, `capacity_switch`, `a5_capacity_switch`: Theorem "A full-capacity A5
  portal" (iv) and Proposition "Hard-coefficient capacity switch": with
  `M(x, y) = e` if `x = e` and `y` otherwise, the outputs `(M(x, y_i))_i` range over all of `G^t`,
  and for a fixed coefficient `x` the image of `y ↦ (M(x, y_i))_i` has one element if `x = e`
  and `|G|^t` (`60^t` for `A₅`) elements otherwise.
* `layerMap_lt`, `layerMap_mono`: Theorem "Rank-layer symbolic transfer": the map
  `Φ(X) = Reach_{G(X)}(X ∪ Seed(X))` is monotone and satisfies `Φ(𝓕_{<k}) = 𝓕_{≤k}` for `k ≥ 1`.
* `layerMap_iterate`: Corollary "A band of B ranks": `Φ^B(𝓕_{<k}) = 𝓕_{≤k+B-1}`.
* `newly_derivable_not_monotone`: the correction stated in the paper — the source's map to the
  facts newly derivable at rank `k` (`X ↦ Φ(X) \ X`) is not monotone.
* `search_first_stop_le` (in `Basic`): the stopping rule of Corollary "One-shot criterion".

The circuit size/depth bounds, the composition-algebra theorem and the fanout-kernel compiler
are not formalized here (the round structure of the fanout-height compiler is in 005e). The
selector term `M` is treated as the function it induces (its realization as an `A₅` term is
Maurer–Rhodes polynomial completeness, which is not formalized).
-/

namespace GC.Portals

section Capacity

variable {G : Type*} [Group G] [DecidableEq G]

/-- The fixed function `M(x, y) = e` if `x = e`, and `y` otherwise. -/
def portalM (x y : G) : G := if x = 1 then 1 else y

/-- Theorem (full-capacity portal) (iv): every vector of `G^t` is an output vector. -/
theorem full_capacity_portal [Nontrivial G] (t : ℕ) (v : Fin t → G) :
    ∃ (x : G) (y : Fin t → G), (fun i => portalM x (y i)) = v := by
  obtain ⟨x, hx⟩ := exists_ne (1 : G)
  exact ⟨x, v, funext fun i => by simp [portalM, hx]⟩

/-- Proposition (hard-coefficient capacity switch). -/
theorem capacity_switch [Fintype G] (t : ℕ) (x : G) :
    (Finset.univ.image (fun y : Fin t → G => fun i => portalM x (y i))).card =
      if x = 1 then 1 else Fintype.card G ^ t := by
  split_ifs with hx
  · rw [Finset.card_eq_one]
    refine ⟨fun _ => 1, ?_⟩
    ext v
    simp [portalM, hx, eq_comm]
  · have : (fun y : Fin t → G => fun i => portalM x (y i)) = id := by
      funext y i; simp [portalM, hx]
    rw [this, Finset.image_id, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]

/-- The capacity switch for `A₅`: one state if `x = e`, `60^t` states otherwise. -/
theorem a5_capacity_switch (t : ℕ) (x : alternatingGroup (Fin 5)) :
    (Finset.univ.image (fun y : Fin t → alternatingGroup (Fin 5) => fun i => portalM x (y i))).card
      = if x = 1 then 1 else 60 ^ t := by
  rw [capacity_switch, card_alternatingGroup_five]

end Capacity

namespace HornSystem

variable {α : Type*} (S : HornSystem α)

/-- `Seed(X)`: conclusions of binary rules with both premises in `X`. -/
def seedsOf (X : Set α) : Set α := {g | ∃ f ∈ X, ∃ f' ∈ X, S.binary f f' g}

/-- The rank-layer map `Φ(X) = Reach_{G(X)}(X ∪ Seed(X))`. -/
def layerMap (X : Set α) : Set α := S.reach X (X ∪ S.seedsOf X)

/-- `Φ` is monotone (it is computed by a monotone circuit). -/
theorem layerMap_mono : Monotone S.layerMap := by
  intro X Y hXY g ⟨a, ha, hag⟩
  refine ⟨a, ?_, ?_⟩
  · rcases ha with ha | ⟨f, hf, f', hf', hb⟩
    · exact Or.inl (hXY ha)
    · exact Or.inr ⟨f, hXY hf, f', hXY hf', hb⟩
  · refine Relation.ReflTransGen.mono (fun u v h => ?_) _ _ hag
    rcases h with h | ⟨f', hf', h⟩ | ⟨f', hf', h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨f', hXY hf', h⟩)
    · exact Or.inr (Or.inr ⟨f', hXY hf', h⟩)

/-- Theorem (rank-layer symbolic transfer): `Φ(𝓕_{<k}) = 𝓕_{≤k}` for every `k ≥ 1`. -/
theorem layerMap_lt (k : ℕ) (hk : 1 ≤ k) : S.layerMap (S.lt k) = S.le k := by
  apply Set.Subset.antisymm
  · apply S.le_of_reach
    rintro g (hg | ⟨f, ⟨r, hr, hp⟩, f', ⟨r', hr', hp'⟩, hb⟩)
    · exact S.lt_subset_le k hg
    · refine ⟨_, ?_, Proves.binary hb hp hp'⟩
      calc strahler r r' ≤ strahler (k - 1) (k - 1) := strahler_mono (by omega) (by omega)
        _ ≤ k := by unfold strahler; split_ifs <;> omega
  · rw [S.rank_layer k hk]
    rintro g (hg | ⟨a, ha, hag⟩)
    · exact ⟨g, Or.inl hg, Relation.ReflTransGen.refl⟩
    · obtain ⟨_, f, f', hb, ⟨⟨r, hr, hp⟩, _⟩, ⟨⟨r', hr', hp'⟩, _⟩⟩ := ha
      exact ⟨a, Or.inr ⟨f, ⟨r, by omega, hp⟩, f', ⟨r', by omega, hp'⟩, hb⟩, hag⟩

/-- Corollary (a band of `B` ranks): `Φ^B(𝓕_{<k}) = 𝓕_{≤k+B-1}` for `k, B ≥ 1`. -/
theorem layerMap_iterate (k B : ℕ) (hk : 1 ≤ k) (hB : 1 ≤ B) :
    S.layerMap^[B] (S.lt k) = S.le (k + B - 1) := by
  induction B with
  | zero => omega
  | succ B ih =>
    rcases Nat.eq_zero_or_pos B with rfl | hB'
    · simp [S.layerMap_lt k hk]
    · rw [Function.iterate_succ_apply', ih hB', S.le_eq_lt_succ,
        S.layerMap_lt _ (by omega), show k + B - 1 + 1 = k + (B + 1) - 1 by omega]

end HornSystem

/-- The one-rule Horn system `0 ⇒ 1` on two facts. -/
def oneRule : HornSystem (Fin 2) where
  ax _ := False
  unary f g := f = 0 ∧ g = 1
  binary _ _ _ := False

/-- The source's map to the newly derivable facts, `X ↦ Φ(X) \ X`, is not monotone. -/
theorem newly_derivable_not_monotone :
    ¬ Monotone (fun X : Set (Fin 2) => oneRule.layerMap X \ X) := by
  intro hmono
  have h := hmono (show ({0} : Set (Fin 2)) ⊆ {0, 1} by simp)
  have h1 : (1 : Fin 2) ∈ oneRule.layerMap {0} \ {0} := by
    refine ⟨⟨0, Or.inl rfl, Relation.ReflTransGen.single (Or.inl ⟨rfl, rfl⟩)⟩, by simp⟩
  have := (h h1).2
  simp at this

end GC.Portals
