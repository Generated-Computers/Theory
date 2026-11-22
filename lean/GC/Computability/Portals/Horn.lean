import GC.Computability.Portals.Basic
import Mathlib.Logic.Relation

/-!
# Ranked Horn systems (shared by manuscripts 005c and 005d)

A Horn system has axioms, unary rules `f ⇒ g` and binary rules `f ∧ f' ⇒ g`. A proof has a
Horton–Strahler rank: axioms `0`, unary rules keep the rank, binary rules combine the premise
ranks by `strahler`. `S.le k` (`𝓕_{≤k}`) and `S.lt k` (`𝓕_{<k}`) are the facts with a proof of
rank at most `k`, respectively less than `k`.

`rank_layer` is the rank-layer reachability lemma of 005d (Lemma "Rank-layer reachability"):
`𝓕_{≤k} = 𝓕_{<k} ∪ Reach_{G_k}(S_k)` for `k ≥ 1`.
-/

namespace GC.Portals

/-- A Horn system with rules of arity at most two on the fact universe `α`. -/
structure HornSystem (α : Type*) where
  /-- rules without premises -/
  ax : α → Prop
  /-- `unary f g`: a rule deriving `g` from `f` -/
  unary : α → α → Prop
  /-- `binary f f' g`: a rule deriving `g` from `f` and `f'` -/
  binary : α → α → α → Prop

namespace HornSystem

variable {α : Type*} (S : HornSystem α)

/-- `S.Proves f r`: the fact `f` has a proof of Horton–Strahler rank `r`. -/
inductive Proves : α → ℕ → Prop
  | ax {f : α} : S.ax f → Proves f 0
  | unary {f g : α} {r : ℕ} : S.unary f g → Proves f r → Proves g r
  | binary {f f' g : α} {r r' : ℕ} :
      S.binary f f' g → Proves f r → Proves f' r' → Proves g (strahler r r')

/-- `𝓕_{≤k}`: facts with a proof of rank at most `k`. -/
def le (k : ℕ) : Set α := {f | ∃ r ≤ k, S.Proves f r}

/-- `𝓕_{<k}`: facts with a proof of rank less than `k`. -/
def lt (k : ℕ) : Set α := {f | ∃ r < k, S.Proves f r}

/-- `f` has minimum rank exactly `k`. -/
def ExactRank (f : α) (k : ℕ) : Prop := f ∈ S.le k ∧ f ∉ S.lt k

/-- The balanced seeds `S_k`: conclusions outside `𝓕_{<k}` of binary rules whose two premises
both have rank exactly `k - 1`. -/
def seeds (k : ℕ) : Set α :=
  {g | g ∉ S.lt k ∧ ∃ f f', S.binary f f' g ∧ S.ExactRank f (k - 1) ∧ S.ExactRank f' (k - 1)}

/-- The arcs of the graph `G(X)`: `f → g` if a rule derives `g` from `f` alone or from `f`
together with one side premise in `X`. -/
def arc (X : Set α) (f g : α) : Prop :=
  S.unary f g ∨ (∃ f' ∈ X, S.binary f f' g) ∨ (∃ f' ∈ X, S.binary f' f g)

/-- Facts reachable in `G(X)` from `A`. -/
def reach (X A : Set α) : Set α := {g | ∃ a ∈ A, Relation.ReflTransGen (S.arc X) a g}

theorem lt_subset_le (k : ℕ) : S.lt k ⊆ S.le k := fun _ ⟨r, hr, h⟩ => ⟨r, hr.le, h⟩

theorem le_eq_lt_succ (k : ℕ) : S.le k = S.lt (k + 1) := by
  ext f; simp only [le, lt, Set.mem_setOf_eq, Nat.lt_succ_iff]

/-- Arcs of `G_k` preserve `𝓕_{≤k}`. -/
theorem le_of_arc {k : ℕ} {f g : α} (hf : f ∈ S.le k) (h : S.arc (S.lt k) f g) : g ∈ S.le k := by
  obtain ⟨r, hr, hp⟩ := hf
  rcases h with h | ⟨f', ⟨r', hr', hp'⟩, h⟩ | ⟨f', ⟨r', hr', hp'⟩, h⟩
  · exact ⟨r, hr, Proves.unary h hp⟩
  · refine ⟨_, ?_, Proves.binary h hp hp'⟩
    calc strahler r r' ≤ strahler k (k - 1) := strahler_mono hr (by omega)
      _ = k := by unfold strahler; split_ifs <;> omega
  · refine ⟨_, ?_, Proves.binary h hp' hp⟩
    calc strahler r' r ≤ strahler (k - 1) k := strahler_mono (by omega) hr
      _ = k := by unfold strahler; split_ifs <;> omega

theorem le_of_reach {k : ℕ} {A : Set α} (hA : A ⊆ S.le k) : S.reach (S.lt k) A ⊆ S.le k := by
  rintro g ⟨a, ha, hag⟩
  induction hag with
  | refl => exact hA ha
  | tail _ hbc ih => exact S.le_of_arc ih hbc

theorem seeds_subset_le (k : ℕ) (hk : 1 ≤ k) : S.seeds k ⊆ S.le k := by
  rintro g ⟨_, f, f', hb, ⟨⟨r, hr, hp⟩, _⟩, ⟨⟨r', hr', hp'⟩, _⟩⟩
  refine ⟨_, ?_, Proves.binary hb hp hp'⟩
  calc strahler r r' ≤ strahler (k - 1) (k - 1) := strahler_mono hr hr'
    _ ≤ k := by unfold strahler; split_ifs <;> omega

/-- The case missing in the source: a binary rule with both premises in `𝓕_{<k}` and conclusion
outside `𝓕_{<k}` has both premises of rank exactly `k - 1`, so its conclusion is a seed. -/
theorem mem_seeds_of_binary {k : ℕ} {f f' g : α} (hb : S.binary f f' g) (hf : f ∈ S.lt k)
    (hf' : f' ∈ S.lt k) (hg : g ∉ S.lt k) : g ∈ S.seeds k := by
  obtain ⟨r, hr, hp⟩ := hf
  obtain ⟨r', hr', hp'⟩ := hf'
  refine ⟨hg, f, f', hb, ⟨⟨r, by omega, hp⟩, ?_⟩, ⟨⟨r', by omega, hp'⟩, ?_⟩⟩
  · rintro ⟨r₀, hr₀, hp₀⟩
    apply hg
    refine ⟨_, ?_, Proves.binary hb hp₀ hp'⟩
    calc strahler r₀ r' ≤ strahler (k - 2) (k - 1) := strahler_mono (by omega) (by omega)
      _ < k := by unfold strahler; split_ifs <;> omega
  · rintro ⟨r₀, hr₀, hp₀⟩
    apply hg
    refine ⟨_, ?_, Proves.binary hb hp hp₀⟩
    calc strahler r r₀ ≤ strahler (k - 1) (k - 2) := strahler_mono (by omega) (by omega)
      _ < k := by unfold strahler; split_ifs <;> omega

theorem lt_or_reach_of_proves {k : ℕ} (hk : 1 ≤ k) {g : α} {r : ℕ} (hp : S.Proves g r)
    (hr : r ≤ k) : g ∈ S.lt k ∨ g ∈ S.reach (S.lt k) (S.seeds k) := by
  induction hp with
  | ax h => exact Or.inl ⟨0, by omega, Proves.ax h⟩
  | @unary f g r hu hpf ih =>
    rcases ih hr with ⟨r₀, hr₀, hp₀⟩ | ⟨a, ha, hag⟩
    · exact Or.inl ⟨r₀, hr₀, Proves.unary hu hp₀⟩
    · exact Or.inr ⟨a, ha, hag.tail (Or.inl hu)⟩
  | @binary f f' g r r' hb hpf hpf' ihf ihf' =>
    by_cases hg : g ∈ S.lt k
    · exact Or.inl hg
    right
    have h1 := le_strahler_left r r'
    have h2 := le_strahler_right r r'
    by_cases hrr : r = r'
    · subst hrr
      have hs : strahler r r = r + 1 := by unfold strahler; simp
      exact ⟨g, S.mem_seeds_of_binary hb ⟨r, by omega, hpf⟩ ⟨r, by omega, hpf'⟩ hg,
        Relation.ReflTransGen.refl⟩
    · rcases Nat.lt_or_gt_of_ne hrr with hlt | hlt
      · have hs : strahler r r' = r' := by unfold strahler; split_ifs <;> omega
        have hf : f ∈ S.lt k := ⟨r, by omega, hpf⟩
        rcases ihf' (by omega) with hf' | ⟨a, ha, hag⟩
        · exact ⟨g, S.mem_seeds_of_binary hb hf hf' hg, Relation.ReflTransGen.refl⟩
        · exact ⟨a, ha, hag.tail (Or.inr (Or.inr ⟨f, hf, hb⟩))⟩
      · have hs : strahler r r' = r := by unfold strahler; split_ifs <;> omega
        have hf' : f' ∈ S.lt k := ⟨r', by omega, hpf'⟩
        rcases ihf (by omega) with hf | ⟨a, ha, hag⟩
        · exact ⟨g, S.mem_seeds_of_binary hb hf hf' hg, Relation.ReflTransGen.refl⟩
        · exact ⟨a, ha, hag.tail (Or.inr (Or.inl ⟨f', hf', hb⟩))⟩

/-- Lemma (rank-layer reachability, 005d): for every `k ≥ 1`,
`𝓕_{≤k} = 𝓕_{<k} ∪ Reach_{G_k}(S_k)`, where `G_k = G(𝓕_{<k})`. -/
theorem rank_layer (k : ℕ) (hk : 1 ≤ k) :
    S.le k = S.lt k ∪ S.reach (S.lt k) (S.seeds k) := by
  apply Set.Subset.antisymm
  · rintro g ⟨r, hr, hp⟩
    exact S.lt_or_reach_of_proves hk hp hr
  · exact Set.union_subset (S.lt_subset_le k) (S.le_of_reach (S.seeds_subset_le k hk))

end HornSystem

end GC.Portals
