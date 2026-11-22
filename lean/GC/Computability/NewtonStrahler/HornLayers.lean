import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Logic.Relation
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace GC.NewtonStrahler

/-- A Horn rule `P ⇒ q`; the premises form a set. -/
structure Rule (F : Type*) where
  prem : Finset F
  concl : F

/-- A Horn system `(𝓕, 𝓐, 𝓡)` over the facts `F`: a set of axioms and a finite list of rules
(Definition 2.1). -/
structure HornSystem (F : Type*) where
  axioms : Set F
  rules : List (Rule F)

variable {F : Type*}

/-- Derivation trees (Definition 2.2): an axiom leaf, or a rule `P ⇒ q` of the system with one
child derivation tree for each premise `p ∈ P`. -/
inductive Deriv (H : HornSystem F) : F → Type _ where
  | ax {q : F} (h : q ∈ H.axioms) : Deriv H q
  | node (r : Rule F) (hr : r ∈ H.rules) (sub : ∀ p ∈ r.prem, Deriv H p) : Deriv H r.concl

open Classical in
/-- The Horton–Strahler combination of the ranks `g a`, `a ∈ s`: `0` if `s = ∅`; otherwise the
largest rank `r₁` if it is attained only once, and `r₁ + 1` if it is attained at least twice. -/
noncomputable def hsMax {ι : Type*} (s : Finset ι) (g : ι → ℕ) : ℕ :=
  if ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ g a = s.sup g ∧ g b = s.sup g then s.sup g + 1 else s.sup g

/-- The Horton–Strahler rank of a derivation tree (Definition 2.2). -/
noncomputable def Deriv.rank {H : HornSystem F} : {q : F} → Deriv H q → ℕ
  | _, .ax _ => 0
  | _, .node r _ sub => hsMax r.prem.attach fun p => (sub p.1 p.2).rank


/-! ### The Strahler combination -/

lemma hsMax_le_iff {ι : Type*} (s : Finset ι) (g : ι → ℕ) (k : ℕ) :
    hsMax s g ≤ k ↔
      (∀ a ∈ s, g a ≤ k) ∧ ∀ a ∈ s, ∀ b ∈ s, a ≠ b → min (g a) (g b) < k := by
  classical
  unfold hsMax
  split_ifs with h
  · obtain ⟨a, ha, b, hb, hab, hga, hgb⟩ := h
    constructor
    · intro hk
      refine ⟨fun c hc => ?_, fun c hc d _ _ => ?_⟩
      · have := Finset.le_sup (f := g) hc; omega
      · have := Finset.le_sup (f := g) hc; omega
    · rintro ⟨_, h2⟩
      have := h2 a ha b hb hab
      omega
  · push Not at h
    constructor
    · intro hk
      refine ⟨fun c hc => (Finset.le_sup (f := g) hc).trans hk, fun a ha b hb hab => ?_⟩
      by_contra hcon
      have h1 := Finset.le_sup (f := g) ha
      have h2 := Finset.le_sup (f := g) hb
      have : g a = s.sup g := by omega
      have := h a ha b hb hab this
      omega
    · rintro ⟨h1, -⟩
      exact Finset.sup_le h1

lemma le_hsMax {ι : Type*} {s : Finset ι} (g : ι → ℕ) {a : ι} (ha : a ∈ s) :
    g a ≤ hsMax s g :=
  ((hsMax_le_iff s g _).mp le_rfl).1 a ha

variable {H : HornSystem F}

lemma Deriv.rank_sub_le (r : Rule F) (hr : r ∈ H.rules) (sub : ∀ p ∈ r.prem, Deriv H p)
    (p : F) (hp : p ∈ r.prem) : (sub p hp).rank ≤ (Deriv.node r hr sub).rank := by
  rw [Deriv.rank]
  exact le_hsMax (fun p : r.prem => (sub p.1 p.2).rank) (s := r.prem.attach)
    (Finset.mem_attach _ ⟨p, hp⟩)

lemma Deriv.rank_node_le_iff (r : Rule F) (hr : r ∈ H.rules) (sub : ∀ p ∈ r.prem, Deriv H p)
    (k : ℕ) : (Deriv.node r hr sub).rank ≤ k ↔
      (∀ p (hp : p ∈ r.prem), (sub p hp).rank ≤ k) ∧
      ∀ p (hp : p ∈ r.prem) b (hb : b ∈ r.prem), p ≠ b →
        min (sub p hp).rank (sub b hb).rank < k := by
  rw [Deriv.rank, hsMax_le_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun p hp => h1 ⟨p, hp⟩ (Finset.mem_attach _ _),
      fun p hp b hb hpb => h2 ⟨p, hp⟩ (Finset.mem_attach _ _) ⟨b, hb⟩ (Finset.mem_attach _ _)
        (fun h => hpb (congrArg Subtype.val h))⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun p _ => h1 p.1 p.2,
      fun p _ b _ hpb => h2 p.1 p.2 b.1 b.2 (fun h => hpb (Subtype.ext h))⟩

/-! ### Rank layers -/

/-- `S_k`: the facts with a derivation tree of rank at most `k`. -/
def rankLayer (H : HornSystem F) (k : ℕ) : Set F := {q | ∃ T : Deriv H q, T.rank ≤ k}

/-- `S_{k-1}`: the facts with a derivation tree of rank less than `k` (so `S_{-1} = ∅`). -/
def rankBelow (H : HornSystem F) (k : ℕ) : Set F := {q | ∃ T : Deriv H q, T.rank < k}

/-- The seed set `B_k = X ∪ 𝓐 ∪ {q : (P ⇒ q) ∈ 𝓡, P ⊆ X}` for `X = S_{k-1}`. -/
def seeds (H : HornSystem F) (X : Set F) : Set F :=
  X ∪ H.axioms ∪ {q | ∃ r ∈ H.rules, (↑r.prem : Set F) ⊆ X ∧ r.concl = q}

/-- The graph `G_k` for `X = S_{k-1}`: an edge `p → q` for every rule `P ⇒ q` with
`P \ X = {p}`. -/
def layerEdge (H : HornSystem F) (X : Set F) (p q : F) : Prop :=
  ∃ r ∈ H.rules, (↑r.prem : Set F) \ X = {p} ∧ r.concl = q

/-- `Ŝ_k`: the facts reachable from the seeds in the graph `G_k` (seeds included). -/
def reachLayer (H : HornSystem F) (X : Set F) : Set F :=
  {q | ∃ b ∈ seeds H X, Relation.ReflTransGen (layerEdge H X) b q}

/-- Strahler saturation: start from `∅` and apply one reachability layer per round. -/
def saturate (H : HornSystem F) : ℕ → Set F
  | 0 => ∅
  | t + 1 => reachLayer H (saturate H t)

lemma rankBelow_zero (H : HornSystem F) : rankBelow H 0 = ∅ := by
  ext q; simp [rankBelow]

lemma rankBelow_succ (H : HornSystem F) (k : ℕ) : rankBelow H (k + 1) = rankLayer H k := by
  ext q; simp [rankBelow, rankLayer]

lemma rankBelow_subset_rankLayer (H : HornSystem F) (k : ℕ) :
    rankBelow H k ⊆ rankLayer H k := fun _ ⟨T, hT⟩ => ⟨T, hT.le⟩

/-- A rule all of whose premises lie in `S_{k-1}` puts its conclusion into `S_k`. -/
lemma concl_mem_rankLayer {r : Rule F} (hr : r ∈ H.rules) {k : ℕ}
    (h : ∀ p ∈ r.prem, p ∈ rankBelow H k) : r.concl ∈ rankLayer H k := by
  choose T hT using h
  refine ⟨Deriv.node r hr T, ?_⟩
  rw [Deriv.rank_node_le_iff]
  exact ⟨fun p hp => (hT p hp).le, fun p hp _ _ _ => (min_le_left _ _).trans_lt (hT p hp)⟩

/-- **Theorem 4.1 (exact Strahler layers).** For every `k ≥ 0`, the set of facts reachable in
`G_k` from the seeds `B_k`, both built from `S_{k-1}`, is exactly `S_k`. -/
theorem reachLayer_rankBelow (H : HornSystem F) (k : ℕ) :
    reachLayer H (rankBelow H k) = rankLayer H k := by
  set X := rankBelow H k with hX
  apply Set.Subset.antisymm
  · -- `Ŝ_k ⊆ S_k`
    have hseed : seeds H X ⊆ rankLayer H k := by
      rintro q ((hq | hq) | ⟨r, hr, hsub, rfl⟩)
      · exact rankBelow_subset_rankLayer H k hq
      · exact ⟨Deriv.ax hq, by simp [Deriv.rank]⟩
      · have : ∀ p ∈ r.prem, ∃ T : Deriv H p, T.rank < k := fun p hp => hsub hp
        choose T hT using this
        refine ⟨Deriv.node r hr T, ?_⟩
        rw [Deriv.rank_node_le_iff]
        exact ⟨fun p hp => (hT p hp).le, fun p hp _ _ _ => (min_le_left _ _).trans_lt (hT p hp)⟩
    have hstep : ∀ p q, layerEdge H X p q → p ∈ rankLayer H k → q ∈ rankLayer H k := by
      rintro p q ⟨r, hr, hdiff, rfl⟩ ⟨Tp, hTp⟩
      have hother : ∀ a ∈ r.prem, a ≠ p → a ∈ X := by
        intro a ha hap
        by_contra hax
        have : a ∈ (↑r.prem : Set F) \ X := ⟨ha, hax⟩
        rw [hdiff] at this
        exact hap this
      have : ∀ a ∈ r.prem, ∃ T : Deriv H a, T.rank ≤ k ∧ (a ≠ p → T.rank < k) := by
        intro a ha
        by_cases hap : a = p
        · subst hap; exact ⟨Tp, hTp, fun h => absurd rfl h⟩
        · obtain ⟨T, hT⟩ := hother a ha hap
          exact ⟨T, hT.le, fun _ => hT⟩
      choose T hT using this
      refine ⟨Deriv.node r hr T, ?_⟩
      rw [Deriv.rank_node_le_iff]
      refine ⟨fun a ha => (hT a ha).1, fun a ha b hb hab => ?_⟩
      by_cases hap : a = p
      · subst hap
        exact (min_le_right _ _).trans_lt ((hT b hb).2 (Ne.symm hab))
      · exact (min_le_left _ _).trans_lt ((hT a ha).2 hap)
    rintro q ⟨b, hb, hpath⟩
    induction hpath with
    | refl => exact hseed hb
    | tail _ he ih => exact hstep _ _ he ih
  · -- `S_k ⊆ Ŝ_k`
    rintro q ⟨T, hT⟩
    induction T with
    | ax h => exact ⟨_, Or.inl (Or.inr h), Relation.ReflTransGen.refl⟩
    | node r hr sub ih =>
      rw [Deriv.rank_node_le_iff] at hT
      obtain ⟨hle, hmin⟩ := hT
      by_cases hall : ∀ p (hp : p ∈ r.prem), (sub p hp).rank < k
      · exact ⟨_, Or.inr ⟨r, hr, fun p hp => ⟨sub p hp, hall p hp⟩, rfl⟩,
          Relation.ReflTransGen.refl⟩
      · push Not at hall
        obtain ⟨p, hp, hpk⟩ := hall
        have hothers : ∀ b ∈ r.prem, b ≠ p → b ∈ X := by
          intro b hb hbp
          have := hmin p hp b hb (Ne.symm hbp)
          have := hle p hp
          exact ⟨sub b hb, by omega⟩
        by_cases hpX : p ∈ X
        · refine ⟨_, Or.inr ⟨r, hr, fun b hb => ?_, rfl⟩, Relation.ReflTransGen.refl⟩
          by_cases hbp : b = p
          · exact hbp ▸ hpX
          · exact hothers b hb hbp
        · obtain ⟨b0, hb0, hpath⟩ := ih p hp (hle p hp)
          refine ⟨b0, hb0, hpath.tail ⟨r, hr, ?_, rfl⟩⟩
          ext a
          simp only [Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff]
          constructor
          · rintro ⟨ha, haX⟩
            by_contra hap
            exact haX (hothers a ha hap)
          · rintro rfl
            exact ⟨hp, hpX⟩

/-- The saturation iteration after `t` rounds is `S_{t-1}`. -/
theorem saturate_eq_rankBelow (H : HornSystem F) (t : ℕ) : saturate H t = rankBelow H t := by
  induction t with
  | zero => rw [saturate, rankBelow_zero]
  | succ t ih => rw [saturate, ih, reachLayer_rankBelow, rankBelow_succ]

/-- **Theorem 4.1 / Theorem 5.1 (round count).** `K + 1` reachability rounds of Strahler
saturation compute exactly the set `S_K` of facts of proof rank at most `K`. -/
theorem saturate_succ (H : HornSystem F) (K : ℕ) : saturate H (K + 1) = rankLayer H K := by
  rw [saturate_eq_rankBelow, rankBelow_succ]

/-! ### Stabilization -/

lemma rankLayer_mono (H : HornSystem F) {k l : ℕ} (h : k ≤ l) :
    rankLayer H k ⊆ rankLayer H l := fun _ ⟨T, hT⟩ => ⟨T, hT.trans h⟩

lemma rankBelow_mono (H : HornSystem F) {k l : ℕ} (h : k ≤ l) :
    rankBelow H k ⊆ rankBelow H l := fun _ ⟨T, hT⟩ => ⟨T, lt_of_lt_of_le hT h⟩

/-- **Corollary 4.2 (stabilization).** If `S_k = S_{k-1}` then `S_j = S_k` for all `j ≥ k`
(stated with `rankBelow H (k+1) = S_k` and `rankBelow H k = S_{k-1}`). -/
theorem rankBelow_stable (H : HornSystem F) {k : ℕ}
    (h : rankBelow H (k + 1) = rankBelow H k) : ∀ j ≥ k, rankBelow H j = rankBelow H k := by
  have hstep : ∀ t, rankBelow H (t + 1) = reachLayer H (rankBelow H t) := fun t => by
    rw [reachLayer_rankBelow, rankBelow_succ]
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => rfl
  | succ j hkj ih => rw [hstep, ih, ← hstep, h]

/-- **Corollary 4.2, last claim.** Over a finite set of facts, every derivable fact has proof
rank at most `|𝓕| - 1`. -/
theorem derivable_mem_rankLayer [Fintype F] {q : F} (T : Deriv H q) :
    q ∈ rankLayer H (Fintype.card F - 1) := by
  classical
  -- some round `t ≤ |𝓕|` is stable
  have hex : ∃ t ≤ Fintype.card F, rankBelow H (t + 1) = rankBelow H t := by
    by_contra hcon
    push Not at hcon
    have hgrow : ∀ t ≤ Fintype.card F + 1, t ≤ (rankBelow H t).ncard := by
      intro t
      induction t with
      | zero => intro _; exact Nat.zero_le _
      | succ t ih =>
        intro ht
        have hss : rankBelow H t ⊂ rankBelow H (t + 1) :=
          Set.ssubset_iff_subset_ne.mpr ⟨rankBelow_mono H (Nat.le_succ t),
            fun h => hcon t (by omega) h.symm⟩
        have := Set.ncard_lt_ncard hss
        have := ih (by omega)
        omega
    have h1 := hgrow (Fintype.card F + 1) le_rfl
    have h2 := Set.ncard_le_card (rankBelow H (Fintype.card F + 1))
    rw [Nat.card_eq_fintype_card] at h2
    omega
  obtain ⟨t, ht, hst⟩ := hex
  have hstable := rankBelow_stable H hst
  have hcard : 0 < Fintype.card F := Fintype.card_pos_iff.mpr ⟨q⟩
  have hqmem : q ∈ rankBelow H (T.rank + 1) := ⟨T, Nat.lt_succ_self _⟩
  have hsub : rankBelow H (T.rank + 1) ⊆ rankBelow H (Fintype.card F) := by
    rcases le_or_gt (T.rank + 1) (Fintype.card F) with hle | hlt
    · exact rankBelow_mono H hle
    · rw [hstable _ (by omega), hstable _ ht]
  have := hsub hqmem
  rwa [show Fintype.card F = Fintype.card F - 1 + 1 by omega, rankBelow_succ] at this

/-! ### Relation to Newton's method over the Boolean semiring -/

/-- The one-step operator `f(X) = 𝓐 ∪ {q : (P ⇒ q) ∈ 𝓡, P ⊆ X}`. -/
def hornStep (H : HornSystem F) (X : Set F) : Set F :=
  H.axioms ∪ {q | ∃ r ∈ H.rules, (↑r.prem : Set F) ⊆ X ∧ r.concl = q}

/-- The graph `D_X` of the differential `Df_X`: an edge `p → q` whenever some rule `P ⇒ q`
has `p ∈ P` and `P \ {p} ⊆ X`. -/
def diffEdge (H : HornSystem F) (X : Set F) (p q : F) : Prop :=
  ∃ r ∈ H.rules, p ∈ r.prem ∧ (↑r.prem : Set F) \ {p} ⊆ X ∧ r.concl = q

/-- The Boolean Newton operator `N(X) = Df_X^*(f(X))`. -/
def hornNewton (H : HornSystem F) (X : Set F) : Set F :=
  {q | ∃ b ∈ hornStep H X, Relation.ReflTransGen (diffEdge H X) b q}

lemma rankBelow_subset_hornStep (H : HornSystem F) (k : ℕ) :
    rankBelow H k ⊆ hornStep H (rankBelow H k) := by
  rintro q ⟨T, hT⟩
  cases T with
  | ax h => exact Or.inl h
  | node r hr sub =>
    exact Or.inr ⟨r, hr, fun p hp =>
      ⟨sub p hp, lt_of_le_of_lt (Deriv.rank_sub_le r hr sub p hp) hT⟩, rfl⟩

/-- **Proposition 6.1 (layers are Newton iterates).** `S_k = N(S_{k-1})`. -/
theorem hornNewton_rankBelow (H : HornSystem F) (k : ℕ) :
    hornNewton H (rankBelow H k) = rankLayer H k := by
  rw [← reachLayer_rankBelow]
  set X := rankBelow H k
  have hpost := rankBelow_subset_hornStep H k
  apply Set.Subset.antisymm
  · rintro q ⟨b, hb, hpath⟩
    induction hpath with
    | refl =>
      rcases hb with hb | hb
      · exact ⟨b, Or.inl (Or.inr hb), Relation.ReflTransGen.refl⟩
      · exact ⟨b, Or.inr hb, Relation.ReflTransGen.refl⟩
    | @tail c d _ he ih =>
      obtain ⟨r, hr, hcr, hsub, rfl⟩ := he
      by_cases hcX : c ∈ X
      · refine ⟨_, Or.inr ⟨r, hr, fun a ha => ?_, rfl⟩, Relation.ReflTransGen.refl⟩
        by_cases hac : a = c
        · exact hac ▸ hcX
        · exact hsub ⟨ha, hac⟩
      · obtain ⟨b0, hb0, hp⟩ := ih
        refine ⟨b0, hb0, hp.tail ⟨r, hr, ?_, rfl⟩⟩
        ext a
        simp only [Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff]
        constructor
        · rintro ⟨ha, haX⟩
          by_contra hac
          exact haX (hsub ⟨ha, hac⟩)
        · rintro rfl
          exact ⟨hcr, hcX⟩
  · rintro q ⟨b, hb, hpath⟩
    refine ⟨b, ?_, Relation.ReflTransGen.mono (fun c d he => ?_) _ _ hpath⟩
    · rcases hb with (hb | hb) | hb
      · exact hpost hb
      · exact Or.inl hb
      · exact Or.inr hb
    · obtain ⟨r, hr, hdiff, rfl⟩ := he
      have hc : c ∈ (↑r.prem : Set F) \ X := by rw [hdiff]; rfl
      refine ⟨r, hr, hc.1, fun a ⟨ha, hac⟩ => ?_, rfl⟩
      by_contra haX
      have : a ∈ (↑r.prem : Set F) \ X := ⟨ha, haX⟩
      rw [hdiff] at this
      exact hac this

/-- **Proposition 6.1, second claim.** `S_k = N^{k+1}(∅)`. -/
theorem hornNewton_iterate (H : HornSystem F) (k : ℕ) :
    (hornNewton H)^[k + 1] ∅ = rankLayer H k := by
  have : ∀ t, (hornNewton H)^[t] ∅ = rankBelow H t := by
    intro t
    induction t with
    | zero => simp [rankBelow_zero]
    | succ t ih =>
      rw [Function.iterate_succ_apply', ih, hornNewton_rankBelow, rankBelow_succ]
  rw [this, rankBelow_succ]

/-! ### Leaves and the few-leaves corollary -/

/-- The number of leaves of a derivation tree (a node with no children is a leaf). -/
def Deriv.leaves : {q : F} → Deriv H q → ℕ
  | _, .ax _ => 1
  | _, .node r _ sub => max 1 (∑ p ∈ r.prem.attach, (sub p.1 p.2).leaves)

/-- **Lemma 2.3(b).** A derivation tree of rank `r` has at least `2^r` leaves. -/
theorem Deriv.two_pow_rank_le_leaves {q : F} (T : Deriv H q) : 2 ^ T.rank ≤ T.leaves := by
  classical
  induction T with
  | ax h => simp [Deriv.rank, Deriv.leaves]
  | node r hr sub ih =>
    rw [Deriv.leaves]
    rcases r.prem.eq_empty_or_nonempty with hempty | hpne
    · have : r.prem.attach = ∅ := Finset.attach_eq_empty_iff.mpr hempty
      simp [Deriv.rank, hsMax, this]
    · refine le_trans ?_ (le_max_right _ _)
      set g : r.prem → ℕ := fun p => (sub p.1 p.2).rank
      set l : r.prem → ℕ := fun p => (sub p.1 p.2).leaves
      have hgl : ∀ p, 2 ^ g p ≤ l p := fun p => ih p.1 p.2
      have hne : r.prem.attach.Nonempty := Finset.attach_nonempty_iff.mpr hpne
      rw [Deriv.rank]
      change 2 ^ hsMax r.prem.attach g ≤ ∑ p ∈ r.prem.attach, l p
      unfold hsMax
      split_ifs with h2
      · obtain ⟨a, ha, b, hb, hab, hga, hgb⟩ := h2
        calc 2 ^ (r.prem.attach.sup g + 1) = 2 ^ g a + 2 ^ g b := by
              rw [hga, hgb, pow_succ, mul_two]
          _ ≤ l a + l b := Nat.add_le_add (hgl a) (hgl b)
          _ = ∑ p ∈ {a, b}, l p := (Finset.sum_pair hab).symm
          _ ≤ ∑ p ∈ r.prem.attach, l p :=
              Finset.sum_le_sum_of_subset_of_nonneg (by
                intro x hx
                simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                rcases hx with rfl | rfl <;> assumption) (fun _ _ _ => Nat.zero_le _)
      · obtain ⟨a, ha, hsup⟩ := Finset.exists_mem_eq_sup _ hne g
        rw [hsup]
        exact (hgl a).trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) ha)

/-- **Corollary 5.3 (few leaves), rank part.** A fact with a derivation tree with at most `L`
leaves lies in `S_{⌊log₂ L⌋}`. -/
theorem mem_rankLayer_of_leaves_le {q : F} (T : Deriv H q) {L : ℕ} (hL : T.leaves ≤ L) :
    q ∈ rankLayer H (Nat.log 2 L) :=
  ⟨T, Nat.le_log_of_pow_le one_lt_two ((Deriv.two_pow_rank_le_leaves T).trans hL)⟩

/-- **Corollary 5.3 (few leaves), round part.** If every derivable fact has a derivation tree
with at most `L` leaves, then `⌊log₂ L⌋ + 1` rounds of Strahler saturation compute the set of
all derivable facts. -/
theorem saturate_eq_derivable_of_leaves {L : ℕ}
    (hL : ∀ q (_ : Deriv H q), ∃ T' : Deriv H q, T'.leaves ≤ L) :
    saturate H (Nat.log 2 L + 1) = {q | Nonempty (Deriv H q)} := by
  rw [saturate_succ]
  ext q
  constructor
  · rintro ⟨T, -⟩; exact ⟨T⟩
  · rintro ⟨T⟩
    obtain ⟨T', hT'⟩ := hL q T
    exact mem_rankLayer_of_leaves_le T' hT'

end GC.NewtonStrahler
