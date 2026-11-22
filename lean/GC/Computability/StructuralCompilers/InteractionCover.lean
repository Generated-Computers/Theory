import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.IntervalCases

/-!
# Interaction covers and the corrected residual evaluator (manuscript 007a, Section 4)

The binary core of a Sequential NOR instance is a list of normalized records
`z_k = c`, `z_k = z_a ⊕ σ` or `z_k = NOR(z_a ⊕ σ, z_c ⊕ τ)` (`a, c < k`, `a ≠ c`).
The interaction graph joins the two sources of every binary record; `C(j)` takes, in each
component, the left or the right sources (Definition 4.4).

* `interactionCover_isVertexCover` : `C(j)` meets every binary record (Lemma 4.5, first part).
* `record_unary_outside_cover` : relative to fixed cover values, every record outside the cover
  is a unary map of one earlier non-cover variable (or of the virtual root `0` of value `1`),
  and the map depends only on cover values below `k` (Lemma 4.5, second part; see the note on
  the number of cover values below).
* `residual_eq_ancestryProduct` : the corrected proof of Theorem 4.6: the residual value
  `y_k(X)` is `F^X_k(1)` with `F^X_k = h_{k,m} ∘ ⋯ ∘ h_{k,1}`, `h_{k,i} = f^X_i` if `i` is on
  the pointer chain of `k` and `id` otherwise.
* `source_compression_claim_false` : the claim of the source notes that the residual compresses
  to signed copies of single cover variables is false (Remark 4.7).
-/

namespace GC.StructuralCompilers

/-- A normalized record of a core gate (Section 2.3). -/
inductive CoreRecord
  /-- `z_k = c` -/
  | const (c : Bool)
  /-- `z_k = z_a ⊕ σ` -/
  | copy (a : ℕ) (σ : Bool)
  /-- `z_k = NOR(z_a ⊕ σ, z_c ⊕ τ)`; `a` is the left and `c` the right source -/
  | bin (a : ℕ) (σ : Bool) (c : ℕ) (τ : Bool)

/-- Evaluation of a record on an assignment `z`. -/
def CoreRecord.eval : CoreRecord → (ℕ → Bool) → Bool
  | const c, _ => c
  | copy a σ, z => xor (z a) σ
  | bin a σ c τ, z => !(xor (z a) σ || xor (z c) τ)

/-- A record of gate `k` is well formed if it mentions only core variables `1 ≤ a < k`, and the
two sources of a binary record are distinct. -/
def CoreRecord.WF (k : ℕ) : CoreRecord → Prop
  | const _ => True
  | copy a _ => 1 ≤ a ∧ a < k
  | bin a _ c _ => 1 ≤ a ∧ a < k ∧ 1 ≤ c ∧ c < k ∧ a ≠ c

/-- A normalized core of size `m`: records for the gates `1, …, m`. -/
structure CoreSystem where
  /-- number of core gates -/
  m : ℕ
  /-- the record of gate `k` (only `1 ≤ k ≤ m` matters) -/
  record : ℕ → CoreRecord
  /-- well-formedness -/
  wf : ∀ k, 1 ≤ k → k ≤ m → (record k).WF k

/-- `a` and `c` are the left and right sources of a binary record of the core. -/
def CoreSystem.BinEdge (S : CoreSystem) (a c : ℕ) : Prop :=
  ∃ k, 1 ≤ k ∧ k ≤ S.m ∧ ∃ σ τ, S.record k = CoreRecord.bin a σ c τ

/-- The interaction graph `G_int(j)`: an edge `{a, c}` for every binary record. -/
def CoreSystem.intGraph (S : CoreSystem) : SimpleGraph ℕ := SimpleGraph.fromRel S.BinEdge

/-- Left sources. -/
def CoreSystem.leftSources (S : CoreSystem) : Set ℕ := {a | ∃ c, S.BinEdge a c}

/-- Right sources. -/
def CoreSystem.rightSources (S : CoreSystem) : Set ℕ := {c | ∃ a, S.BinEdge a c}

/-- The cover obtained from a choice of side (`true` = left sources, `false` = right sources) in
every connected component of the interaction graph. -/
def CoreSystem.sideCover (S : CoreSystem) (side : S.intGraph.ConnectedComponent → Bool) :
    Set ℕ :=
  {v | (side (S.intGraph.connectedComponentMk v) = true ∧ v ∈ S.leftSources) ∨
       (side (S.intGraph.connectedComponentMk v) = false ∧ v ∈ S.rightSources)}

open Classical in
/-- The side rule of Definition 4.4: in each component take the smaller of `L ∩ K` and `R ∩ K`,
the left one on ties. -/
noncomputable def CoreSystem.paperSide (S : CoreSystem) (K : S.intGraph.ConnectedComponent) :
    Bool :=
    decide ({v | v ∈ S.leftSources ∧ S.intGraph.connectedComponentMk v = K}.ncard ≤
      {v | v ∈ S.rightSources ∧ S.intGraph.connectedComponentMk v = K}.ncard)

/-- The interaction cover `C(j)` of Definition 4.4. -/
def CoreSystem.interactionCover (S : CoreSystem) : Set ℕ := S.sideCover S.paperSide

/-- Lemma 4.5 (first part), for every side rule: the side cover meets every binary record. -/
theorem sideCover_isVertexCover (S : CoreSystem) (side : S.intGraph.ConnectedComponent → Bool)
    {a c : ℕ} (h : S.BinEdge a c) : a ∈ S.sideCover side ∨ c ∈ S.sideCover side := by
  have hac : a ≠ c := by
    obtain ⟨k, hk1, hkm, σ, τ, hr⟩ := h
    have := S.wf k hk1 hkm
    rw [hr] at this
    exact this.2.2.2.2
  have hadj : S.intGraph.Adj a c := by
    rw [CoreSystem.intGraph, SimpleGraph.fromRel_adj]
    exact ⟨hac, Or.inl h⟩
  have hcomp := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj
  simp only [CoreSystem.sideCover, Set.mem_ofPred_eq, hcomp]
  cases hs : side (S.intGraph.connectedComponentMk c)
  · exact Or.inr (Or.inr ⟨rfl, a, h⟩)
  · exact Or.inl (Or.inl ⟨rfl, c, h⟩)

/-- **Lemma 4.5 (first part).** `C(j)` is a vertex cover of the interaction graph: every binary
record has a source in `C(j)`. -/
theorem interactionCover_isVertexCover (S : CoreSystem) {a c : ℕ} (h : S.BinEdge a c) :
    a ∈ S.interactionCover ∨ c ∈ S.interactionCover :=
  sideCover_isVertexCover S S.paperSide h

/-- A set `C` meets every binary record of the core. -/
def CoreSystem.IsCover (S : CoreSystem) (C : Set ℕ) : Prop :=
  ∀ a c, S.BinEdge a c → a ∈ C ∨ c ∈ C

lemma interactionCover_isCover (S : CoreSystem) : S.IsCover S.interactionCover :=
  fun _ _ h => interactionCover_isVertexCover S h

/-- **Lemma 4.5 (second part).** Let `C` meet every binary record. Every gate `k ∉ C` has a
pointer `p < k`, either the virtual root `0` or a variable outside `C`, and a unary map
`f z : Bool → Bool`, determined by the values of `z` on the cover variables below `k`, such that
the record of `k` evaluates to `f z (z p)` whenever `z 0 = 1`. -/
theorem record_unary_outside_cover (S : CoreSystem) (C : Set ℕ) (hC : S.IsCover C)
    (k : ℕ) (hk1 : 1 ≤ k) (hkm : k ≤ S.m) :
    ∃ p, p < k ∧ (p = 0 ∨ p ∉ C) ∧
      ∃ f : (ℕ → Bool) → Bool → Bool,
        (∀ z z', (∀ i, 1 ≤ i → i < k → i ∈ C → z i = z' i) → f z = f z') ∧
        ∀ z, z 0 = true → (S.record k).eval z = f z (z p) := by
  classical
  have hwf := S.wf k hk1 hkm
  cases hr : S.record k with
  | const c =>
    exact ⟨0, by omega, Or.inl rfl, fun _ _ => c, fun _ _ _ => rfl, fun z _ => rfl⟩
  | copy a σ =>
    rw [hr] at hwf
    obtain ⟨ha1, hak⟩ := hwf
    by_cases ha : a ∈ C
    · refine ⟨0, by omega, Or.inl rfl, fun z _ => xor (z a) σ, ?_, fun z _ => rfl⟩
      intro z z' h
      funext b
      simp only [h a ha1 hak ha]
    · exact ⟨a, hak, Or.inr ha, fun _ b => xor b σ, fun _ _ _ => rfl, fun z _ => rfl⟩
  | bin a σ c τ =>
    rw [hr] at hwf
    obtain ⟨ha1, hak, hc1, hck, hac⟩ := hwf
    have hcov := hC a c ⟨k, hk1, hkm, σ, τ, hr⟩
    by_cases ha : a ∈ C <;> by_cases hc : c ∈ C
    · refine ⟨0, by omega, Or.inl rfl, fun z _ => !(xor (z a) σ || xor (z c) τ), ?_,
        fun z _ => rfl⟩
      intro z z' h
      funext b
      simp only [h a ha1 hak ha, h c hc1 hck hc]
    · refine ⟨c, hck, Or.inr hc, fun z b => !(xor (z a) σ || xor b τ), ?_, fun z _ => rfl⟩
      intro z z' h
      funext b
      simp only [h a ha1 hak ha]
    · refine ⟨a, hak, Or.inr ha, fun z b => !(xor b σ || xor (z c) τ), ?_, fun z _ => rfl⟩
      intro z z' h
      funext b
      simp only [h c hc1 hck hc]
    · exact absurd hcov (by tauto)

/-! ### Residual semantics (Definition 2.6) and the corrected evaluator -/

open Classical in
/-- The residual semantics `y(X)`: the exceptional variables `k ∈ E` take the values `X k`, the
other gates are evaluated from their records in increasing order; index `0` is a virtual node of
value `1`. -/
noncomputable def CoreSystem.residual (S : CoreSystem) (E : Set ℕ) (X : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | k + 1 =>
      if k + 1 ∈ E then X (k + 1)
      else (S.record (k + 1)).eval (fun i => if _h : i < k + 1 then S.residual E X i else false)

/-- `i` lies on the pointer chain `k, p k, p (p k), …`. -/
def OnChain (p : ℕ → ℕ) (k i : ℕ) : Prop := ∃ t, p^[t] k = i

open Classical in
/-- The ordered ancestry product `h_{k,n} ∘ ⋯ ∘ h_{k,1}` with `h_{k,i} = F i` if `i` lies on the
chain of `k` and `i ∉ C`, and `h_{k,i} = id` otherwise (proof of Theorem 4.6). -/
noncomputable def ancestryProduct (p : ℕ → ℕ) (C : Set ℕ) (F : ℕ → Bool → Bool) (k : ℕ) :
    ℕ → Bool → Bool
  | 0 => id
  | n + 1 =>
      (if OnChain p k (n + 1) ∧ n + 1 ∉ C then F (n + 1) else id) ∘
        ancestryProduct p C F k n

lemma residual_zero (S : CoreSystem) (E : Set ℕ) (X : ℕ → Bool) : S.residual E X 0 = true := by
  rw [CoreSystem.residual]

lemma residual_of_mem (S : CoreSystem) (E : Set ℕ) (X : ℕ → Bool) {k : ℕ} (hk : 1 ≤ k)
    (h : k ∈ E) : S.residual E X k = X k := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [CoreSystem.residual]
  simp [h]

lemma residual_of_not_mem (S : CoreSystem) (E : Set ℕ) (X : ℕ → Bool) {k : ℕ} (hk1 : 1 ≤ k)
    (hkm : k ≤ S.m) (h : k ∉ E) : S.residual E X k = (S.record k).eval (S.residual E X) := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [CoreSystem.residual]
  simp only [h, if_false]
  have hwf := S.wf (k + 1) hk1 hkm
  cases hr : S.record (k + 1) with
  | const c => rfl
  | copy a σ =>
    rw [hr] at hwf
    simp [CoreRecord.eval, hwf.2]
  | bin a σ c τ =>
    rw [hr] at hwf
    simp [CoreRecord.eval, hwf.2.1, hwf.2.2.2.1]

lemma onChain_iff (p : ℕ → ℕ) (k i : ℕ) : OnChain p k i ↔ i = k ∨ OnChain p (p k) i := by
  constructor
  · rintro ⟨t, ht⟩
    rcases t with _ | t
    · exact Or.inl ht.symm
    · exact Or.inr ⟨t, by rw [← ht, Function.iterate_succ_apply]⟩
  · rintro (rfl | ⟨t, ht⟩)
    · exact ⟨0, rfl⟩
    · exact ⟨t + 1, by rw [Function.iterate_succ_apply, ht]⟩

lemma ancestryProduct_congr (p : ℕ → ℕ) (C : Set ℕ) (F : ℕ → Bool → Bool) (k k' : ℕ) (n : ℕ)
    (h : ∀ i, 1 ≤ i → i ≤ n → (OnChain p k i ↔ OnChain p k' i)) :
    ancestryProduct p C F k n = ancestryProduct p C F k' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [ancestryProduct]
    rw [ih (fun i h1 h2 => h i h1 (by omega)), h (n + 1) (by omega) le_rfl]

/-- The ancestry product equals the composition along the pointer chain, for every `n ≥ k`. -/
lemma ancestryProduct_eq_chain (p : ℕ → ℕ) (C : Set ℕ) (F : ℕ → Bool → Bool)
    (hp0 : p 0 = 0) (hp : ∀ k, 1 ≤ k → k ∉ C → p k < k ∧ (p k = 0 ∨ p k ∉ C)) :
    ∀ k, (k = 0 ∨ k ∉ C) → ∀ n, k ≤ n → ∀ b,
      ancestryProduct p C F k n b =
        if k = 0 then b else F k (ancestryProduct p C F (p k) n b) := by
  -- first: factors beyond the chain are the identity
  have hle : ∀ k, (k = 0 ∨ k ∉ C) → ∀ i, OnChain p k i → i ≤ k ∧ (i = 0 ∨ i ∉ C) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk i hi
      rcases (onChain_iff p k i).1 hi with rfl | hi'
      · exact ⟨le_rfl, hk⟩
      · rcases Nat.eq_zero_or_pos k with rfl | hkpos
        · obtain ⟨t, ht⟩ := hi'
          have hz : ∀ t, p^[t] 0 = 0 := by
            intro t
            induction t with
            | zero => rfl
            | succ t iht => rw [Function.iterate_succ_apply, hp0, iht]
          rw [hp0, hz] at ht
          exact ⟨by omega, Or.inl ht.symm⟩
        · have hkC : k ∉ C := hk.resolve_left (by omega)
          obtain ⟨hlt, hpk⟩ := hp k hkpos hkC
          have := ih (p k) hlt hpk i hi'
          exact ⟨by omega, this.2⟩
  have hbeyond : ∀ k, (k = 0 ∨ k ∉ C) → ∀ n, k ≤ n →
      ancestryProduct p C F k n = ancestryProduct p C F k k := by
    intro k hk n hn
    induction n with
    | zero => rw [show k = 0 by omega]
    | succ n ih =>
      rcases Nat.lt_or_ge k (n + 1) with hlt | hge
      · simp only [ancestryProduct]
        have : ¬ OnChain p k (n + 1) := fun hc => by have := (hle k hk _ hc).1; omega
        simp only [this, false_and, if_false, Function.id_comp]
        exact ih (by omega)
      · rw [show k = n + 1 by omega]
  intro k hk n hn b
  rw [hbeyond k hk n hn]
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · simp [ancestryProduct]
  · have hkC : k ∉ C := hk.resolve_left (by omega)
    obtain ⟨hlt, hpk⟩ := hp k hkpos hkC
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [ancestryProduct, Nat.add_one_ne_zero, if_false]
    have hon : OnChain p (k + 1) (k + 1) := ⟨0, rfl⟩
    simp only [hon, hkC, not_false_eq_true, and_self, if_true, Function.comp_apply]
    have e1 : ancestryProduct p C F (p (k + 1)) n = ancestryProduct p C F (p (k + 1)) k := by
      rw [hbeyond _ hpk n (by omega), hbeyond _ hpk k (by omega)]
    rw [e1, ancestryProduct_congr p C F (k + 1) (p (k + 1)) k]
    intro i hi1 hik
    rw [onChain_iff p (k + 1) i]
    constructor
    · rintro (rfl | h)
      · omega
      · exact h
    · exact Or.inr

/-- **Theorem 4.6, corrected residual evaluator.** Let `C` meet every binary record. There are a
pointer map `p` (with `p k < k`, `p k = 0` or `p k ∉ C`) and unary maps `f X k`, each determined
by the values of `X` on the cover variables below `k`, such that for every assignment `X` of the
cover variables and every gate `k ∉ C` of the core, the residual value is
`y_k(X) = (h_{k,m} ∘ ⋯ ∘ h_{k,1})(1)`, where `h_{k,i} = f X i` if `i` lies on the pointer chain of
`k` and `h_{k,i} = id` otherwise. -/
theorem residual_eq_ancestryProduct (S : CoreSystem) (C : Set ℕ) (hC : S.IsCover C) :
    ∃ (p : ℕ → ℕ) (f : (ℕ → Bool) → ℕ → Bool → Bool),
      (∀ k, 1 ≤ k → k ≤ S.m → k ∉ C → p k < k ∧ (p k = 0 ∨ p k ∉ C)) ∧
      (∀ X X' k, (∀ i, 1 ≤ i → i < k → i ∈ C → X i = X' i) → f X k = f X' k) ∧
      ∀ X k, 1 ≤ k → k ≤ S.m → k ∉ C →
        S.residual C X k = ancestryProduct p C (f X) k S.m true := by
  classical
  have hloc := record_unary_outside_cover S C hC
  -- choose pointers and maps
  let good : ℕ → Prop := fun k => 1 ≤ k ∧ k ≤ S.m ∧ k ∉ C
  let p : ℕ → ℕ := fun k => if h : good k then Classical.choose (hloc k h.1 h.2.1) else 0
  have hpspec : ∀ k (h : good k), p k = Classical.choose (hloc k h.1 h.2.1) := by
    intro k h; simp [p, h]
  let f0 : ℕ → (ℕ → Bool) → Bool → Bool := fun k =>
    if h : good k then Classical.choose (Classical.choose_spec (hloc k h.1 h.2.1)).2.2
    else fun _ b => b
  let f : (ℕ → Bool) → ℕ → Bool → Bool := fun X k => f0 k X
  have hfspec : ∀ k (h : good k),
      (∀ z z', (∀ i, 1 ≤ i → i < k → i ∈ C → z i = z' i) → f0 k z = f0 k z') ∧
      ∀ z, z 0 = true → (S.record k).eval z = f0 k z (z (p k)) := by
    intro k h
    have := Classical.choose_spec (Classical.choose_spec (hloc k h.1 h.2.1)).2.2
    simp only [f0, h, dif_pos, hpspec k h]
    exact this
  have hp : ∀ k, 1 ≤ k → k ∉ C → p k < k ∧ (p k = 0 ∨ p k ∉ C) := by
    intro k hk1 hkC
    by_cases h : good k
    · rw [hpspec k h]
      exact (Classical.choose_spec (hloc k h.1 h.2.1)).imp id (fun h' => h'.1)
    · have h0 : p k = 0 := by simp [p, h]
      exact ⟨by omega, Or.inl h0⟩
  have hp0 : p 0 = 0 := by simp [p, good]
  refine ⟨p, f, fun k hk1 _ hkC => hp k hk1 hkC, ?_, ?_⟩
  · intro X X' k h
    by_cases hg : good k
    · exact (hfspec k hg).1 X X' h
    · simp [f, f0, hg]
  · -- residual values follow the chain
    have hres : ∀ X k, (k = 0 ∨ good k) →
        S.residual C X k = if k = 0 then true else f X k (S.residual C X (p k)) := by
      intro X k hk
      rcases hk with rfl | hg
      · simp [residual_zero]
      · have hk0 : k ≠ 0 := by have := hg.1; omega
        rw [if_neg hk0, residual_of_not_mem S C X hg.1 hg.2.1 hg.2.2,
          (hfspec k hg).2 _ (residual_zero S C X)]
        have := (hfspec k hg).1 (S.residual C X) X (fun i hi _ hiC =>
          residual_of_mem S C X hi hiC)
        simp only [f]
        rw [this]
    intro X k hk1 hkm hkC
    have hchain := ancestryProduct_eq_chain p C (f X) hp0 hp
    -- strong induction along the chain
    have key : ∀ k, (k = 0 ∨ good k) → ∀ n, k ≤ n → n ≤ S.m →
        S.residual C X k = ancestryProduct p C (f X) k n true := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        intro hk n hkn hnm
        rcases hk with rfl | hg
        · rw [hchain 0 (Or.inl rfl) n hkn true]
          simp [residual_zero]
        · have hk0 : k ≠ 0 := by have := hg.1; omega
          rw [hres X k (Or.inr hg), hchain k (Or.inr hg.2.2) n hkn true, if_neg hk0,
            if_neg hk0]
          obtain ⟨hlt, hpk⟩ := hp k hg.1 hg.2.2
          have hpk' : p k = 0 ∨ good (p k) := by
            rcases hpk with h0 | hnC
            · exact Or.inl h0
            · rcases Nat.eq_zero_or_pos (p k) with h0 | hpos
              · exact Or.inl h0
              · exact Or.inr ⟨hpos, by have := hg.2.1; omega, hnC⟩
          rw [ih (p k) hlt hpk' n (by omega) hnm]
    exact key k (Or.inr ⟨hk1, hkm, hkC⟩) S.m hkm le_rfl

/-! ### The counterexample to the source's compression claim (Remark 4.7) -/

/-- The chain of Remark 4.7 with two stages: `y₀ = 1` (gate 1), cover variables `c₁` (gate 2)
and `c₂` (gate 5), `a_r = NOR(c_r, y_{r-1})`, `y_r = NOR(c_r, a_r)` (gates 3, 4, 6, 7). -/
def chainExample : CoreSystem where
  m := 7
  record := fun k =>
    match k with
    | 1 => .const true
    | 2 => .const false
    | 3 => .bin 2 false 1 false
    | 4 => .bin 2 false 3 false
    | 5 => .const false
    | 6 => .bin 5 false 4 false
    | 7 => .bin 5 false 6 false
    | _ => .const false
  wf := by
    intro k hk1 hkm
    interval_cases k <;> simp [CoreRecord.WF]

/-- The cover variables of the chain. -/
def chainCover : Set ℕ := {2, 5}

lemma chainCover_isCover : chainExample.IsCover chainCover := by
  rintro a c ⟨k, hk1, hkm, σ, τ, hr⟩
  simp only [chainExample] at hkm hr
  interval_cases k <;> simp_all [chainCover]

lemma chainExample_y7 (X : ℕ → Bool) :
    chainExample.residual chainCover X 7 = (!X 2 && !X 5) := by
  have h : ∀ k, 1 ≤ k → k ≤ 7 → k ∉ chainCover →
      chainExample.residual chainCover X k =
        (chainExample.record k).eval (chainExample.residual chainCover X) :=
    fun k h1 h2 h3 => residual_of_not_mem _ _ _ h1 h2 h3
  have h2 : chainExample.residual chainCover X 2 = X 2 :=
    residual_of_mem _ _ _ (by norm_num) (by simp [chainCover])
  have h5 : chainExample.residual chainCover X 5 = X 5 :=
    residual_of_mem _ _ _ (by norm_num) (by simp [chainCover])
  have h1 := h 1 (by norm_num) (by norm_num) (by simp [chainCover])
  have h3 := h 3 (by norm_num) (by norm_num) (by simp [chainCover])
  have h4 := h 4 (by norm_num) (by norm_num) (by simp [chainCover])
  have h6 := h 6 (by norm_num) (by norm_num) (by simp [chainCover])
  have h7 := h 7 (by norm_num) (by norm_num) (by simp [chainCover])
  rw [show chainExample.record 1 = .const true from rfl] at h1
  rw [show chainExample.record 3 = .bin 2 false 1 false from rfl] at h3
  rw [show chainExample.record 4 = .bin 2 false 3 false from rfl] at h4
  rw [show chainExample.record 6 = .bin 5 false 4 false from rfl] at h6
  rw [show chainExample.record 7 = .bin 5 false 6 false from rfl] at h7
  simp only [CoreRecord.eval] at h1 h3 h4 h6 h7
  rw [h7, h6, h5, h4, h3, h2, h1]
  cases X 2 <;> cases X 5 <;> rfl

/-- **Remark 4.7.** The claim of the source notes, that relative to the cover variables every
residual value is a constant or a signed copy `X_i ⊕ σ` of a single variable, is false: on the
two-stage chain, `y₂ = y₀ ∧ ¬c₁ ∧ ¬c₂` is neither. -/
theorem source_compression_claim_false :
    chainExample.IsCover chainCover ∧
    (∀ X, chainExample.residual chainCover X 7 = (!X 2 && !X 5)) ∧
    ¬ (∃ b, ∀ X, chainExample.residual chainCover X 7 = b) ∧
    ¬ (∃ i σ, ∀ X, chainExample.residual chainCover X 7 = xor (X i) σ) := by
  refine ⟨chainCover_isCover, chainExample_y7, ?_, ?_⟩
  · rintro ⟨b, hb⟩
    have h0 := hb (fun _ => false)
    have h1 := hb (fun _ => true)
    rw [chainExample_y7] at h0 h1
    simp at h0 h1
    rw [h0] at h1
    exact absurd h1 (by decide)
  · rintro ⟨i, σ, h⟩
    have h0 := h (fun _ => false)
    have hA := h (fun k => decide (k = 2))
    have hB := h (fun k => decide (k = 5))
    rw [chainExample_y7] at h0 hA hB
    simp at h0 hA hB
    -- `σ = true` from the all-zero assignment, then `i = 2` and `i = 5`
    subst h0
    have : i = 2 := by
      by_contra hne; simp [hne] at hA
    have : i = 5 := by
      by_contra hne; simp [hne] at hB
    omega

end GC.StructuralCompilers
