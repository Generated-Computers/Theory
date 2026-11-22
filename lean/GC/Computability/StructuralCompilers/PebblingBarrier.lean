import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Prod
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Lattice.Nat

/-!
# A pebbling barrier for clone-and-decompose algorithms (manuscript 007c, Section 4)

* `pebbling_projection` (Lemma 4.4): a black pebbling of a predecessor-preserving partial
  unfolding `U` of a gate DAG `C` projects to a black pebbling of `C` of no larger cost, so
  `Peb(C) ≤ Peb(U)`.
* `unfolding_computes` : every vertex `u` of `U` computes the value of `π(u)` (Section 4.1).
* `grid_pebbling_lower` (Lemma 4.8, lower bound): every black pebbling of the `g × g` grid `Q_g`
  (`g ≥ 2`) with target `x_{g-1,g-1}` has cost at least `g + 1`.
* `grid_unfolding_pebbling_lower` : hence every black pebbling of every predecessor-preserving
  partial unfolding of `C_g` has cost at least `g + 1`.

A black pebbling is a sequence of configurations starting from the empty one; each step places a
pebble on a vertex all of whose predecessors carry pebbles, removes a pebble, or (for
convenience) leaves the configuration unchanged; repeated configurations do not change the cost.
-/

namespace GC.StructuralCompilers

/-! ### Black pebbling -/

section Pebbling

variable {V : Type*} [DecidableEq V]

/-- One legal step of a black pebbling: keep the configuration, place a pebble on a vertex all of
whose predecessors are pebbled, or remove a pebble. -/
def LegalStep (pred : V → Finset V) (S S' : Finset V) : Prop :=
  S' = S ∨ (∃ v, pred v ⊆ S ∧ S' = insert v S) ∨ (∃ v, S' = S.erase v)

/-- A black pebbling of the DAG given by `pred` with target `t`. -/
structure Pebbling (pred : V → Finset V) (t : V) where
  /-- number of steps -/
  len : ℕ
  /-- the configurations `conf 0, …, conf len` -/
  conf : ℕ → Finset V
  /-- the pebbling starts from the empty configuration -/
  start : conf 0 = ∅
  /-- every step is legal -/
  step : ∀ k, k < len → LegalStep pred (conf k) (conf (k + 1))
  /-- the target is pebbled at some step -/
  hits : ∃ k, k ≤ len ∧ t ∈ conf k

/-- The cost of a pebbling: the maximum number of pebbles at any time. -/
def Pebbling.cost {pred : V → Finset V} {t : V} (P : Pebbling pred t) : ℕ :=
  (Finset.range (P.len + 1)).sup (fun k => (P.conf k).card)

lemma Pebbling.card_le_cost {pred : V → Finset V} {t : V} (P : Pebbling pred t) {k : ℕ}
    (hk : k ≤ P.len) : (P.conf k).card ≤ P.cost :=
  Finset.le_sup (f := fun k => (P.conf k).card) (Finset.mem_range.2 (by omega))

/-- Transfer of pebblings along a map `f : W → V` such that, for every `u`, either the
predecessors of `f u` are images of predecessors of `u`, or some predecessor of `u` has the same
image as `u`. -/
theorem pebbling_transfer {W : Type*} [DecidableEq W] (predW : W → Finset W)
    (predV : V → Finset V) (f : W → V)
    (hf : ∀ u, predV (f u) ⊆ (predW u).image f ∨ ∃ u' ∈ predW u, f u' = f u)
    {t : W} {t' : V} (ht : f t = t') (P : Pebbling predW t) :
    ∃ Q : Pebbling predV t', Q.cost ≤ P.cost := by
  refine ⟨⟨P.len, fun k => (P.conf k).image f, by simp [P.start], ?_, ?_⟩, ?_⟩
  · intro k hk
    rcases P.step k hk with h | ⟨w, hw, h⟩ | ⟨w, h⟩
    · left; rw [h]
    · rw [h, Finset.image_insert]
      rcases hf w with hsub | ⟨u', hu', hfu⟩
      · right; left
        exact ⟨f w, hsub.trans (Finset.image_subset_image hw), rfl⟩
      · left
        apply Finset.insert_eq_of_mem
        rw [← hfu]
        exact Finset.mem_image_of_mem f (hw hu')
    · rw [h]
      by_cases hmem : f w ∈ ((P.conf k).erase w).image f
      · left
        ext y
        simp only [Finset.mem_image, Finset.mem_erase]
        constructor
        · rintro ⟨x, ⟨-, hx⟩, rfl⟩; exact ⟨x, hx, rfl⟩
        · rintro ⟨x, hx, rfl⟩
          by_cases hxw : x = w
          · subst hxw
            simpa [Finset.mem_image, Finset.mem_erase] using hmem
          · exact ⟨x, ⟨hxw, hx⟩, rfl⟩
      · right; right
        refine ⟨f w, ?_⟩
        ext y
        simp only [Finset.mem_image, Finset.mem_erase]
        constructor
        · rintro ⟨x, ⟨hxw, hx⟩, rfl⟩
          refine ⟨fun h => hmem ?_, x, hx, rfl⟩
          rw [← h]
          exact Finset.mem_image_of_mem f (Finset.mem_erase.2 ⟨hxw, hx⟩)
        · rintro ⟨hy, x, hx, rfl⟩
          exact ⟨x, ⟨fun h => hy (h ▸ rfl), hx⟩, rfl⟩
  · obtain ⟨k, hk, htk⟩ := P.hits
    exact ⟨k, hk, ht ▸ Finset.mem_image_of_mem f (by assumption)⟩
  · apply Finset.sup_le
    intro k hk
    exact (Finset.card_image_le).trans (P.card_le_cost (by simpa [Nat.lt_succ_iff] using hk))

end Pebbling

/-! ### Gate DAGs and predecessor-preserving partial unfoldings (Definition 4.1) -/

/-- A gate DAG: every vertex has a gate type and an ordered list of predecessors. -/
structure GateDAG (V τ : Type*) where
  /-- ordered predecessors -/
  preds : V → List V
  /-- gate type -/
  kind : V → τ

/-- The predecessor sets used for pebbling. -/
def GateDAG.predSet {V τ : Type*} [DecidableEq V] (C : GateDAG V τ) (v : V) : Finset V :=
  (C.preds v).toFinset

/-- `(U, z_U, π)` is a predecessor-preserving partial unfolding of `(C, z)`: `π(z_U) = z`, every
vertex that is not a copy carrier is a clone (same gate type, and the labels of its ordered
predecessors are exactly the ordered predecessors of its label), and every copy carrier has a
unique predecessor with the same label. -/
def IsPPUnfolding {V W τ : Type*} (C : GateDAG V τ) (z : V) (U : GateDAG W τ) (zU : W)
    (π : W → V) (carrier : W → Bool) : Prop :=
  π zU = z ∧
  (∀ u, carrier u = false → U.kind u = C.kind (π u) ∧ (U.preds u).map π = C.preds (π u)) ∧
  (∀ u, carrier u = true → ∃ u', U.preds u = [u'] ∧ π u' = π u)

/-- Every vertex `u` of a predecessor-preserving partial unfolding computes the value of `π(u)`:
the values `valC ∘ π` satisfy the gate equations of `U` (clones evaluate their gate, copy
carriers copy their predecessor). -/
theorem unfolding_computes {V W τ : Type*} (C : GateDAG V τ) (z : V) (U : GateDAG W τ) (zU : W)
    (π : W → V) (carrier : W → Bool) (hU : IsPPUnfolding C z U zU π carrier)
    (ev : τ → List Bool → Bool) (valC : V → Bool)
    (hC : ∀ v, valC v = ev (C.kind v) ((C.preds v).map valC)) :
    (∀ u, carrier u = false →
      valC (π u) = ev (U.kind u) ((U.preds u).map (valC ∘ π))) ∧
    (∀ u, carrier u = true → ∃ u', U.preds u = [u'] ∧ valC (π u) = valC (π u')) ∧
    valC (π zU) = valC z := by
  refine ⟨?_, ?_, by rw [hU.1]⟩
  · intro u hu
    obtain ⟨hk, hp⟩ := hU.2.1 u hu
    rw [hC (π u), hk, ← hp, List.map_map]
  · intro u hu
    obtain ⟨u', hp, hπ⟩ := hU.2.2 u hu
    exact ⟨u', hp, by rw [hπ]⟩

/-- **Lemma 4.4 (pebbling projection).** If `U` is a predecessor-preserving partial unfolding of
`C`, every black pebbling of `U` projects to a black pebbling of `C` of no larger cost; hence
`Peb(C) ≤ Peb(U)`. -/
theorem pebbling_projection {V W τ : Type*} [DecidableEq V] [DecidableEq W] (C : GateDAG V τ)
    (z : V) (U : GateDAG W τ) (zU : W) (π : W → V) (carrier : W → Bool)
    (hU : IsPPUnfolding C z U zU π carrier) (P : Pebbling U.predSet zU) :
    ∃ Q : Pebbling C.predSet z, Q.cost ≤ P.cost := by
  have hf : ∀ u, C.predSet (π u) ⊆ (U.predSet u).image π ∨
      ∃ u' ∈ U.predSet u, π u' = π u := by
    intro u
    cases hc : carrier u
    · left
      obtain ⟨-, hp⟩ := hU.2.1 u hc
      intro v hv
      simp only [GateDAG.predSet, List.mem_toFinset, ← hp, List.mem_map] at hv
      obtain ⟨u', hu', rfl⟩ := hv
      exact Finset.mem_image_of_mem π (by simpa [GateDAG.predSet] using hu')
    · right
      obtain ⟨u', hp, hπ⟩ := hU.2.2 u hc
      exact ⟨u', by simp [GateDAG.predSet, hp], hπ⟩
  exact pebbling_transfer U.predSet C.predSet π hf hU.1 P

/-! ### The grid (Section 4.3) -/

/-- Predecessors in the quadrant grid on `ℕ × ℕ`: the north and west neighbours. -/
def quadPred (x : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  (if 1 ≤ x.1 then {(x.1 - 1, x.2)} else ∅) ∪ (if 1 ≤ x.2 then {(x.1, x.2 - 1)} else ∅)

/-- The grid gate DAG `C_g` on `x_{i,j}`, `0 ≤ i, j < g`: `x_{i,j}` reads its north neighbour
`x_{i-1,j}` and its west neighbour `x_{i,j-1}`; top-row and left-column gates read their unique
predecessor twice, and `x_{0,0}` is a source. The gate types are arbitrary. -/
def gridDAG {τ : Type*} (g : ℕ) (kind : Fin g × Fin g → τ) : GateDAG (Fin g × Fin g) τ where
  preds := fun x =>
    if h1 : 1 ≤ x.1.val then
      if h2 : 1 ≤ x.2.val then
        [(⟨x.1.val - 1, by omega⟩, x.2), (x.1, ⟨x.2.val - 1, by omega⟩)]
      else [(⟨x.1.val - 1, by omega⟩, x.2), (⟨x.1.val - 1, by omega⟩, x.2)]
    else
      if h2 : 1 ≤ x.2.val then [(x.1, ⟨x.2.val - 1, by omega⟩), (x.1, ⟨x.2.val - 1, by omega⟩)]
      else []
  kind := kind

/-- The output gate `x_{g-1,g-1}` of `C_g`. -/
def gridOut (g : ℕ) (hg : 1 ≤ g) : Fin g × Fin g := (⟨g - 1, by omega⟩, ⟨g - 1, by omega⟩)

section GridLower

variable (g : ℕ)

/-- A monotone staircase path of the pyramid `T = {i + j ≥ g - 1}` from its base to the apex,
given by its row coordinates `A ℓ` at the levels `ℓ = 0, …, g-1`; the vertex at level `ℓ` is
`(A ℓ, g - 1 + ℓ - A ℓ)`. -/
def IsStair (A : ℕ → ℕ) : Prop :=
  (∀ ℓ, ℓ < g - 1 → A (ℓ + 1) = A ℓ ∨ A (ℓ + 1) = A ℓ + 1) ∧ A (g - 1) = g - 1

/-- The vertex of a staircase at level `ℓ`. -/
def stairVtx (A : ℕ → ℕ) (ℓ : ℕ) : ℕ × ℕ := (A ℓ, g - 1 + ℓ - A ℓ)

/-- A configuration is blocking if every base-to-apex staircase carries a pebble. -/
def Blocking (S : Finset (ℕ × ℕ)) : Prop :=
  ∀ A, IsStair g A → ∃ ℓ, ℓ ≤ g - 1 ∧ stairVtx g A ℓ ∈ S

variable {g}

lemma IsStair.bounds {A : ℕ → ℕ} (hA : IsStair g A) : ∀ ℓ, ℓ ≤ g - 1 → ℓ ≤ A ℓ ∧ A ℓ ≤ g - 1 := by
  have key : ∀ d, d ≤ g - 1 → g - 1 ≤ A (g - 1 - d) + d ∧ A (g - 1 - d) ≤ g - 1 := by
    intro d
    induction d with
    | zero => intro _; simp [hA.2]
    | succ d ih =>
      intro hd
      have := ih (by omega)
      have hstep := hA.1 (g - 1 - (d + 1)) (by omega)
      rw [show g - 1 - (d + 1) + 1 = g - 1 - d by omega] at hstep
      omega
  intro ℓ hℓ
  have := key (g - 1 - ℓ) (by omega)
  rw [show g - 1 - (g - 1 - ℓ) = ℓ by omega] at this
  omega

lemma stairVtx_sum {A : ℕ → ℕ} (hA : IsStair g A) {ℓ : ℕ} (hℓ : ℓ ≤ g - 1) :
    (stairVtx g A ℓ).1 + (stairVtx g A ℓ).2 = g - 1 + ℓ := by
  have := hA.bounds ℓ hℓ
  simp only [stairVtx]
  omega

lemma stairVtx_pred {A : ℕ → ℕ} (hA : IsStair g A) {ℓ : ℕ} (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ g - 1) :
    stairVtx g A (ℓ - 1) ∈ quadPred (stairVtx g A ℓ) := by
  have hb := hA.bounds ℓ hℓ
  have hb' := hA.bounds (ℓ - 1) (by omega)
  have hstep := hA.1 (ℓ - 1) (by omega)
  rw [show ℓ - 1 + 1 = ℓ by omega] at hstep
  rcases hstep with h | h
  · have h' : 1 ≤ g - 1 + ℓ - A ℓ := by omega
    simp only [quadPred, stairVtx, Finset.mem_union]
    right
    simp only [h', if_true, Finset.mem_singleton, Prod.mk.injEq]
    omega
  · have h' : 1 ≤ A ℓ := by omega
    simp only [quadPred, stairVtx, Finset.mem_union]
    left
    simp only [h', if_true, Finset.mem_singleton, Prod.mk.injEq]
    omega

/-- The staircases from the other base vertices: from `(a, g - 1 - a)` go down the column until
the path `A` is met (if `a < A 0`), or along the row until it is met (if `a > A 0`). -/
def detour (A : ℕ → ℕ) (a : ℕ) : ℕ → ℕ :=
  fun ℓ => if a < A 0 then min (a + ℓ) (A ℓ) else max a (A ℓ)

lemma detour_isStair {A : ℕ → ℕ} (hA : IsStair g A) {a : ℕ} (ha : a ≤ g - 1) :
    IsStair g (detour A a) := by
  refine ⟨?_, ?_⟩
  · intro ℓ hℓ
    have := hA.1 ℓ hℓ
    simp only [detour]
    split_ifs <;> omega
  · have := hA.2
    simp only [detour]
    split_ifs <;> omega

lemma detour_zero (A : ℕ → ℕ) (a : ℕ) : detour A a 0 = a := by
  simp only [detour]
  split_ifs <;> omega

/-- **Lemma 4.8 (grid pebbling price, lower bound), on the quadrant grid.** For `g ≥ 2`, every
black pebbling of the grid DAG with target `(g-1, g-1)` has at some time at least `g + 1`
pebbles. -/
theorem quad_pebbling_lower (hg : 2 ≤ g) (P : Pebbling quadPred (g - 1, g - 1)) :
    ∃ k, k ≤ P.len ∧ g + 1 ≤ (P.conf k).card := by
  classical
  -- the empty configuration is not blocking, a configuration with the apex is
  have hstair0 : IsStair g (fun _ => g - 1) := ⟨fun _ _ => Or.inl rfl, rfl⟩
  have hnb0 : ¬ Blocking g ∅ := by
    intro h
    obtain ⟨ℓ, -, hℓ⟩ := h _ hstair0
    simp at hℓ
  have hex : ∃ k, k ≤ P.len ∧ Blocking g (P.conf k) := by
    obtain ⟨k, hk, ht⟩ := P.hits
    refine ⟨k, hk, fun A hA => ⟨g - 1, le_rfl, ?_⟩⟩
    have : stairVtx g A (g - 1) = (g - 1, g - 1) := by
      simp only [stairVtx, hA.2]
      ext <;> simp
    rw [this]
    exact ht
  -- the first blocking time
  obtain ⟨k1, hk1, hmin⟩ : ∃ k1, (k1 ≤ P.len ∧ Blocking g (P.conf k1)) ∧
      ∀ j < k1, ¬ (j ≤ P.len ∧ Blocking g (P.conf j)) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  have hk1pos : k1 ≠ 0 := by
    intro h0
    have := hk1.2
    rw [h0, P.start] at this
    exact hnb0 this
  obtain ⟨k, rfl⟩ : ∃ k, k1 = k + 1 := ⟨k1 - 1, by omega⟩
  have hnb : ¬ Blocking g (P.conf k) := by
    intro hb
    exact hmin k (by omega) ⟨by omega, hb⟩
  set S := P.conf k with hS
  have hblock := hk1.2
  -- the step into the blocking configuration places a pebble
  obtain ⟨v, hpv, hS'⟩ : ∃ v, quadPred v ⊆ S ∧ P.conf (k + 1) = insert v S := by
    rcases P.step k (by omega) with h | h | ⟨w, h⟩
    · rw [h] at hblock; exact absurd hblock hnb
    · exact h
    · exfalso
      apply hnb
      intro A hA
      obtain ⟨ℓ, hℓ, hmem⟩ := hblock A hA
      rw [h] at hmem
      exact ⟨ℓ, hℓ, Finset.mem_of_mem_erase hmem⟩
  rw [hS'] at hblock
  -- a pebble-free staircase `A` before the step
  obtain ⟨A, hA, hfree⟩ : ∃ A, IsStair g A ∧ ∀ ℓ, ℓ ≤ g - 1 → stairVtx g A ℓ ∉ S := by
    by_contra hcon
    push Not at hcon
    exact hnb hcon
  -- the placed vertex is the base vertex of `A`
  have hv : v = stairVtx g A 0 := by
    obtain ⟨ℓ, hℓ, hmem⟩ := hblock A hA
    rcases Finset.mem_insert.1 hmem with h | h
    · rcases Nat.eq_zero_or_pos ℓ with rfl | hpos
      · exact h.symm
      · exfalso
        apply hfree (ℓ - 1) (by omega)
        apply hpv
        rw [← h]
        exact stairVtx_pred hA hpos hℓ
    · exact absurd h (hfree ℓ hℓ)
  have hvS : v ∉ S := by rw [hv]; exact hfree 0 (by omega)
  -- a predecessor of `v` below the base carries a pebble
  have hbase := stairVtx_sum hA (ℓ := 0) (by omega)
  obtain ⟨p, hp, hpsum⟩ : ∃ p ∈ S, p.1 + p.2 + 1 = g - 1 := by
    rw [← hv] at hbase
    by_cases h1 : 1 ≤ v.1
    · refine ⟨(v.1 - 1, v.2), hpv ?_, by simp; omega⟩
      simp [quadPred, h1]
    · have h2 : 1 ≤ v.2 := by omega
      refine ⟨(v.1, v.2 - 1), hpv ?_, by simp; omega⟩
      simp [quadPred, h2]
  -- the detours from the other base vertices meet `S` off the path `A`
  have hhit : ∀ a, a ≤ g - 1 → a ≠ A 0 → ∃ ℓ, ℓ ≤ g - 1 ∧
      stairVtx g (detour A a) ℓ ∈ S ∧ detour A a ℓ ≠ A ℓ := by
    intro a ha hne
    have hD := detour_isStair hA ha
    obtain ⟨ℓ, hℓ, hmem⟩ := hblock _ hD
    rcases Finset.mem_insert.1 hmem with h | h
    · exfalso
      rcases Nat.eq_zero_or_pos ℓ with rfl | hpos
      · have := congrArg Prod.fst h
        rw [hv] at this
        simp only [stairVtx, detour_zero A a] at this
        exact hne this
      · have h1 := stairVtx_sum hD hℓ
        rw [h, hv] at h1
        have h2 := stairVtx_sum hA (ℓ := 0) (by omega)
        omega
    · refine ⟨ℓ, hℓ, h, fun heq => hfree ℓ hℓ ?_⟩
      have : stairVtx g (detour A a) ℓ = stairVtx g A ℓ := by
        simp only [stairVtx, heq]
      rwa [← this]
  choose! lev hlev using hhit
  let H := (Finset.range g).erase (A 0)
  let φ : ℕ → ℕ × ℕ := fun a => stairVtx g (detour A a) (lev a)
  have hHφ : ∀ a ∈ H, a ≤ g - 1 ∧ a ≠ A 0 := by
    intro a ha
    simp only [H, Finset.mem_erase, Finset.mem_range] at ha
    exact ⟨by omega, ha.1⟩
  have hinj : Set.InjOn φ H := by
    intro a ha b hb hab
    obtain ⟨ha1, ha2⟩ := hHφ a ha
    obtain ⟨hb1, hb2⟩ := hHφ b hb
    obtain ⟨hla, -, hna⟩ := hlev a ha1 ha2
    obtain ⟨hlb, -, hnb'⟩ := hlev b hb1 hb2
    have hsa := stairVtx_sum (detour_isStair hA ha1) hla
    have hsb := stairVtx_sum (detour_isStair hA hb1) hlb
    simp only [φ] at hab
    rw [hab] at hsa
    have hlevel : lev a = lev b := by omega
    have h1 := congrArg Prod.fst hab
    simp only [stairVtx] at h1
    rw [hlevel] at h1 hna
    simp only [detour] at h1 hna hnb'
    split_ifs at h1 hna hnb' <;> omega
  have himage : H.image φ ⊆ S.erase p := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨ha1, ha2⟩ := hHφ a ha
    obtain ⟨hla, hmem, -⟩ := hlev a ha1 ha2
    refine Finset.mem_erase.2 ⟨fun heq => ?_, hmem⟩
    have := stairVtx_sum (detour_isStair hA ha1) hla
    simp only [φ] at heq
    rw [heq] at this
    omega
  have hcardH : H.card = g - 1 := by
    have : A 0 ∈ Finset.range g := by
      have := (hA.bounds 0 (by omega)).2
      simp only [Finset.mem_range]; omega
    simp only [H, Finset.card_erase_of_mem this, Finset.card_range]
  have hcardS : g ≤ S.card := by
    have h1 := Finset.card_le_card himage
    rw [Finset.card_image_of_injOn hinj, hcardH, Finset.card_erase_of_mem hp] at h1
    omega
  refine ⟨k + 1, hk1.1, ?_⟩
  rw [hS', Finset.card_insert_of_notMem hvS]
  omega

end GridLower

/-- The embedding of `Q_g` into the quadrant grid preserves predecessors. -/
lemma gridDAG_predSet_image {τ : Type*} (g : ℕ) (kind : Fin g × Fin g → τ) (x : Fin g × Fin g) :
    quadPred ((x.1 : ℕ), (x.2 : ℕ)) =
      ((gridDAG g kind).predSet x).image (fun y => ((y.1 : ℕ), (y.2 : ℕ))) := by
  ext y
  simp only [quadPred, GateDAG.predSet, gridDAG, Finset.mem_union, Finset.mem_image,
    List.mem_toFinset]
  by_cases h1 : 1 ≤ x.1.val <;> by_cases h2 : 1 ≤ x.2.val <;>
    simp [h1, h2] <;> constructor <;> intro h <;> aesop

/-- **Lemma 4.8 (lower bound).** For `g ≥ 2`, every black pebbling of the grid `Q_g` with target
`x_{g-1,g-1}` has cost at least `g + 1`. -/
theorem grid_pebbling_lower {τ : Type*} (g : ℕ) (hg : 2 ≤ g) (kind : Fin g × Fin g → τ)
    (P : Pebbling (gridDAG g kind).predSet (gridOut g (by omega))) : g + 1 ≤ P.cost := by
  obtain ⟨Q, hQ⟩ := pebbling_transfer (gridDAG g kind).predSet quadPred
    (fun y => ((y.1 : ℕ), (y.2 : ℕ)))
    (fun u => Or.inl (by rw [gridDAG_predSet_image g kind u])) (t' := (g - 1, g - 1)) rfl P
  obtain ⟨k, hk, hcard⟩ := quad_pebbling_lower hg Q
  exact le_trans hcard ((Q.card_le_cost hk).trans hQ)

/-- **Lemmas 4.4 and 4.8 combined.** For `g ≥ 2`, every black pebbling of every
predecessor-preserving partial unfolding of the grid circuit `C_g` has cost at least `g + 1`. -/
theorem grid_unfolding_pebbling_lower {τ W : Type*} [DecidableEq W] (g : ℕ) (hg : 2 ≤ g)
    (kind : Fin g × Fin g → τ) (U : GateDAG W τ) (zU : W) (π : W → Fin g × Fin g)
    (carrier : W → Bool)
    (hU : IsPPUnfolding (gridDAG g kind) (gridOut g (by omega)) U zU π carrier)
    (P : Pebbling U.predSet zU) : g + 1 ≤ P.cost := by
  obtain ⟨Q, hQ⟩ := pebbling_projection _ _ U zU π carrier hU P
  exact (grid_pebbling_lower g hg kind Q).trans hQ

/-! ### The upper bound of Lemma 4.8: pebbling the grid row by row -/

lemma mem_gridPred {τ : Type*} {g : ℕ} {kind : Fin g × Fin g → τ} {x y : Fin g × Fin g}
    (hy : y ∈ (gridDAG g kind).predSet x) :
    (1 ≤ x.1.val ∧ y.1.val + 1 = x.1.val ∧ y.2.val = x.2.val) ∨
      (1 ≤ x.2.val ∧ y.1.val = x.1.val ∧ y.2.val + 1 = x.2.val) := by
  have := Finset.mem_image_of_mem (fun y : Fin g × Fin g => ((y.1 : ℕ), (y.2 : ℕ))) hy
  rw [← gridDAG_predSet_image g kind x] at this
  simp only [quadPred, Finset.mem_union] at this
  rcases this with h | h
  · by_cases h1 : 1 ≤ x.1.val
    · rw [if_pos h1, Finset.mem_singleton, Prod.mk.injEq] at h
      left; omega
    · rw [if_neg h1] at h; simp at h
  · by_cases h2 : 1 ≤ x.2.val
    · rw [if_pos h2, Finset.mem_singleton, Prod.mk.injEq] at h
      right; omega
    · rw [if_neg h2] at h; simp at h

/-- The configuration at time `t` of the row-by-row strategy: first row `0` is pebbled from left
to right; then, writing `t = g + 2m + ph` and `m = r g + c`, the pebbles are on
`x_{r+1,j}` (`j < c`), on `x_{r,j}` (`j ≥ c`), and on `x_{r+1,c}` if `ph = 1`. -/
def rowMem (g t i j : ℕ) : Prop :=
  if t < g then i = 0 ∧ j < t
  else (i = (t - g) / 2 / g + 1 ∧ j < (t - g) / 2 % g) ∨
    (i = (t - g) / 2 / g ∧ (t - g) / 2 % g ≤ j) ∨
    ((t - g) % 2 = 1 ∧ i = (t - g) / 2 / g + 1 ∧ j = (t - g) / 2 % g)

instance (g t i j : ℕ) : Decidable (rowMem g t i j) := by unfold rowMem; infer_instance

/-- The configurations of the row-by-row strategy. -/
def rowConf (g t : ℕ) : Finset (Fin g × Fin g) :=
  Finset.univ.filter (fun x => rowMem g t x.1.val x.2.val)

lemma mem_rowConf (g t : ℕ) (x : Fin g × Fin g) :
    x ∈ rowConf g t ↔ rowMem g t x.1.val x.2.val := by
  simp [rowConf]

lemma rowMem_early (g t i j : ℕ) (ht : t < g) : rowMem g t i j ↔ i = 0 ∧ j < t := by
  unfold rowMem
  rw [if_pos ht]

lemma rowMem_late (g m ph i j : ℕ) (hph : ph < 2) :
    rowMem g (g + 2 * m + ph) i j ↔ (i = m / g + 1 ∧ j < m % g) ∨ (i = m / g ∧ m % g ≤ j) ∨
      (ph = 1 ∧ i = m / g + 1 ∧ j = m % g) := by
  unfold rowMem
  rw [if_neg (by omega), show g + 2 * m + ph - g = 2 * m + ph by omega,
    show (2 * m + ph) / 2 = m by omega, show (2 * m + ph) % 2 = ph by omega]

lemma rowConf_card_le (g t : ℕ) : (rowConf g t).card ≤ g + 1 := by
  classical
  -- the special vertex and the column-injective rest
  let sp : ℕ × ℕ := if t < g then (g, g) else ((t - g) / 2 / g + 1, (t - g) / 2 % g)
  let isSp : Fin g × Fin g → Prop := fun x => x.1.val = sp.1 ∧ x.2.val = sp.2
  have h1 : ((rowConf g t).filter isSp).card ≤ 1 := by
    apply Finset.card_le_one.2
    intro a ha b hb
    simp only [Finset.mem_filter, isSp] at ha hb
    ext
    · omega
    · omega
  have h2 : ((rowConf g t).filter (fun x => ¬ isSp x)).card ≤ g := by
    have hinj : Set.InjOn (fun x : Fin g × Fin g => x.2)
        ((rowConf g t).filter (fun x => ¬ isSp x)) := by
      intro a ha b hb hab
      simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_rowConf, isSp, sp] at ha hb
      simp only at hab
      have hab' : a.2.val = b.2.val := by rw [hab]
      ext
      · by_cases ht : t < g
        · rw [rowMem_early g t _ _ ht] at ha hb
          omega
        · unfold rowMem at ha hb
          rw [if_neg ht] at ha hb
          simp only [ht, if_false] at ha hb
          omega
      · exact hab'
    calc _ ≤ (Finset.univ : Finset (Fin g)).card :=
          Finset.card_le_card_of_injOn _ (fun _ _ => Finset.mem_univ _) hinj
      _ = g := by simp
  have := Finset.card_filter_add_card_filter_not (s := rowConf g t) isSp
  omega

/-- **Lemma 4.8 (upper bound).** For `g ≥ 2`, the grid `Q_g` has a black pebbling of cost at
most `g + 1`. -/
theorem grid_pebbling_upper {τ : Type*} (g : ℕ) (hg : 2 ≤ g) (kind : Fin g × Fin g → τ) :
    ∃ P : Pebbling (gridDAG g kind).predSet (gridOut g (by omega)), P.cost ≤ g + 1 := by
  classical
  have hgpos : 0 < g := by omega
  refine ⟨⟨g + 2 * ((g - 1) * g), rowConf g, ?_, ?_, ?_⟩, ?_⟩
  · ext x
    rw [mem_rowConf, rowMem_early g 0 _ _ (by omega)]
    simp
  · intro t ht
    by_cases htg : t < g
    · -- pebble row `0` from left to right
      right; left
      refine ⟨(⟨0, hgpos⟩, ⟨t, htg⟩), ?_, ?_⟩
      · intro y hy
        rcases mem_gridPred hy with ⟨h1, -, -⟩ | ⟨-, h1, h2⟩
        · simp at h1
        · rw [mem_rowConf, rowMem_early g t _ _ htg]
          simp only at h1 h2
          omega
      · ext x
        rw [Finset.mem_insert, mem_rowConf, mem_rowConf]
        by_cases ht1 : t + 1 < g
        · rw [rowMem_early g _ _ _ ht1, rowMem_early g _ _ _ htg, Prod.ext_iff, Fin.ext_iff,
            Fin.ext_iff]
          simp only
          omega
        · have hteq : t + 1 = g + 2 * 0 + 0 := by omega
          rw [hteq, rowMem_late g 0 0 _ _ (by omega), rowMem_early g _ _ _ htg, Prod.ext_iff,
            Fin.ext_iff, Fin.ext_iff]
          simp only [Nat.zero_div, Nat.zero_mod]
          have := x.2.isLt
          omega
    · obtain ⟨m, ph, hph, rfl⟩ : ∃ m ph, ph < 2 ∧ t = g + 2 * m + ph :=
        ⟨(t - g) / 2, (t - g) % 2, by omega, by omega⟩
      have hm : m < (g - 1) * g := by omega
      have hr : m / g + 1 < g := by
        have := (Nat.div_lt_iff_lt_mul hgpos).2 hm
        omega
      have hc : m % g < g := Nat.mod_lt _ hgpos
      rcases (show ph = 0 ∨ ph = 1 by omega) with rfl | rfl
      · -- place `x_{r+1,c}`
        right; left
        refine ⟨(⟨m / g + 1, hr⟩, ⟨m % g, hc⟩), ?_, ?_⟩
        · intro y hy
          rw [mem_rowConf, rowMem_late g m 0 _ _ (by omega)]
          rcases mem_gridPred hy with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;> simp only at h1 h2 <;>
            generalize m / g = r at * <;> generalize m % g = c at * <;> omega
        · ext x
          rw [Finset.mem_insert, mem_rowConf, mem_rowConf]
          rw [show g + 2 * m + 0 + 1 = g + 2 * m + 1 by omega, rowMem_late g m 1 _ _ (by omega),
            rowMem_late g m 0 _ _ (by omega), Prod.ext_iff, Fin.ext_iff, Fin.ext_iff]
          simp only
          generalize m / g = r at *
          generalize m % g = c at *
          simp only [true_and, false_and, or_false, zero_ne_one]
          constructor <;> intro h <;> omega
      · -- remove `x_{r,c}`
        right; right
        refine ⟨(⟨m / g, by omega⟩, ⟨m % g, hc⟩), ?_⟩
        ext x
        rw [Finset.mem_erase, mem_rowConf, mem_rowConf]
        rw [show g + 2 * m + 1 + 1 = g + 2 * (m + 1) + 0 by omega,
          rowMem_late g (m + 1) 0 _ _ (by omega), rowMem_late g m 1 _ _ (by omega), ne_eq,
          Prod.ext_iff, Fin.ext_iff, Fin.ext_iff]
        simp only
        have hdm := Nat.div_add_mod m g
        have hx2 := x.2.isLt
        by_cases hc1 : m % g + 1 < g
        · have h' : (m + 1) / g = m / g ∧ (m + 1) % g = m % g + 1 :=
            (Nat.div_mod_unique hgpos).2 ⟨by
              generalize m / g = r at *; generalize m % g = c at *; omega, hc1⟩
          rw [h'.1, h'.2]
          clear h'
          generalize m / g = r at *
          generalize m % g = c at *
          simp only [true_and, false_and, or_false, zero_ne_one]
          constructor <;> intro h <;> omega
        · have h' : (m + 1) / g = m / g + 1 ∧ (m + 1) % g = 0 :=
            (Nat.div_mod_unique hgpos).2 ⟨by
              rw [Nat.mul_add]
              generalize m / g = r at *; generalize m % g = c at *; omega, hgpos⟩
          rw [h'.1, h'.2]
          clear h'
          generalize m / g = r at *
          generalize m % g = c at *
          simp only [true_and, false_and, or_false, zero_ne_one]
          constructor <;> intro h <;> omega
  · -- the target is pebbled at the end
    refine ⟨g + 2 * ((g - 1) * g), le_rfl, ?_⟩
    rw [mem_rowConf]
    simp only [gridOut]
    rw [show g + 2 * ((g - 1) * g) = g + 2 * ((g - 1) * g) + 0 by rfl,
      rowMem_late g _ 0 _ _ (by omega), Nat.mul_div_cancel _ hgpos, Nat.mul_mod_left]
    right; left
    exact ⟨rfl, Nat.zero_le _⟩
  · apply Finset.sup_le
    intro t _
    exact rowConf_card_le g t

/-- The black pebbling price `Peb(D)`: the least cost of a black pebbling. -/
noncomputable def pebblingPrice {V : Type*} [DecidableEq V] (pred : V → Finset V) (t : V) : ℕ :=
  sInf {c | ∃ P : Pebbling pred t, P.cost = c}

/-- **Lemma 4.8 (grid pebbling price).** For `g ≥ 2`, `Peb(Q_g) = g + 1`. -/
theorem grid_pebblingPrice {τ : Type*} (g : ℕ) (hg : 2 ≤ g) (kind : Fin g × Fin g → τ) :
    pebblingPrice (gridDAG g kind).predSet (gridOut g (by omega)) = g + 1 := by
  obtain ⟨P, hP⟩ := grid_pebbling_upper g hg kind
  apply le_antisymm
  · exact (Nat.sInf_le (show P.cost ∈ {c | ∃ P : Pebbling (gridDAG g kind).predSet
      (gridOut g (by omega)), P.cost = c} from ⟨P, rfl⟩)).trans hP
  · apply le_csInf (show Set.Nonempty {c | ∃ P : Pebbling (gridDAG g kind).predSet
      (gridOut g (by omega)), P.cost = c} from ⟨P.cost, P, rfl⟩)
    rintro c ⟨Q, rfl⟩
    exact grid_pebbling_lower g hg kind Q

end GC.StructuralCompilers
