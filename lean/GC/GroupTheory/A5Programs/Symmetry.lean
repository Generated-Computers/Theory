import GC.GroupTheory.A5Programs.Collisions
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.GroupTheory.Perm.ClosureSwap
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Stable colors do not certify symmetry (manuscript 004h)

* `frucht_cubic`, `frucht_asymmetric`: the graph with LCF code
  `[-5,-2,-4,2,5,-2,2,5,-2,-5,4,2]` (the Frucht graph) is cubic on 12 vertices and has no
  nontrivial automorphism.
* `incidence_refinement_stable`, `incidence_rigid`: on its colored incidence graph, one round of
  color refinement does not split the two initial classes (12 vertex-nodes, 18 edge-nodes), but
  the only color-preserving automorphism is the identity (Theorem 3.1).
* `rotation_orbits_ge`: rotations of `D^q` are transitive on coordinates but have at least
  `|D|^q / q` orbits (Theorem 4.1, lower bound; the exact count is Burnside's lemma).
* `symmetric_shell`, `symmetric_shell_boolean`: the shell `F_g(x)_i = M(g, x_i)` with an `A₅`
  selector `M` is `S_q`-equivariant, its response is constant `e` if `g = e` and the identity
  otherwise, so its response decides the value of an arbitrary compiled Boolean circuit
  (Theorem 5.1).
* `swap_forest`: if a block is equivariant under the transpositions along the edges of a
  connected graph on the records, it is equivariant under all permutations of the records
  (Theorem 6.4, connected case).
-/

namespace GC.A5Programs

open Equiv

/-! ## The Frucht graph -/

/-- Chord offsets of the LCF code `[-5,-2,-4,2,5,-2,2,5,-2,-5,4,2]`, modulo 12. -/
def fruchtOff : Fin 12 → Fin 12 := ![7, 10, 8, 2, 5, 10, 2, 5, 10, 7, 4, 2]

/-- Neighbors: the two cycle neighbors and the chord. -/
def fruchtNbrs (v : Fin 12) : List (Fin 12) := [v + 1, v + 11, v + fruchtOff v]

/-- Adjacency of the Frucht graph. -/
def fruchtAdj (u v : Fin 12) : Prop := v ∈ fruchtNbrs u

instance : DecidableRel fruchtAdj := fun u v => inferInstanceAs (Decidable (v ∈ fruchtNbrs u))

theorem fruchtAdj_symm : ∀ u v, fruchtAdj u v → fruchtAdj v u := by decide
theorem fruchtAdj_irrefl : ∀ v, ¬ fruchtAdj v v := by decide
theorem fruchtNbrs_nodup : ∀ v, (fruchtNbrs v).Nodup := by decide

/-- The Frucht graph. -/
def fruchtGraph : SimpleGraph (Fin 12) where
  Adj := fruchtAdj
  symm := ⟨fun u v h => fruchtAdj_symm u v h⟩
  loopless := ⟨fun v h => fruchtAdj_irrefl v h⟩

instance : DecidableRel fruchtGraph.Adj := inferInstanceAs (DecidableRel fruchtAdj)

/-- The Frucht graph is cubic. -/
theorem frucht_cubic : ∀ v, fruchtGraph.degree v = 3 := by decide

section Rigid

variable (σ : Perm (Fin 12)) (hσ : ∀ u v, fruchtAdj (σ u) (σ v) ↔ fruchtAdj u v)

include hσ in
theorem nbrs_perm (v : Fin 12) : (fruchtNbrs (σ v)).Perm ((fruchtNbrs v).map σ) := by
  rw [List.perm_ext_iff_of_nodup (fruchtNbrs_nodup _) ((fruchtNbrs_nodup v).map σ.injective)]
  intro u
  rw [List.mem_map]
  constructor
  · intro hu
    refine ⟨σ⁻¹ u, ?_, by simp⟩
    have : fruchtAdj (σ v) (σ (σ⁻¹ u)) := by rw [show σ (σ⁻¹ u) = u by simp]; exact hu
    exact (hσ _ _).1 this
  · rintro ⟨a, ha, rfl⟩
    exact (hσ v a).2 ha

/-- Initial coloring: does the vertex lie on a triangle? -/
def triCol (v : Fin 12) : ℕ :=
  if ∃ a ∈ fruchtNbrs v, ∃ b ∈ fruchtNbrs v, fruchtAdj a b then 1 else 0

/-- One round of (numerical) refinement. -/
def refineCol (c : Fin 12 → ℕ) (v : Fin 12) : ℕ :=
  7 * c v + ((fruchtNbrs v).map fun u => c u * c u + 1).sum

include hσ in
theorem triCol_inv (v : Fin 12) : triCol (σ v) = triCol v := by
  unfold triCol
  have hp := nbrs_perm σ hσ v
  congr 1
  apply propext
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    obtain ⟨a', ha', rfl⟩ := List.mem_map.1 (hp.mem_iff.1 ha)
    obtain ⟨b', hb', rfl⟩ := List.mem_map.1 (hp.mem_iff.1 hb)
    exact ⟨a', ha', b', hb', (hσ a' b').1 hab⟩
  · rintro ⟨a, ha, b, hb, hab⟩
    exact ⟨σ a, hp.mem_iff.2 (List.mem_map_of_mem ha), σ b,
      hp.mem_iff.2 (List.mem_map_of_mem hb), (hσ a b).2 hab⟩

include hσ in
theorem refineCol_inv (c : Fin 12 → ℕ) (hc : ∀ v, c (σ v) = c v) (v : Fin 12) :
    refineCol c (σ v) = refineCol c v := by
  unfold refineCol
  rw [hc, ((nbrs_perm σ hσ v).map _).sum_eq, List.map_map]
  congr 2
  apply List.map_congr_left
  intro u _; simp [hc]

/-- Four rounds of refinement from the triangle coloring. -/
def col4 : Fin 12 → ℕ := refineCol (refineCol (refineCol (refineCol triCol)))

set_option maxRecDepth 100000 in
theorem col4_nodup : (List.ofFn col4).Nodup := by decide +kernel

include hσ in
/-- Every automorphism of the Frucht graph is the identity. -/
theorem frucht_rigid : σ = 1 := by
  have h1 := refineCol_inv σ hσ _ (triCol_inv σ hσ)
  have h2 := refineCol_inv σ hσ _ h1
  have h3 := refineCol_inv σ hσ _ h2
  have h4 := refineCol_inv σ hσ _ h3
  have hinj : Function.Injective col4 := List.nodup_ofFn.1 col4_nodup
  ext v
  exact congrArg Fin.val (hinj (h4 v))

end Rigid

/-- **The Frucht graph is asymmetric**: its only automorphism is the identity. -/
theorem frucht_asymmetric (φ : fruchtGraph ≃g fruchtGraph) : ∀ v, φ v = v := by
  have := frucht_rigid φ.toEquiv (fun u v => φ.map_adj_iff (v := u) (w := v))
  intro v
  have h := congrArg (fun f : Perm (Fin 12) => f v) this
  simpa using h

/-! ## The colored incidence graph -/

/-- The 18 edges of the Frucht graph. -/
def fruchtEdge : Fin 18 → Fin 12 × Fin 12 :=
  ![(0, 1), (0, 7), (0, 11), (1, 2), (1, 11), (2, 3), (2, 10), (3, 4), (3, 5), (4, 5), (4, 9),
    (5, 6), (6, 7), (6, 8), (7, 8), (8, 9), (9, 10), (10, 11)]

/-- Incidence of a vertex and an edge. -/
def inc (v : Fin 12) (e : Fin 18) : Prop := v = (fruchtEdge e).1 ∨ v = (fruchtEdge e).2

instance (v : Fin 12) (e : Fin 18) : Decidable (inc v e) := by unfold inc; infer_instance

/-- Adjacency of the incidence graph `I(Φ)`: vertex-nodes `inl v`, edge-nodes `inr e`. -/
def incAdj : Fin 12 ⊕ Fin 18 → Fin 12 ⊕ Fin 18 → Prop
  | .inl v, .inr e => inc v e
  | .inr e, .inl v => inc v e
  | _, _ => False

instance : DecidableRel incAdj := fun x y => by
  cases x <;> cases y <;> unfold incAdj <;> infer_instance

/-- The incidence graph of the Frucht graph. -/
def incGraph : SimpleGraph (Fin 12 ⊕ Fin 18) where
  Adj := incAdj
  symm := ⟨by intro x y h; cases x <;> cases y <;> simp_all [incAdj]⟩
  loopless := ⟨by intro x h; cases x <;> simp_all [incAdj]⟩

instance : DecidableRel incGraph.Adj := inferInstanceAs (DecidableRel incAdj)

/-- The initial coloring: vertex-nodes and edge-nodes. -/
def incColor (x : Fin 12 ⊕ Fin 18) : Bool := x.isLeft

/-- One round of color refinement: own color and the multiset of neighbor colors. -/
def refineRound {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → Bool)
    (x : V) : Bool × Multiset Bool :=
  (c x, (Finset.univ.filter (G.Adj x)).val.map c)

set_option maxRecDepth 100000 in
theorem incidence_refine_values : ∀ x, refineRound incGraph incColor x =
    if x.isLeft then (true, {false, false, false}) else (false, {true, true}) := by
  decide +kernel

/-- **Stable colors** (004h, Theorem 3.1, first part): one round of color refinement on the
colored incidence graph induces the same partition as the initial coloring (12 vertex-nodes,
18 edge-nodes); the refinement is stable immediately. -/
theorem incidence_refinement_stable (x y : Fin 12 ⊕ Fin 18) :
    refineRound incGraph incColor x = refineRound incGraph incColor y ↔
      incColor x = incColor y := by
  rw [incidence_refine_values, incidence_refine_values]
  cases x <;> cases y <;> simp [incColor]

theorem frucht_adj_iff_inc : ∀ u v, fruchtAdj u v ↔ (u ≠ v ∧ ∃ e, inc u e ∧ inc v e) := by
  decide

theorem edge_determined : ∀ e e' : Fin 18, (∀ v, inc v e ↔ inc v e') → e = e' := by decide

/-- **No nontrivial color-preserving automorphism** (004h, Theorem 3.1, second part). -/
theorem incidence_rigid (τ : incGraph ≃g incGraph) (hτ : ∀ x, incColor (τ x) = incColor x) :
    ∀ x, τ x = x := by
  -- `τ` and `τ⁻¹` preserve the two kinds of nodes
  have hL : ∀ (φ : incGraph ≃g incGraph), (∀ x, incColor (φ x) = incColor x) →
      ∀ v, ∃ w, φ (.inl v) = .inl w := by
    intro φ hφ v
    have := hφ (.inl v)
    rcases h : φ (.inl v) with w | e
    · exact ⟨w, rfl⟩
    · rw [h] at this; simp [incColor] at this
  have hR : ∀ (φ : incGraph ≃g incGraph), (∀ x, incColor (φ x) = incColor x) →
      ∀ e, ∃ e', φ (.inr e) = .inr e' := by
    intro φ hφ e
    have := hφ (.inr e)
    rcases h : φ (.inr e) with w | e'
    · rw [h] at this; simp [incColor] at this
    · exact ⟨e', rfl⟩
  have hτ' : ∀ x, incColor (τ.symm x) = incColor x := by
    intro x; conv_rhs => rw [← τ.apply_symm_apply x]
    rw [hτ]
  choose σf hσf using hL τ hτ
  choose σg hσg using hL τ.symm hτ'
  choose εf hεf using hR τ hτ
  choose εg hεg using hR τ.symm hτ'
  have hfg : ∀ v, σg (σf v) = v := by
    intro v
    have : τ.symm (τ (.inl v)) = .inl v := τ.symm_apply_apply _
    rw [hσf, hσg] at this; exact Sum.inl_injective this
  have hgf : ∀ v, σf (σg v) = v := by
    intro v
    have : τ (τ.symm (.inl v)) = .inl v := τ.apply_symm_apply _
    rw [hσg, hσf] at this; exact Sum.inl_injective this
  have hεgf : ∀ e, εf (εg e) = e := by
    intro e
    have : τ (τ.symm (.inr e)) = .inr e := τ.apply_symm_apply _
    rw [hεg, hεf] at this; exact Sum.inr_injective this
  let σ : Perm (Fin 12) := ⟨σf, σg, hfg, hgf⟩
  have hinc : ∀ v e, inc (σf v) (εf e) ↔ inc v e := by
    intro v e
    have := τ.map_adj_iff (v := .inl v) (w := .inr e)
    rw [hσf, hεf] at this
    exact this
  have hσ : ∀ u v, fruchtAdj (σ u) (σ v) ↔ fruchtAdj u v := by
    intro u v
    rw [frucht_adj_iff_inc, frucht_adj_iff_inc]
    simp only [σ, Equiv.coe_fn_mk]
    constructor
    · rintro ⟨hne, e, h1, h2⟩
      refine ⟨fun h => hne (by rw [h]), εg e, ?_, ?_⟩
      · rw [← hinc, hεgf]; exact h1
      · rw [← hinc, hεgf]; exact h2
    · rintro ⟨hne, e, h1, h2⟩
      refine ⟨fun h => hne (by rw [← hfg u, ← hfg v, h]), εf e, (hinc u e).2 h1,
        (hinc v e).2 h2⟩
  have hσ1 := frucht_rigid σ hσ
  have hσid : ∀ v, σf v = v := fun v => by
    have := congrArg (fun f : Perm (Fin 12) => f v) hσ1; simpa [σ] using this
  intro x
  rcases x with v | e
  · rw [hσf, hσid]
  · rw [hεf]
    congr 1
    symm
    apply edge_determined
    intro v
    have := hinc v e
    rw [hσid] at this
    exact this.symm

/-! ## Transitivity is not enough -/

/-- Tuples of `q = n + 1` records, rotated by `Fin (n + 1)`. -/
def Necklace (n : ℕ) (D : Type*) := Fin (n + 1) → D

instance (n : ℕ) (D : Type*) : AddAction (Fin (n + 1)) (Necklace n D) where
  vadd j x := fun i => x (i + j)
  zero_vadd x := by funext i; show x (i + 0) = x i; rw [add_zero]
  add_vadd j k x := by funext i; show x (i + (j + k)) = x (i + j + k); rw [add_assoc]

instance (n : ℕ) (D : Type*) [Fintype D] : Fintype (Necklace n D) :=
  inferInstanceAs (Fintype (Fin (n + 1) → D))

open Classical in
/-- **Transitive action with many orbits** (004h, Theorem 4.1). Rotations act transitively on
the `q = n + 1` positions, yet the number of orbits on `D^q` is at least `|D|^q / q`:
`|D|^q ≤ q · #orbits`. -/
theorem rotation_orbits_ge (n : ℕ) (D : Type*) [Fintype D] :
    (∀ i i' : Fin (n + 1), ∃ j : Fin (n + 1), i + j = i') ∧
    Fintype.card D ^ (n + 1) ≤
      (n + 1) * Fintype.card (AddAction.orbitRel.Quotient (Fin (n + 1)) (Necklace n D)) := by
  refine ⟨fun i i' => ⟨i' - i, by abel⟩, ?_⟩
  have hb := AddAction.sum_card_fixedBy_eq_card_orbits_mul_card_addGroup (Fin (n + 1))
    (Necklace n D)
  have h0 : Fintype.card (AddAction.fixedBy (Necklace n D) (0 : Fin (n + 1))) =
      Fintype.card D ^ (n + 1) := by
    rw [Fintype.card_congr (Equiv.subtypeUnivEquiv (fun x => by simp))]
    trans Fintype.card (Fin (n + 1) → D)
    · exact Fintype.card_congr (Equiv.refl _)
    · simp
  have hle : Fintype.card (AddAction.fixedBy (Necklace n D) (0 : Fin (n + 1))) ≤
      ∑ g : Fin (n + 1), Fintype.card (AddAction.fixedBy (Necklace n D) g) :=
    Finset.single_le_sum (f := fun g => Fintype.card (AddAction.fixedBy (Necklace n D) g))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
  rw [hb, h0, Fintype.card_fin] at hle
  rw [mul_comm]; exact hle

/-! ## Symmetry can hide a hard coefficient -/

/-- An `A₅` selector `M(c, x) = e` if `c = e`, `x` otherwise, as a group term (Maurer–Rhodes). -/
theorem exists_selector : ∃ M : GTerm A5 2, ∀ c x : A5,
    M.eval ![c, x] = if c = 1 then 1 else x := by
  classical
  obtain ⟨M, hM⟩ := maurer_rhodes A5_not_commutative
    (fun y : Fin 2 → A5 => if y 0 = 1 then 1 else y 1)
  exact ⟨M, fun c x => by rw [hM]; simp⟩

/-- The shell `F_g(x)_i = M(g, x_i)`. -/
def shell (M : GTerm A5 2) (g : A5) {q : ℕ} (x : Fin q → A5) : Fin q → A5 :=
  fun i => M.eval ![g, x i]

/-- **Symmetric shell with a hard coefficient** (004h, Theorem 5.1). With the selector `M`,
the block `F_g` is equivariant under every permutation of the records, its response is the
constant `e` when `g = e` and the identity when `g ≠ e`. -/
theorem symmetric_shell : ∃ M : GTerm A5 2,
    (∀ (g : A5) (q : ℕ) (τ : Perm (Fin q)) (x : Fin q → A5),
      shell M g (x ∘ τ) = shell M g x ∘ τ) ∧
    (∀ (q : ℕ) (x : Fin q → A5), shell M 1 x = 1) ∧
    (∀ g : A5, g ≠ 1 → ∀ (q : ℕ) (x : Fin q → A5), shell M g x = x) := by
  obtain ⟨M, hM⟩ := exists_selector
  refine ⟨M, fun g q τ x => rfl, fun q x => ?_, fun g hg q x => ?_⟩
  · funext i; simp [shell, hM]
  · funext i; simp [shell, hM, hg]

/-- The response of the shell decides an arbitrary compiled Boolean circuit (004h,
Theorem 5.1, last sentence): with `g` the `A₅` copy of a Boolean node, the response of `F_g` on
one record is the identity map iff the node is true. -/
theorem symmetric_shell_boolean (bs : List BOp) (hwf : BWellFormed bs) {k : ℕ}
    (hk : k < bs.length) :
    ∃ M : GTerm A5 2, ∀ hmem : val id (compile bs).1 ((compile bs).2.getD k 0) ∈
        alternatingGroup (Fin 5),
      ((∀ x : Fin 1 → A5, shell M ⟨_, hmem⟩ x = x) ↔ bval bs k = true) := by
  obtain ⟨M, -, h1, h2⟩ := symmetric_shell
  refine ⟨M, fun hmem => ?_⟩
  have hv := (boolean_to_A5 bs hwf).2.2.2 k hk
  by_cases hb : bval bs k = true
  · rw [hb] at hv
    have hne : (⟨_, hmem⟩ : A5) ≠ 1 := by
      intro h
      have := congrArg Subtype.val h
      simp only [OneMemClass.coe_one] at this
      rw [hv] at this; exact absurd this (by decide)
    simp only [hb, iff_true]
    exact fun x => h2 _ hne 1 x
  · have hb' : bval bs k = false := by simpa using hb
    rw [hb'] at hv
    have he : (⟨_, hmem⟩ : A5) = 1 := Subtype.ext (by simpa [enc] using hv)
    simp only [hb', Bool.false_eq_true, iff_false]
    intro h
    have := h (fun _ => ⟨aA, gadget_identities.1.1⟩)
    rw [he, h1] at this
    have := congrArg (fun f => ((f 0 : A5) : Perm (Fin 5))) this
    simp at this
    exact absurd this (by decide)

/-! ## Certified transpositions generate the symmetric group -/

/-- **Swap-forest generation** (004h, Theorem 6.4, connected case; Lemma 6.3 supplies the
hypothesis from certified transpositions). If a record block `B` is equivariant under the
transpositions along the edges of a connected graph on the `q` records, it is equivariant under
every permutation of the records. -/
theorem swap_forest {q : ℕ} {E Cf : Type*} (B : Cf → (Fin q → E) → (Fin q → E))
    (G : SimpleGraph (Fin q)) (hconn : G.Connected)
    (hswap : ∀ i j, G.Adj i j → ∀ c x, B c (x ∘ Equiv.swap i j) = B c x ∘ Equiv.swap i j) :
    ∀ τ : Perm (Fin q), ∀ c x, B c (x ∘ τ) = B c x ∘ τ := by
  -- the equivariance group
  let H : Subgroup (Perm (Fin q)) :=
    { carrier := {τ | ∀ c x, B c (x ∘ τ) = B c x ∘ τ}
      one_mem' := fun c x => rfl
      mul_mem' := by
        intro σ τ hσ hτ c x
        show B c (x ∘ ⇑(σ * τ)) = B c x ∘ ⇑(σ * τ)
        have e1 : x ∘ ⇑(σ * τ) = (x ∘ ⇑σ) ∘ ⇑τ := rfl
        have e2 : B c x ∘ ⇑(σ * τ) = (B c x ∘ ⇑σ) ∘ ⇑τ := rfl
        rw [e1, e2, hτ, hσ]
      inv_mem' := by
        intro τ hτ c x
        show B c (x ∘ ⇑(τ⁻¹)) = B c x ∘ ⇑(τ⁻¹)
        have := hτ c (x ∘ ⇑(τ⁻¹))
        have e : (x ∘ ⇑(τ⁻¹)) ∘ ⇑τ = x := by funext i; simp
        rw [e] at this
        rw [this]; funext i; simp }
  let S : Set (Perm (Fin q)) := {σ | ∃ i j, G.Adj i j ∧ σ = Equiv.swap i j}
  have hS : ∀ σ ∈ S, σ.IsSwap := by
    rintro σ ⟨i, j, hij, rfl⟩; exact ⟨i, j, G.ne_of_adj hij, rfl⟩
  have htrans : MulAction.IsPretransitive (Subgroup.closure S) (Fin q) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨w⟩ := hconn.preconnected a b
    induction w with
    | nil => exact ⟨1, rfl⟩
    | @cons u v c huv w ih =>
      obtain ⟨g, hg⟩ := ih
      refine ⟨g * ⟨Equiv.swap u v, Subgroup.subset_closure ⟨u, v, huv, rfl⟩⟩, ?_⟩
      rw [mul_smul]
      show g • (Equiv.swap u v u) = c
      rw [Equiv.swap_apply_left]; exact hg
  have htop : Subgroup.closure S = ⊤ := closure_of_isSwap_of_isPretransitive hS
  have hle : Subgroup.closure S ≤ H := by
    rw [Subgroup.closure_le]
    rintro σ ⟨i, j, hij, rfl⟩
    exact hswap i j hij
  intro τ
  exact hle (htop ▸ Subgroup.mem_top τ)

end GC.A5Programs
