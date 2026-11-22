import GC.GroupTheory.A5Programs.TwoGen
import GC.GroupTheory.A5Programs.MaurerRhodes
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import Mathlib.Data.Fintype.EquivFin

/-!
# Finding pigeonhole collisions in `A₅` (manuscript 004a)

* `probe_selector_A5`: 61 fixed unary terms `T_0, …, T_60` over `A₅` such that, for every value
  `x`, the probe values `T_i(x)` have exactly one equal pair, `{0, j+1}` where `x = g_j`
  (Theorem 3.2); hence any colliding pair determines `x` (`collision_determines_value`,
  Corollary 3.4). The terms exist by the Maurer–Rhodes theorem, proved in `MaurerRhodes.lean`.
* `predicate_complete_A5`: for every `S ⊆ A₅` there are unary terms `U, V` with
  `U(x) = V(x) ↔ x ∈ S` (Theorem 3.5).
* `universal_collisions`: nodes with explicit value tables over a context set `X` contain at least
  `(N - 60^|X|)/2` disjoint pairs that are equal in every context (Theorem 4.2, Corollary 4.3).
* `calculus_sound`, `calculus_complete`: the value/equality calculus (R1)–(R6) is sound and
  complete (Theorem 5.1).
-/

namespace GC.A5Programs

open Equiv

/-! ## The probe selector -/

section Selector

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G] [IsSimpleGroup G]

/-- The coloring of the `n + 1` probe positions for anchor value `x`: position `0` and position
`enum x + 1` get the identity, the other positions get the other elements bijectively. -/
def probeColor {n : ℕ} (enum : G ≃ Fin n) (x : G) : Fin (n + 1) → G :=
  Fin.cases 1 (fun i => enum.symm (Equiv.swap (enum 1) (enum x) i))

omit [Fintype G] [DecidableEq G] [IsSimpleGroup G] in
theorem probeColor_eq_iff {n : ℕ} (enum : G ≃ Fin n) (x : G) (i j : Fin (n + 1)) (hij : i < j) :
    probeColor enum x i = probeColor enum x j ↔ i = 0 ∧ j = (enum x).succ := by
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => exact absurd hij (lt_irrefl _)
    | succ j =>
      simp only [probeColor, Fin.cases_zero, Fin.cases_succ, true_and, Fin.succ_inj]
      rw [eq_comm, Equiv.symm_apply_eq, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]
  | succ i =>
    induction j using Fin.cases with
    | zero => exact absurd hij (by simp)
    | succ j =>
      simp only [probeColor, Fin.cases_succ, Fin.succ_ne_zero, false_and, iff_false]
      intro h
      have := (Equiv.swap (enum 1) (enum x)).injective (enum.symm.injective h)
      subst this; exact lt_irrefl _ hij

/-- **The probe selector** (004a, Theorem 3.2), for any finite simple nonabelian group with an
enumeration `enum : G ≃ Fin n`: there are `n + 1` unary terms such that, for every `x`, the
only colliding pair of probe values is `{0, enum x + 1}`. -/
theorem probe_selector (hG : ∃ a b : G, a * b ≠ b * a) {n : ℕ} (enum : G ≃ Fin n) :
    ∃ T : Fin (n + 1) → GTerm G 1, ∀ x : G, ∀ i j : Fin (n + 1), i < j →
      ((T i).eval (fun _ => x) = (T j).eval (fun _ => x) ↔ i = 0 ∧ j = (enum x).succ) := by
  have hT : ∀ i : Fin (n + 1), IsPolynomial (fun y : Fin 1 → G => probeColor enum (y 0) i) :=
    fun i => maurer_rhodes hG _
  choose T hT using hT
  exact ⟨T, fun x i j hij => by rw [hT i, hT j]; exact probeColor_eq_iff enum x i j hij⟩

end Selector

/-- `A₅` as a group: the alternating group on five points. -/
abbrev A5 := alternatingGroup (Fin 5)

theorem A5_not_commutative : ∃ a b : A5, a * b ≠ b * a := by
  refine ⟨⟨pA, (mem_A5list_iff _).1 (by decide)⟩, ⟨qA, (mem_A5list_iff _).1 (by decide)⟩, ?_⟩
  intro h
  have := congrArg Subtype.val h
  simp only [Subgroup.coe_mul] at this
  revert this; decide

/-- **61-probe collision selector for `A₅`** (004a, Theorem 3.2). There are an enumeration
`A₅ ≃ Fin 60` and 61 fixed unary group terms `T_0, …, T_60` with constants in `A₅` such that for
every value `x` of the anchor node, the probe values `T_i(x)` contain exactly one equal pair,
namely `{0, enum x + 1}`. -/
theorem probe_selector_A5 : ∃ (enum : A5 ≃ Fin 60) (T : Fin 61 → GTerm A5 1),
    ∀ x : A5, ∀ i j : Fin 61, i < j →
      ((T i).eval (fun _ => x) = (T j).eval (fun _ => x) ↔ i = 0 ∧ j = (enum x).succ) := by
  classical
  let enum : A5 ≃ Fin 60 := Fintype.equivFinOfCardEq card_alternatingGroup_five
  obtain ⟨T, hT⟩ := probe_selector A5_not_commutative enum
  exact ⟨enum, T, hT⟩

/-- **Collision search is as hard as evaluation** (004a, Corollary 3.4, mathematical core): any
colliding pair of the 61 probes determines the value of the anchor. -/
theorem collision_determines_value : ∃ T : Fin 61 → GTerm A5 1,
    (∀ x : A5, ∃ i j : Fin 61, i < j ∧ (T i).eval (fun _ => x) = (T j).eval (fun _ => x)) ∧
    ∀ x y : A5, ∀ i j : Fin 61, i < j →
      (T i).eval (fun _ => x) = (T j).eval (fun _ => x) →
      (T i).eval (fun _ => y) = (T j).eval (fun _ => y) → x = y := by
  obtain ⟨enum, T, hT⟩ := probe_selector_A5
  refine ⟨T, fun x => ⟨0, (enum x).succ, Fin.succ_pos _, (hT x _ _ (Fin.succ_pos _)).2
    ⟨rfl, rfl⟩⟩, fun x y i j hij hx hy => ?_⟩
  have h1 := ((hT x i j hij).1 hx).2
  have h2 := ((hT y i j hij).1 hy).2
  exact enum.injective (Fin.succ_injective _ (h1.symm.trans h2))

/-- **Predicate-complete equality** (004a, Theorem 3.5): for every `S ⊆ A₅` there are unary terms
`U, V` with `U(x) = V(x)` exactly when `x ∈ S`. -/
theorem predicate_complete_A5 (S : Set A5) :
    ∃ U V : GTerm A5 1, ∀ x : A5, U.eval (fun _ => x) = V.eval (fun _ => x) ↔ x ∈ S := by
  classical
  obtain ⟨a, b, hab⟩ := A5_not_commutative
  have hb : b ≠ 1 := by rintro rfl; simp at hab
  obtain ⟨H, hH⟩ := maurer_rhodes A5_not_commutative
    (fun y : Fin 1 → A5 => if y 0 ∈ S then 1 else b)
  refine ⟨H, .const 1, fun x => ?_⟩
  rw [hH]
  by_cases hx : x ∈ S <;> simp [GTerm.eval, hx, hb]

/-! ## Universal collisions -/

/-- Pigeonhole matching: if `f` takes at most `m` values on `s`, there are disjoint pairs of
distinct elements of `s` with equal `f`-values, at least `(|s| - m)/2` of them. -/
theorem exists_disjoint_equal_pairs {α β : Type*} [DecidableEq α] [DecidableEq β] (f : α → β)
    (m : ℕ) : ∀ s : Finset α, (s.image f).card ≤ m →
    ∃ M : Finset (α × α), (∀ p ∈ M, p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 ≠ p.2 ∧ f p.1 = f p.2) ∧
      (M.image Prod.fst ∪ M.image Prod.snd).card = 2 * M.card ∧ s.card ≤ 2 * M.card + m := by
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
    intro hm
    by_cases hinj : Set.InjOn f s
    · refine ⟨∅, by simp, by simp, ?_⟩
      rw [← Finset.card_image_of_injOn hinj]; simpa using hm
    · simp only [Set.InjOn, not_forall] at hinj
      obtain ⟨x, hx, y, hy, hfxy, hxy⟩ := hinj
      rw [Finset.mem_coe] at hx hy
      set s' := (s.erase x).erase y with hs'
      have hsub : s' ⊂ s := by
        refine Finset.ssubset_iff_subset_ne.2 ⟨fun z hz => ?_, fun h => ?_⟩
        · simp [hs'] at hz; exact hz.2.2
        · have : x ∈ s' := h ▸ hx
          simp [hs'] at this
      have hm' : (s'.image f).card ≤ m :=
        (Finset.card_le_card (Finset.image_subset_image hsub.1)).trans hm
      obtain ⟨M, hM1, hM2, hM3⟩ := ih s' hsub hm'
      have hxs' : x ∉ s' := by simp [hs']
      have hys' : y ∉ s' := by simp [hs']
      have hends : ∀ z ∈ M.image Prod.fst ∪ M.image Prod.snd, z ∈ s' := by
        intro z hz
        simp only [Finset.mem_union, Finset.mem_image] at hz
        rcases hz with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
        · exact (hM1 p hp).1
        · exact (hM1 p hp).2.1
      have hnot : (x, y) ∉ M := fun h => hxs' (hM1 _ h).1
      refine ⟨insert (x, y) M, ?_, ?_, ?_⟩
      · intro p hp
        rcases Finset.mem_insert.1 hp with rfl | hp
        · exact ⟨hx, hy, hxy, hfxy⟩
        · obtain ⟨h1, h2, h3, h4⟩ := hM1 p hp
          exact ⟨hsub.1 h1, hsub.1 h2, h3, h4⟩
      · rw [Finset.card_insert_of_notMem hnot, Finset.image_insert, Finset.image_insert]
        have e : insert (x, y).1 (M.image Prod.fst) ∪ insert (x, y).2 (M.image Prod.snd) =
            insert x (insert y (M.image Prod.fst ∪ M.image Prod.snd)) := by
          ext z; simp only [Finset.mem_union, Finset.mem_insert]; tauto
        rw [e, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, hM2]
        · ring
        · exact fun h => hys' (hends y h)
        · simp only [Finset.mem_insert, not_or]
          exact ⟨hxy, fun h => hxs' (hends x h)⟩
      · rw [Finset.card_insert_of_notMem hnot]
        have : s.card = s'.card + 2 := by
          rw [hs', Finset.card_erase_of_mem (by simp [Ne.symm hxy, hy]),
            Finset.card_erase_of_mem hx]
          have : 2 ≤ s.card := by
            have : ({x, y} : Finset α) ⊆ s := by
              intro z hz; simp at hz; rcases hz with rfl | rfl <;> assumption
            have h2 := Finset.card_le_card this
            rwa [Finset.card_pair hxy] at h2
          omega
        omega

/-- **Universal collisions under a small context** (004a, Theorem 4.2 and Corollary 4.3). Let
`U` be a set of `N` nodes with explicit value tables `f u : X → A₅` over a finite context set `X`.
Then there are pairwise disjoint pairs of distinct nodes of `U`, at least `(N - 60^|X|)/2` of
them, whose tables agree, so that the two nodes are equal whatever the true context is. For
`|X| = 2` the bound is `(N - 3600)/2`. -/
theorem universal_collisions {ι X : Type*} [DecidableEq ι] [Fintype X] [DecidableEq X]
    (U : Finset ι) (f : ι → X → A5) :
    ∃ M : Finset (ι × ι), (∀ p ∈ M, p.1 ∈ U ∧ p.2 ∈ U ∧ p.1 ≠ p.2 ∧ ∀ x, f p.1 x = f p.2 x) ∧
      (M.image Prod.fst ∪ M.image Prod.snd).card = 2 * M.card ∧
      U.card ≤ 2 * M.card + 60 ^ Fintype.card X := by
  classical
  have hm : (U.image f).card ≤ 60 ^ Fintype.card X := by
    calc (U.image f).card ≤ (Finset.univ : Finset (X → A5)).card := Finset.card_le_univ _
      _ = 60 ^ Fintype.card X := by
        rw [Finset.card_univ, Fintype.card_fun, card_alternatingGroup_five]
  obtain ⟨M, h1, h2, h3⟩ := exists_disjoint_equal_pairs f _ U hm
  exact ⟨M, fun p hp => ⟨(h1 p hp).1, (h1 p hp).2.1, (h1 p hp).2.2.1,
    fun x => congrFun (h1 p hp).2.2.2 x⟩, h2, h3⟩

/-! ## The value and equality calculus -/

section Calculus

variable {α : Type} {G : Type*} [Group G] (ν : α → G) (ops : List (Op α))

/-- Facts: `V g u` (node `u` has value `g`) and `E u v` (nodes `u, v` have equal values). -/
inductive Fact (G : Type*) where
  | V : G → ℕ → Fact G
  | E : ℕ → ℕ → Fact G

/-- The calculus (R1)–(R6) of 004a, Section 5. -/
inductive Derivable : Fact G → Prop
  | leaf {u : ℕ} {a : α} : ops[u]? = some (.leaf a) → Derivable (.V (ν a) u)
  | fwdMul {z x y : ℕ} {g h : G} : ops[z]? = some (.mul x y) →
      Derivable (.V g x) → Derivable (.V h y) → Derivable (.V (g * h) z)
  | fwdInv {z x : ℕ} {g : G} : ops[z]? = some (.inv x) →
      Derivable (.V g x) → Derivable (.V g⁻¹ z)
  | bwdInv {z x : ℕ} {g : G} : ops[z]? = some (.inv x) →
      Derivable (.V g z) → Derivable (.V g⁻¹ x)
  | cancelLeft {z x y : ℕ} {k g : G} : ops[z]? = some (.mul x y) →
      Derivable (.V k z) → Derivable (.V g x) → Derivable (.V (g⁻¹ * k) y)
  | cancelRight {z x y : ℕ} {k h : G} : ops[z]? = some (.mul x y) →
      Derivable (.V k z) → Derivable (.V h y) → Derivable (.V (k * h⁻¹) x)
  | eqOfVal {u v : ℕ} {g : G} : Derivable (.V g u) → Derivable (.V g v) → Derivable (.E u v)
  | congMul {z x y z' x' y' : ℕ} : ops[z]? = some (.mul x y) → ops[z']? = some (.mul x' y') →
      Derivable (.E x x') → Derivable (.E y y') → Derivable (.E z z')
  | cancMulLeft {z x y z' x' y' : ℕ} : ops[z]? = some (.mul x y) →
      ops[z']? = some (.mul x' y') →
      Derivable (.E z z') → Derivable (.E x x') → Derivable (.E y y')
  | cancMulRight {z x y z' x' y' : ℕ} : ops[z]? = some (.mul x y) →
      ops[z']? = some (.mul x' y') →
      Derivable (.E z z') → Derivable (.E y y') → Derivable (.E x x')
  | congInv {z x z' x' : ℕ} : ops[z]? = some (.inv x) → ops[z']? = some (.inv x') →
      Derivable (.E x x') → Derivable (.E z z')
  | cancInv {z x z' x' : ℕ} : ops[z]? = some (.inv x) → ops[z']? = some (.inv x') →
      Derivable (.E z z') → Derivable (.E x x')
  | symm {u v : ℕ} : Derivable (.E u v) → Derivable (.E v u)
  | trans {u v w : ℕ} : Derivable (.E u v) → Derivable (.E v w) → Derivable (.E u w)

/-- Truth of a fact in the evaluation of the program. -/
def Fact.Holds : Fact G → Prop
  | .V g u => val ν ops u = g
  | .E u v => val ν ops u = val ν ops v

theorem val_of_getElem? (hwf : WellFormed ops) {z : ℕ} {op : Op α} (h : ops[z]? = some op) :
    val ν ops z = match op with
      | .leaf a => ν a
      | .mul i j => val ν ops i * val ν ops j
      | .inv i => (val ν ops i)⁻¹ := by
  obtain ⟨hz, hop⟩ := List.getElem?_eq_some_iff.1 h
  have hw := hwf z hz
  rw [hop] at hw
  rw [val_of_lt ν ops hz, hop]
  have hpre : ∀ i < z, val ν (ops.take z) i = val ν ops i := by
    intro i hi
    conv_rhs => rw [← List.take_append_drop z ops]
    rw [val_append_of_lt _ _ _ (by simp; omega)]
  cases op with
  | leaf a => rfl
  | mul i j =>
    show val ν (ops.take z) i * val ν (ops.take z) j = _
    rw [hpre i hw.1, hpre j hw.2]
  | inv i =>
    show (val ν (ops.take z) i)⁻¹ = _
    rw [hpre i hw]

theorem val_leaf_node (hwf : WellFormed ops) {z : ℕ} {a : α} (h : ops[z]? = some (.leaf a)) :
    val ν ops z = ν a := val_of_getElem? ν ops hwf h

theorem val_mul_node (hwf : WellFormed ops) {z x y : ℕ} (h : ops[z]? = some (.mul x y)) :
    val ν ops z = val ν ops x * val ν ops y := val_of_getElem? ν ops hwf h

theorem val_inv_node (hwf : WellFormed ops) {z x : ℕ} (h : ops[z]? = some (.inv x)) :
    val ν ops z = (val ν ops x)⁻¹ := val_of_getElem? ν ops hwf h

/-- **Soundness** (004a, Theorem 5.1): in a well-formed program every derivable fact is
true. -/
theorem calculus_sound (hwf : WellFormed ops) {f : Fact G} (h : Derivable ν ops f) :
    f.Holds ν ops := by
  induction h with
  | leaf hu => exact val_leaf_node ν ops hwf hu
  | fwdMul hz _ _ ihx ihy =>
    simp only [Fact.Holds] at *; rw [val_mul_node ν ops hwf hz, ihx, ihy]
  | fwdInv hz _ ihx => simp only [Fact.Holds] at *; rw [val_inv_node ν ops hwf hz, ihx]
  | bwdInv hz _ ihz =>
    simp only [Fact.Holds] at *; rw [val_inv_node ν ops hwf hz] at ihz; rw [← ihz, inv_inv]
  | cancelLeft hz _ _ ihz ihx =>
    simp only [Fact.Holds] at *; rw [val_mul_node ν ops hwf hz] at ihz; rw [← ihz, ← ihx]; group
  | cancelRight hz _ _ ihz ihy =>
    simp only [Fact.Holds] at *; rw [val_mul_node ν ops hwf hz] at ihz; rw [← ihz, ← ihy]; group
  | eqOfVal _ _ ihu ihv => simp only [Fact.Holds] at *; rw [ihu, ihv]
  | congMul hz hz' _ _ ihx ihy =>
    simp only [Fact.Holds] at *
    rw [val_mul_node ν ops hwf hz, val_mul_node ν ops hwf hz', ihx, ihy]
  | cancMulLeft hz hz' _ _ ihz ihx =>
    simp only [Fact.Holds] at *
    rw [val_mul_node ν ops hwf hz, val_mul_node ν ops hwf hz', ihx] at ihz
    exact mul_left_cancel ihz
  | cancMulRight hz hz' _ _ ihz ihy =>
    simp only [Fact.Holds] at *
    rw [val_mul_node ν ops hwf hz, val_mul_node ν ops hwf hz', ihy] at ihz
    exact mul_right_cancel ihz
  | congInv hz hz' _ ihx =>
    simp only [Fact.Holds] at *
    rw [val_inv_node ν ops hwf hz, val_inv_node ν ops hwf hz', ihx]
  | cancInv hz hz' _ ihz =>
    simp only [Fact.Holds] at *
    rw [val_inv_node ν ops hwf hz, val_inv_node ν ops hwf hz'] at ihz
    exact inv_injective ihz
  | symm _ ih => simp only [Fact.Holds] at *; exact ih.symm
  | trans _ _ ih1 ih2 => simp only [Fact.Holds] at *; exact ih1.trans ih2

/-- **Completeness** (004a, Theorem 5.1): in a well-formed program, `V (val u) u` is derivable
for every node `u`, and `E u v` is derivable whenever `val u = val v`. -/
theorem calculus_complete (hwf : WellFormed ops) :
    (∀ u < ops.length, Derivable ν ops (.V (val ν ops u) u)) ∧
    (∀ u < ops.length, ∀ v < ops.length, val ν ops u = val ν ops v →
      Derivable ν ops (.E u v)) := by
  have hV : ∀ u < ops.length, Derivable ν ops (.V (val ν ops u) u) := by
    intro u
    induction u using Nat.strong_induction_on with
    | _ u ih =>
      intro hu
      have hw := hwf u hu
      have hget : ops[u]? = some (ops[u]'hu) := List.getElem?_eq_getElem hu
      cases hop : ops[u]'hu with
      | leaf a =>
        rw [hop] at hget
        rw [val_leaf_node ν ops hwf hget]; exact .leaf hget
      | mul i j =>
        rw [hop] at hget hw
        rw [val_mul_node ν ops hwf hget]
        exact .fwdMul hget (ih i hw.1 (by have := hw.1; omega)) (ih j hw.2 (by have := hw.2; omega))
      | inv i =>
        rw [hop] at hget hw
        rw [val_inv_node ν ops hwf hget]
        exact .fwdInv hget (ih i hw (by have : i < u := hw; omega))
  refine ⟨hV, fun u hu v hv huv => ?_⟩
  have h2 := hV v hv
  rw [← huv] at h2
  exact .eqOfVal (hV u hu) h2

end Calculus

end GC.A5Programs
