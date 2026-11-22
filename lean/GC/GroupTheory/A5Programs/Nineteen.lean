import GC.GroupTheory.A5Programs.NineteenData
import GC.GroupTheory.A5Programs.Hall
import GC.GroupTheory.A5Programs.DeepCore
import GC.GroupTheory.A5Programs.Collisions
import Mathlib.GroupTheory.Perm.Fin

/-!
# Nineteen orbits and mirror words (manuscript 004c)

* `classification`: every pair `(x, y) ∈ A₅²` either generates `A₅` and is conjugate under `S₅`
  to exactly one of 19 explicit representatives, by exactly one conjugating permutation, or lies
  in one of 21 explicit maximal subgroups, each metabelian.
* `census_hot`, `census_cold`: exactly 2280 ordered pairs generate `A₅` and 1320 do not
  (Table 1); the generating pairs form 19 free orbits of `S₅` (Section 5).
* `hall_A5`: evaluation on the 19 representatives maps `F₂` onto `A₅^19` (Hall; Theorem 5.2).
* `mirror_word`, `mirror_selectors`, `no_interpolation`: Theorem 6.1, Corollaries 6.2 and 6.3.
-/

namespace GC.A5Programs

open Equiv
open scoped commutatorElement

/-! ## Words -/

/-- Evaluation of a two-letter word. -/
def PWord.eval {G : Type*} [Group G] (a b : G) : PWord → G
  | .one => 1
  | .x => a
  | .y => b
  | .mul u v => u.eval a b * v.eval a b
  | .inv u => (u.eval a b)⁻¹

theorem PWord.eval_hom {G H : Type*} [Group G] [Group H] (f : G →* H) (a b : G) (w : PWord) :
    f (w.eval a b) = w.eval (f a) (f b) := by
  induction w with
  | one => simp [PWord.eval]
  | x => rfl
  | y => rfl
  | mul u v hu hv => simp [PWord.eval, hu, hv]
  | inv u hu => simp [PWord.eval, hu]

theorem PWord.eval_mem {G : Type*} [Group G] (K : Subgroup G) {a b : G} (ha : a ∈ K)
    (hb : b ∈ K) (w : PWord) : w.eval a b ∈ K := by
  induction w with
  | one => exact K.one_mem
  | x => exact ha
  | y => exact hb
  | mul u v hu hv => exact K.mul_mem hu hv
  | inv u hu => exact K.inv_mem hu

/-- Words whose element orders separate the 19 orbits. -/
def invWords : List PWord :=
  [.mul .x .y, .mul .x (.inv .y), .mul (.mul .x .x) .y, .mul .x (.mul .y .y),
   .mul (.mul (.mul (.inv .x) (.inv .y)) .x) .y, .mul (.mul (.mul .x .y) .x) (.inv .y), .x, .y]

/-- An automorphism-invariant of a pair: which of the words have order dividing 2, 3, 5. -/
def ordInv {G : Type*} [Group G] [DecidableEq G] (a b : G) : List Bool :=
  invWords.flatMap fun w =>
    [decide ((w.eval a b) ^ 2 = 1), decide ((w.eval a b) ^ 3 = 1), decide ((w.eval a b) ^ 5 = 1)]

theorem ordInv_hom {G H : Type*} [Group G] [Group H] [DecidableEq G] [DecidableEq H]
    (f : G →* H) (hf : Function.Injective f) (a b : G) : ordInv (f a) (f b) = ordInv a b := by
  have key : ∀ (g : G) (n : ℕ), (f g ^ n = 1 ↔ g ^ n = 1) := by
    intro g n
    rw [← map_pow, ← map_one f]
    exact hf.eq_iff
  unfold ordInv
  congr 1
  funext w
  rw [← PWord.eval_hom]
  simp only [key]

/-! ## Checking the certificates -/

/-- Kernel check of one certificate. -/
def checkCert (x y : Perm (Fin 5)) : Cert → Bool
  | .hot k σ => decide (Function.Injective σ) &&
      (List.finRange 5).all (fun i => σ (x i) == repX k (σ i)) &&
      (List.finRange 5).all (fun i => σ (y i) == repY k (σ i))
  | .cold m => pmem x (maxList m) && pmem y (maxList m)

/-- All 3600 certificates. -/
def checkAll : Bool :=
  (A5list.zip certTable).all (fun p => (A5list.zip p.2).all (fun q => checkCert p.1 q.1 q.2))

set_option maxRecDepth 200000 in
theorem checkAll_true : checkAll = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem certTable_shape : certTable.length = 60 ∧ ∀ row ∈ certTable, row.length = 60 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem maxList_spec : ∀ m : Fin 21,
    ((maxList m).all fun a => (maxList m).all fun b =>
      pmem (a * b) (maxList m) && pmem ⁅a, b⁆ (normList m)) = true ∧
    ((maxList m).all fun a => pmem a⁻¹ (maxList m)) = true ∧ pmem 1 (maxList m) = true ∧
    ((normList m).all fun a => (normList m).all fun b =>
      pmem (a * b) (normList m) && peq (a * b) (b * a)) = true ∧
    ((normList m).all fun a => pmem a⁻¹ (normList m)) = true ∧ pmem 1 (normList m) = true ∧
    (pmem pA (maxList m) && pmem qA (maxList m)) = false := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rep_spec : ∀ k : Fin 19,
    peq ((repWordP k).eval (repX k) (repY k)) pA = true ∧
    peq ((repWordQ k).eval (repX k) (repY k)) qA = true ∧
    pmem (repX k) A5list = true ∧ pmem (repY k) A5list = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ordInv_nodup : (List.ofFn fun k : Fin 19 => ordInv (repX k) (repY k)).Nodup := by
  decide +kernel

/-! ## Consequences of the certificates -/

/-- The pair `(x, y)` generates `A₅`. -/
def IsHot (x y : Perm (Fin 5)) : Prop := Subgroup.closure {x, y} = alternatingGroup (Fin 5)

/-- `(x, y)` is conjugate by an element of `S₅` to the `k`-th representative. -/
def InOrbit (k : Fin 19) (x y : Perm (Fin 5)) : Prop :=
  ∃ σ : Perm (Fin 5), σ * x * σ⁻¹ = repX k ∧ σ * y * σ⁻¹ = repY k

/-- The maximal subgroup with element list `maxList m`. -/
def maxGrp (m : Fin 21) : Subgroup (Perm (Fin 5)) where
  carrier := {g | g ∈ maxList m}
  mul_mem' := by
    intro a b ha hb
    have := (maxList_spec m).1
    simp only [List.all_eq_true, Bool.and_eq_true] at this
    exact pmem_iff.1 (this a ha b hb).1
  one_mem' := pmem_iff.1 (maxList_spec m).2.2.1
  inv_mem' := by
    intro a ha
    have := (maxList_spec m).2.1
    simp only [List.all_eq_true] at this
    exact pmem_iff.1 (this a ha)

/-- The abelian normal subgroup with element list `normList m`. -/
def normGrp (m : Fin 21) : Subgroup (Perm (Fin 5)) where
  carrier := {g | g ∈ normList m}
  mul_mem' := by
    intro a b ha hb
    have := (maxList_spec m).2.2.2.1
    simp only [List.all_eq_true, Bool.and_eq_true] at this
    exact pmem_iff.1 (this a ha b hb).1
  one_mem' := pmem_iff.1 (maxList_spec m).2.2.2.2.2.1
  inv_mem' := by
    intro a ha
    have := (maxList_spec m).2.2.2.2.1
    simp only [List.all_eq_true] at this
    exact pmem_iff.1 (this a ha)

theorem maxGrp_comm_mem (m : Fin 21) {a b : Perm (Fin 5)} (ha : a ∈ maxGrp m)
    (hb : b ∈ maxGrp m) : ⁅a, b⁆ ∈ normGrp m := by
  have := (maxList_spec m).1
  simp only [List.all_eq_true, Bool.and_eq_true] at this
  exact pmem_iff.1 (this a ha b hb).2

theorem normGrp_comm (m : Fin 21) {a b : Perm (Fin 5)} (ha : a ∈ normGrp m)
    (hb : b ∈ normGrp m) : a * b = b * a := by
  have := (maxList_spec m).2.2.2.1
  simp only [List.all_eq_true, Bool.and_eq_true] at this
  exact peq_iff.1 (this a ha b hb).2

/-- Evaluation of the free group `F(X, Y)` at a pair. -/
def evalPair (x y : Perm (Fin 5)) : F2 →* Perm (Fin 5) := FreeGroup.lift ![x, y]

/-- Every maximal subgroup is metabelian: words of `F₂''` vanish on its pairs. -/
theorem maxGrp_kill (m : Fin 21) {x y : Perm (Fin 5)} (hx : x ∈ maxGrp m) (hy : y ∈ maxGrp m)
    {w : F2} (hw : w ∈ derivedSeries F2 2) : evalPair x y w = 1 := by
  have hK : ∀ v, evalPair x y v ∈ maxGrp m := by
    intro v
    induction v using FreeGroup.induction_on with
    | one => exact (maxGrp m).one_mem
    | of i => fin_cases i <;> simpa [evalPair]
    | inv_of i _ => fin_cases i <;> simpa [evalPair] using (maxGrp m).inv_mem (by simpa)
    | mul u v hu hv => rw [map_mul]; exact (maxGrp m).mul_mem hu hv
  have h1 : derivedSeries F2 1 ≤ (normGrp m).comap (evalPair x y) := by
    rw [derivedSeries_one, _root_.commutator, Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_comap, map_commutatorElement]
    exact maxGrp_comm_mem m (hK a) (hK b)
  have h2 : derivedSeries F2 2 ≤ (evalPair x y).ker := by
    rw [show derivedSeries F2 2 = ⁅derivedSeries F2 1, derivedSeries F2 1⁆ from
      derivedSeries_succ F2 1, Subgroup.commutator_le]
    intro a ha b hb
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact normGrp_comm m (h1 ha) (h1 hb)
  exact h2 hw

theorem pA_mem : pA ∈ alternatingGroup (Fin 5) := (mem_A5list_iff _).1 (by decide)
theorem qA_mem : qA ∈ alternatingGroup (Fin 5) := (mem_A5list_iff _).1 (by decide)

/-- `p = (1 2 3 4 5)` and `q = (1 2 3)` generate `A₅`. -/
theorem closure_pq : Subgroup.closure {pA, qA} = alternatingGroup (Fin 5) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro g hg
    rcases hg with rfl | rfl
    · exact pA_mem
    · exact qA_mem
  · intro g hg
    rw [← val_libOps_libIdx hg]
    apply val_mem_of_leaves
    intro i _
    fin_cases i
    · exact Subgroup.subset_closure (by simp [pq])
    · exact Subgroup.subset_closure (by simp [pq])

theorem maxGrp_ne (m : Fin 21) : ¬ (pA ∈ maxGrp m ∧ qA ∈ maxGrp m) := by
  rintro ⟨h1, h2⟩
  have := (maxList_spec m).2.2.2.2.2.2
  rw [show pmem pA (maxList m) = true from pmem_iff.2 h1,
    show pmem qA (maxList m) = true from pmem_iff.2 h2] at this
  exact absurd this (by decide)

theorem repX_mem (k : Fin 19) : repX k ∈ alternatingGroup (Fin 5) :=
  (mem_A5list_iff _).1 (pmem_iff.1 (rep_spec k).2.2.1)
theorem repY_mem (k : Fin 19) : repY k ∈ alternatingGroup (Fin 5) :=
  (mem_A5list_iff _).1 (pmem_iff.1 (rep_spec k).2.2.2)

/-- Each representative pair generates `A₅`. -/
theorem rep_hot (k : Fin 19) : IsHot (repX k) (repY k) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro g hg
    rcases hg with rfl | rfl
    · exact repX_mem k
    · exact repY_mem k
  · rw [← closure_pq, Subgroup.closure_le]
    have hx : repX k ∈ Subgroup.closure {repX k, repY k} := Subgroup.subset_closure (by simp)
    have hy : repY k ∈ Subgroup.closure {repX k, repY k} := Subgroup.subset_closure (by simp)
    intro g hg
    rcases hg with rfl | rfl
    · rw [← peq_iff.1 (rep_spec k).1]; exact PWord.eval_mem _ hx hy _
    · rw [← peq_iff.1 (rep_spec k).2.1]; exact PWord.eval_mem _ hx hy _

theorem conj_mem_alt {σ g : Perm (Fin 5)} (hg : g ∈ alternatingGroup (Fin 5)) :
    σ * g * σ⁻¹ ∈ alternatingGroup (Fin 5) :=
  (inferInstance : (alternatingGroup (Fin 5)).Normal).conj_mem g hg σ

/-- Pairs in an orbit generate `A₅`. -/
theorem hot_of_inOrbit {k : Fin 19} {x y : Perm (Fin 5)} (h : InOrbit k x y) : IsHot x y := by
  obtain ⟨σ, hx, hy⟩ := h
  have ex : x = σ⁻¹ * repX k * σ := by rw [← hx]; group
  have ey : y = σ⁻¹ * repY k * σ := by rw [← hy]; group
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro g hg
    rcases hg with rfl | rfl
    · rw [ex]; simpa using conj_mem_alt (σ := σ⁻¹) (repX_mem k)
    · rw [ey]; simpa using conj_mem_alt (σ := σ⁻¹) (repY_mem k)
  · intro g hg
    have hg' : σ * g * σ⁻¹ ∈ Subgroup.closure {repX k, repY k} := by
      rw [rep_hot k]; exact conj_mem_alt hg
    let f : Perm (Fin 5) →* Perm (Fin 5) := (MulAut.conj σ⁻¹).toMonoidHom
    have hle : Subgroup.closure {repX k, repY k} ≤ (Subgroup.closure {x, y}).comap f := by
      rw [Subgroup.closure_le]
      intro a ha
      rcases ha with rfl | rfl
      · rw [SetLike.mem_coe, Subgroup.mem_comap]
        have : f (repX k) = x := by simp [f, ex]
        rw [this]; exact Subgroup.subset_closure (by simp)
      · rw [SetLike.mem_coe, Subgroup.mem_comap]
        have : f (repY k) = y := by simp [f, ey]
        rw [this]; exact Subgroup.subset_closure (by simp)
    have := hle hg'
    rw [Subgroup.mem_comap] at this
    simpa [f, mul_assoc] using this

theorem exists_cert {x y : Perm (Fin 5)} (hx : x ∈ alternatingGroup (Fin 5))
    (hy : y ∈ alternatingGroup (Fin 5)) : ∃ c, checkCert x y c = true := by
  have hx' := (mem_A5list_iff x).2 hx
  have hy' := (mem_A5list_iff y).2 hy
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx'
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy'
  have hAll := checkAll_true
  simp only [checkAll, List.all_eq_true] at hAll
  have hi' : i < certTable.length := by rw [certTable_shape.1]; rwa [A5list_length] at hi
  have hrow := hAll (A5list[i], certTable[i]) (by
    have := List.getElem_mem (show i < (A5list.zip certTable).length by simp; omega)
    rwa [List.getElem_zip] at this)
  have hj' : j < (certTable[i]).length := by
    rw [certTable_shape.2 _ (List.getElem_mem _)]; rwa [A5list_length] at hj
  have := hrow (A5list[j], (certTable[i])[j]) (by
    have := List.getElem_mem (show j < (A5list.zip certTable[i]).length by simp; omega)
    rwa [List.getElem_zip] at this)
  exact ⟨_, this⟩

theorem inOrbit_of_cert {x y : Perm (Fin 5)} {k : Fin 19} {σ : Fin 5 → Fin 5}
    (h : checkCert x y (.hot k σ) = true) : InOrbit k x y := by
  simp only [checkCert, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_finRange,
    beq_iff_eq, true_implies] at h
  obtain ⟨⟨hinj, hx⟩, hy⟩ := h
  let σ' : Perm (Fin 5) := Equiv.ofBijective σ (Finite.injective_iff_bijective.1 hinj)
  refine ⟨σ', ?_, ?_⟩
  · rw [mul_inv_eq_iff_eq_mul]; ext i; simp [σ', hx i]
  · rw [mul_inv_eq_iff_eq_mul]; ext i; simp [σ', hy i]

/-- **Classification of pairs.** Every pair of elements of `A₅` either lies in an `S₅`-orbit of
one of the 19 representatives (and then generates `A₅`) or lies in one of the 21 metabelian
maximal subgroups (and then does not generate `A₅`). -/
theorem classification {x y : Perm (Fin 5)} (hx : x ∈ alternatingGroup (Fin 5))
    (hy : y ∈ alternatingGroup (Fin 5)) :
    (IsHot x y ↔ ∃ k, InOrbit k x y) ∧ (¬ IsHot x y ↔ ∃ m, x ∈ maxGrp m ∧ y ∈ maxGrp m) := by
  have hcold : ∀ m, x ∈ maxGrp m → y ∈ maxGrp m → ¬ IsHot x y := by
    intro m hxm hym hhot
    apply maxGrp_ne m
    have hle : Subgroup.closure {x, y} ≤ maxGrp m := by
      rw [Subgroup.closure_le]; intro g hg; rcases hg with rfl | rfl <;> assumption
    rw [hhot] at hle
    exact ⟨hle pA_mem, hle qA_mem⟩
  obtain ⟨c, hc⟩ := exists_cert hx hy
  cases c with
  | hot k σ =>
    have hk := inOrbit_of_cert hc
    exact ⟨⟨fun _ => ⟨k, hk⟩, fun _ => hot_of_inOrbit hk⟩,
      ⟨fun h => absurd (hot_of_inOrbit hk) h, fun ⟨m, h1, h2⟩ => hcold m h1 h2⟩⟩
  | cold m =>
    simp only [checkCert, Bool.and_eq_true] at hc
    have h1 : x ∈ maxGrp m := pmem_iff.1 hc.1
    have h2 : y ∈ maxGrp m := pmem_iff.1 hc.2
    exact ⟨⟨fun h => absurd h (hcold m h1 h2), fun ⟨k, hk⟩ => absurd (hot_of_inOrbit hk)
      (hcold m h1 h2)⟩, ⟨fun _ => ⟨m, h1, h2⟩, fun _ => hcold m h1 h2⟩⟩

/-- Words of `F₂''` vanish on non-generating pairs. -/
theorem cold_kill {x y : Perm (Fin 5)} (hx : x ∈ alternatingGroup (Fin 5))
    (hy : y ∈ alternatingGroup (Fin 5)) (hc : ¬ IsHot x y) {w : F2}
    (hw : w ∈ derivedSeries F2 2) : evalPair x y w = 1 := by
  obtain ⟨m, h1, h2⟩ := (classification hx hy).2.1 hc
  exact maxGrp_kill m h1 h2 hw

/-! ## Orbits are free and distinct -/

/-- The centralizer of `A₅` in `S₅` is trivial. -/
theorem centralizer_pq {ρ : Perm (Fin 5)} (hp : ρ * pA = pA * ρ) (hq : ρ * qA = qA * ρ) :
    ρ = 1 := by
  have ep : ∀ i, ρ (pA i) = pA (ρ i) := fun i => by
    have := congrArg (fun f : Perm (Fin 5) => f i) hp; simpa using this
  have eq : ∀ i, ρ (qA i) = qA (ρ i) := fun i => by
    have := congrArg (fun f : Perm (Fin 5) => f i) hq; simpa using this
  have key : ∀ v : Fin 5, qA v = pA v → qA (pA v) = pA (pA v) → v = 0 := by decide
  have h0 : ρ 0 = 0 := by
    apply key
    · rw [← eq 0, ← ep 0]; rfl
    · rw [← ep 0, show pA 0 = 1 from rfl, ← eq 1, ← ep 1]; rfl
  have h1 : ρ 1 = 1 := by rw [show (1 : Fin 5) = pA 0 from rfl, ep, h0]
  have h2 : ρ 2 = 2 := by rw [show (2 : Fin 5) = pA 1 from rfl, ep, h1]
  have h3 : ρ 3 = 3 := by rw [show (3 : Fin 5) = pA 2 from rfl, ep, h2]
  have h4 : ρ 4 = 4 := by rw [show (4 : Fin 5) = pA 3 from rfl, ep, h3]
  ext i; fin_cases i <;> simp [h0, h1, h2, h3, h4]

theorem ordInv_conj (ρ a b : Perm (Fin 5)) :
    ordInv (ρ * a * ρ⁻¹) (ρ * b * ρ⁻¹) = ordInv a b :=
  ordInv_hom (MulAut.conj ρ).toMonoidHom (MulAut.conj ρ).injective a b

/-- Each pair lies in at most one orbit. -/
theorem inOrbit_unique {k l : Fin 19} {x y : Perm (Fin 5)} (hk : InOrbit k x y)
    (hl : InOrbit l x y) : k = l := by
  obtain ⟨σ, hx, hy⟩ := hk
  obtain ⟨τ, hx', hy'⟩ := hl
  have e1 : repX l = (τ * σ⁻¹) * repX k * (τ * σ⁻¹)⁻¹ := by rw [← hx, ← hx']; group
  have e2 : repY l = (τ * σ⁻¹) * repY k * (τ * σ⁻¹)⁻¹ := by rw [← hy, ← hy']; group
  have hinv : ordInv (repX l) (repY l) = ordInv (repX k) (repY k) := by
    rw [e1, e2, ordInv_conj]
  have := (ordInv_nodup.getElem_inj_iff (i := k.val) (j := l.val) (hi := by simp)
    (hj := by simp)).1 (by simp only [List.getElem_ofFn, Fin.eta]; exact hinv.symm)
  exact Fin.ext this

/-- `S₅` acts freely on generating pairs. -/
theorem inOrbit_free {k : Fin 19} {x y σ τ : Perm (Fin 5)}
    (hσ : σ * x * σ⁻¹ = repX k ∧ σ * y * σ⁻¹ = repY k)
    (hτ : τ * x * τ⁻¹ = repX k ∧ τ * y * τ⁻¹ = repY k) : σ = τ := by
  set ρ := τ⁻¹ * σ with hρ
  have cx : ρ * x = x * ρ := by
    have := hσ.1.trans hτ.1.symm
    rw [hρ]; calc τ⁻¹ * σ * x = τ⁻¹ * (σ * x * σ⁻¹) * σ := by group
      _ = τ⁻¹ * (τ * x * τ⁻¹) * σ := by rw [this]
      _ = x * (τ⁻¹ * σ) := by group
  have cy : ρ * y = y * ρ := by
    have := hσ.2.trans hτ.2.symm
    rw [hρ]; calc τ⁻¹ * σ * y = τ⁻¹ * (σ * y * σ⁻¹) * σ := by group
      _ = τ⁻¹ * (τ * y * τ⁻¹) * σ := by rw [this]
      _ = y * (τ⁻¹ * σ) := by group
  have hxy : IsHot x y := hot_of_inOrbit ⟨σ, hσ⟩
  have hcent : Subgroup.closure {x, y} ≤ Subgroup.centralizer {ρ} := by
    rw [Subgroup.closure_le]
    intro g hg
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro h hh; rw [Set.mem_singleton_iff] at hh; subst hh
    rcases hg with rfl | rfl
    · exact cx
    · exact cy
  rw [hxy] at hcent
  have h1 := Subgroup.mem_centralizer_iff.1 (hcent pA_mem) ρ rfl
  have h2 := Subgroup.mem_centralizer_iff.1 (hcent qA_mem) ρ rfl
  have := centralizer_pq h1 h2
  rw [hρ, inv_mul_eq_one] at this
  exact this.symm

/-! ## The census -/

/-- The elements of `A₅` as a finset. -/
def A5set : Finset (Perm (Fin 5)) := A5list.toFinset

theorem mem_A5set {g : Perm (Fin 5)} : g ∈ A5set ↔ g ∈ alternatingGroup (Fin 5) := by
  simp [A5set, mem_A5list_iff]

/-- The parametrization of generating pairs by orbit index and conjugating permutation. -/
def orbitParam (p : Fin 19 × Perm (Fin 5)) : Perm (Fin 5) × Perm (Fin 5) :=
  (p.2⁻¹ * repX p.1 * p.2, p.2⁻¹ * repY p.1 * p.2)

theorem orbitParam_inOrbit (p : Fin 19 × Perm (Fin 5)) :
    InOrbit p.1 (orbitParam p).1 (orbitParam p).2 :=
  ⟨p.2, by simp [orbitParam, mul_assoc], by simp [orbitParam, mul_assoc]⟩

theorem orbitParam_injective : Function.Injective orbitParam := by
  rintro ⟨k, σ⟩ ⟨l, τ⟩ h
  have hk := orbitParam_inOrbit (k, σ)
  have hl := orbitParam_inOrbit (l, τ)
  rw [h] at hk
  have hkl : k = l := inOrbit_unique hk hl
  subst hkl
  have h1 : σ * (orbitParam (k, τ)).1 * σ⁻¹ = repX k ∧ σ * (orbitParam (k, τ)).2 * σ⁻¹ = repY k :=
    by rw [← h]; simp [orbitParam, mul_assoc]
  have h2 : τ * (orbitParam (k, τ)).1 * τ⁻¹ = repX k ∧ τ * (orbitParam (k, τ)).2 * τ⁻¹ = repY k :=
    by simp [orbitParam, mul_assoc]
  rw [inOrbit_free h1 h2]

open Classical in
/-- **Census of generating pairs** (004c, Table 1 and Section 5): exactly `2280 = 19 · 120`
ordered pairs of elements of `A₅` generate `A₅`; they are the images of the 19 representatives
under conjugation by the 120 elements of `S₅`, each pair exactly once. -/
theorem census_hot :
    ((A5set ×ˢ A5set).filter fun pr => IsHot pr.1 pr.2) = Finset.univ.image orbitParam ∧
    ((A5set ×ˢ A5set).filter fun pr => IsHot pr.1 pr.2).card = 2280 := by
  have heq : ((A5set ×ˢ A5set).filter fun pr => IsHot pr.1 pr.2) =
      Finset.univ.image orbitParam := by
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.mem_product, mem_A5set, Finset.mem_image,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨hx, hy⟩, hh⟩
      obtain ⟨k, σ, hσx, hσy⟩ := ((classification hx hy).1).1 hh
      refine ⟨(k, σ), ?_⟩
      simp only [orbitParam, Prod.mk.injEq]
      constructor
      · rw [← hσx]; group
      · rw [← hσy]; group
    · rintro ⟨p, hp⟩
      have hin := orbitParam_inOrbit p
      rw [hp] at hin
      have hx : (orbitParam p).1 = x := by rw [hp]
      have hy : (orbitParam p).2 = y := by rw [hp]
      refine ⟨⟨?_, ?_⟩, hot_of_inOrbit hin⟩
      · rw [← hx]; simpa [orbitParam] using conj_mem_alt (σ := p.2⁻¹) (repX_mem p.1)
      · rw [← hy]; simpa [orbitParam] using conj_mem_alt (σ := p.2⁻¹) (repY_mem p.1)
  refine ⟨heq, ?_⟩
  rw [heq, Finset.card_image_of_injective _ orbitParam_injective, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_perm, Fintype.card_fin]
  rfl

open Classical in
/-- Exactly `1320` ordered pairs of elements of `A₅` do not generate `A₅` (004c, Table 1). -/
theorem census_cold :
    ((A5set ×ˢ A5set).filter fun pr => ¬ IsHot pr.1 pr.2).card = 1320 := by
  have htot : (A5set ×ˢ A5set).card = 3600 := by
    rw [Finset.card_product, A5set, List.toFinset_card_of_nodup A5list_nodup, A5list_length]
  have := Finset.card_filter_add_card_filter_not (s := A5set ×ˢ A5set)
    (fun pr => IsHot pr.1 pr.2)
  rw [census_hot.2, htot] at this
  omega

/-! ## Hall's theorem for `A₅` and mirror words -/

/-- The representatives as elements of the group `A₅`. -/
def repXA (k : Fin 19) : A5 := ⟨repX k, repX_mem k⟩
/-- The representatives as elements of the group `A₅`. -/
def repYA (k : Fin 19) : A5 := ⟨repY k, repY_mem k⟩

/-- Evaluation on the 19 representatives, `Φ : F₂ → A₅^19`. -/
def Phi : F2 →* (Fin 19 → A5) := FreeGroup.lift ![fun k => repXA k, fun k => repYA k]

theorem Phi_apply (w : F2) (k : Fin 19) : ((Phi w k : A5) : Perm (Fin 5)) =
    evalPair (repX k) (repY k) w := by
  let f : F2 →* Perm (Fin 5) :=
    (alternatingGroup (Fin 5)).subtype.comp ((Pi.evalMonoidHom (fun _ => A5) k).comp Phi)
  have : f = evalPair (repX k) (repY k) := by
    apply FreeGroup.ext_hom
    intro i; fin_cases i <;> rfl
  exact congrArg (fun g : F2 →* Perm (Fin 5) => g w) this

theorem closure_repA (k : Fin 19) : Subgroup.closure {repXA k, repYA k} = ⊤ := by
  apply Subgroup.map_injective (alternatingGroup (Fin 5)).subtype_injective
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have : ((alternatingGroup (Fin 5)).subtype '' {repXA k, repYA k}) = {repX k, repY k} := by
    simp [Set.image_insert_eq, repXA, repYA]
  rw [this]; exact rep_hot k

/-- **Hall's theorem for `A₅`** (004c, Theorem 5.2): evaluation on the 19 representatives
maps `F₂` onto `A₅^19`. -/
theorem hall_A5 : Function.Surjective Phi := by
  rw [← MonoidHom.range_eq_top, Phi, FreeGroup.range_lift_eq_closure]
  have hr : Set.range ![fun k => repXA k, fun k => repYA k] =
      ({fun k => repXA k, fun k => repYA k} : Set (Fin 19 → A5)) := by
    ext f; simp [Fin.exists_fin_two, eq_comm, or_comm]
  rw [hr]
  apply hall_generation A5_not_commutative (fun k => repXA k) (fun k => repYA k) closure_repA
  rintro i j hij ⟨φ, h1, h2⟩
  apply hij
  have hsub : ∀ a b : A5, ordInv (a : Perm (Fin 5)) (b : Perm (Fin 5)) = ordInv a b :=
    fun a b => ordInv_hom (alternatingGroup (Fin 5)).subtype
      (alternatingGroup (Fin 5)).subtype_injective a b
  have hinv : ordInv (repX j) (repY j) = ordInv (repX i) (repY i) := by
    have e := ordInv_hom φ.toMonoidHom φ.injective (repXA i) (repYA i)
    simp only [MulEquiv.coe_toMonoidHom] at e
    rw [h1, h2] at e
    have := hsub (repXA j) (repYA j)
    have := hsub (repXA i) (repYA i)
    simp only [repXA, repYA] at *
    rw [‹ordInv (repX j) (repY j) = _›, ‹ordInv (repX i) (repY i) = _›]
    exact e
  have := (ordInv_nodup.getElem_inj_iff (i := i.val) (j := j.val) (hi := by simp)
    (hj := by simp)).1 (by simp only [List.getElem_ofFn, Fin.eta]; exact hinv.symm)
  exact Fin.ext this

/-- `A₅^19` is perfect at every level of the derived series. -/
theorem derivedSeries_pi_eq_top (n : ℕ) : derivedSeries (Fin 19 → A5) n = ⊤ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [derivedSeries_succ, ih, eq_top_iff]
    intro f _
    have hc : ∀ g : A5, ∃ a b : A5, ⁅a, b⁆ = g := by
      intro g
      obtain ⟨a, ha, b, hb, hab⟩ := exists_commutator_A5 g.1 g.2
      exact ⟨⟨a, ha⟩, ⟨b, hb⟩, Subtype.ext hab⟩
    choose a b hab using hc
    have : f = ⁅fun k => a (f k), fun k => b (f k)⁆ := by
      funext k; simp only [commutatorElement_def, Pi.mul_apply, Pi.inv_apply]
      have := hab (f k); rw [commutatorElement_def] at this; exact this.symm
    rw [this]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem evalPair_conj (σ a b : Perm (Fin 5)) (w : F2) :
    evalPair (σ⁻¹ * a * σ) (σ⁻¹ * b * σ) w = σ⁻¹ * evalPair a b w * σ := by
  let f : F2 →* Perm (Fin 5) := (MulAut.conj σ⁻¹).toMonoidHom.comp (evalPair a b)
  have : evalPair (σ⁻¹ * a * σ) (σ⁻¹ * b * σ) = f := by
    apply FreeGroup.ext_hom; intro i; fin_cases i <;> simp [f, evalPair]
  rw [this]; simp [f]

/-- **Cold mirrors are blind** (004c, Theorem 6.1). For every target tuple `g ∈ A₅^19` there is a
word `w ∈ F₂''` with `w(x_k, y_k) = g_k` for all 19 representatives and `w(x, y) = e` for every
pair `(x, y) ∈ A₅²` that does not generate `A₅`. -/
theorem mirror_word (g : Fin 19 → Perm (Fin 5)) (hg : ∀ k, g k ∈ alternatingGroup (Fin 5)) :
    ∃ w ∈ derivedSeries F2 2, (∀ k, evalPair (repX k) (repY k) w = g k) ∧
      ∀ x y, x ∈ alternatingGroup (Fin 5) → y ∈ alternatingGroup (Fin 5) → ¬ IsHot x y →
        evalPair x y w = 1 := by
  have hmap : (derivedSeries F2 2).map Phi = ⊤ := by
    rw [map_derivedSeries_eq hall_A5, derivedSeries_pi_eq_top]
  have : (fun k => (⟨g k, hg k⟩ : A5)) ∈ (derivedSeries F2 2).map Phi :=
    hmap ▸ Subgroup.mem_top _
  obtain ⟨w, hw, hΦ⟩ := this
  refine ⟨w, hw, fun k => ?_, fun x y hx hy hc => cold_kill hx hy hc hw⟩
  rw [← Phi_apply, hΦ]

theorem inOrbit_eval {k : Fin 19} {x y : Perm (Fin 5)} (h : InOrbit k x y) (w : F2) :
    ∃ σ : Perm (Fin 5), evalPair x y w = σ⁻¹ * evalPair (repX k) (repY k) w * σ := by
  obtain ⟨σ, hx, hy⟩ := h
  refine ⟨σ, ?_⟩
  rw [← evalPair_conj, ← hx, ← hy]
  congr 1 <;> group

/-- **Nineteen mirror selectors** (004c, Corollary 6.2): for each orbit `i` there is a word
`w_i ∈ F₂''` that is not the identity exactly on the pairs of orbit `i`. -/
theorem mirror_selectors (i : Fin 19) : ∃ w ∈ derivedSeries F2 2,
    ∀ x y, x ∈ alternatingGroup (Fin 5) → y ∈ alternatingGroup (Fin 5) →
      (evalPair x y w ≠ 1 ↔ InOrbit i x y) := by
  classical
  obtain ⟨w, hw, hval, hcold⟩ := mirror_word (fun k => if k = i then pA else 1)
    (fun k => by split_ifs; exacts [pA_mem, Subgroup.one_mem _])
  refine ⟨w, hw, fun x y hx hy => ?_⟩
  by_cases hh : IsHot x y
  · obtain ⟨k, hk⟩ := ((classification hx hy).1).1 hh
    obtain ⟨σ, hσ⟩ := inOrbit_eval hk w
    rw [hσ, hval]
    constructor
    · intro hne
      by_cases hki : k = i
      · subst hki; exact hk
      · exfalso; apply hne; simp [hki]
    · intro hi
      have := inOrbit_unique hk hi
      subst this
      simp only [if_true]
      intro h
      have : pA = 1 := by
        have := congrArg (fun z => σ * z * σ⁻¹) h; simpa [mul_assoc] using this
      exact absurd this (by decide)
  · rw [hcold x y hx hy hh]
    simp only [ne_eq, not_true_eq_false, false_iff]
    exact fun hi => hh (hot_of_inOrbit hi)

theorem evalPair_mem {x y : Perm (Fin 5)} (hx : x ∈ alternatingGroup (Fin 5))
    (hy : y ∈ alternatingGroup (Fin 5)) (w : F2) : evalPair x y w ∈ alternatingGroup (Fin 5) := by
  induction w using FreeGroup.induction_on with
  | one => exact Subgroup.one_mem _
  | of i => fin_cases i <;> simpa [evalPair]
  | inv_of i ih => rw [map_inv]; exact Subgroup.inv_mem _ ih
  | mul u v hu hv => rw [map_mul]; exact Subgroup.mul_mem _ hu hv

/-- **No interpolation from easy rows** (004c, Corollary 6.3). For every word `u`, orbit `i` and
target `h ∈ A₅` there is a word `u'` that agrees with `u` on every pair of `A₅²` outside orbit
`i` (all non-generating pairs and the other 18 orbits) and takes the value `h` on the `i`-th
representative. -/
theorem no_interpolation (u : F2) (i : Fin 19) (h : Perm (Fin 5))
    (hh : h ∈ alternatingGroup (Fin 5)) : ∃ u' : F2,
    evalPair (repX i) (repY i) u' = h ∧
    ∀ x y, x ∈ alternatingGroup (Fin 5) → y ∈ alternatingGroup (Fin 5) → ¬ InOrbit i x y →
      evalPair x y u' = evalPair x y u := by
  classical
  set c := (evalPair (repX i) (repY i) u)⁻¹ * h with hc
  have hcm : c ∈ alternatingGroup (Fin 5) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (evalPair_mem (repX_mem i) (repY_mem i) u)) hh
  obtain ⟨w, hw, hval, hcold⟩ := mirror_word (fun k => if k = i then c else 1)
    (fun k => by split_ifs; exacts [hcm, Subgroup.one_mem _])
  refine ⟨u * w, ?_, fun x y hx hy hni => ?_⟩
  · rw [map_mul, hval]; simp [hc]
  · rw [map_mul]
    by_cases hhot : IsHot x y
    · obtain ⟨k, hk⟩ := ((classification hx hy).1).1 hhot
      have hki : k ≠ i := fun e => hni (e ▸ hk)
      obtain ⟨σ, hσ⟩ := inOrbit_eval hk w
      rw [hσ, hval]; simp [hki]
    · rw [hcold x y hx hy hhot, mul_one]

end GC.A5Programs
