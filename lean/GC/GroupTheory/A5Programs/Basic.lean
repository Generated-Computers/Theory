import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.Perm.Fin

/-!
# Straight-line programs over `A₅`: shared definitions

Permutations of five points are written `Equiv.Perm (Fin 5)` and act on `{0,…,4}`; the paper's
point `i ∈ {1,…,5}` is `i - 1` here. Products compose right to left, `(σ * τ) i = σ (τ i)`, as in
the papers. A concrete permutation is given by the vector of its values and the vector of the
values of its inverse (`mk5`), so that all finite checks are decided by the kernel.

* `A5list`: an explicit list of the 60 elements of `alternatingGroup (Fin 5)`;
  `mem_A5list_iff` shows that it is exactly the alternating group.
* `Op`, `evalProg`, `val`: straight-line programs (circuits with sharing) over a group, given as
  lists of operations whose operands are indices of earlier nodes.
-/

namespace GC.A5Programs

open Equiv

/-- A permutation of `Fin 5` from the vector of its values and the vector of its inverse. -/
def mk5 (f g : Fin 5 → Fin 5) (h1 : ∀ i, g (f i) = i := by decide)
    (h2 : ∀ i, f (g i) = i := by decide) : Perm (Fin 5) := ⟨f, g, h1, h2⟩

/-- `p = (1 2 3 4 5)` (paper notation), i.e. `0 ↦ 1 ↦ 2 ↦ 3 ↦ 4 ↦ 0`. -/
def pA : Perm (Fin 5) := mk5 ![1,2,3,4,0] ![4,0,1,2,3]
/-- `q = (1 2 3)`. -/
def qA : Perm (Fin 5) := mk5 ![1,2,0,3,4] ![2,0,1,3,4]

/-- The 60 elements of `A₅`, in breadth-first order from `p, q, p⁻¹, q⁻¹, e`. -/
def A5list : List (Perm (Fin 5)) :=
  [mk5 ![1,2,3,4,0] ![4,0,1,2,3],
   mk5 ![1,2,0,3,4] ![2,0,1,3,4],
   mk5 ![4,0,1,2,3] ![1,2,3,4,0],
   mk5 ![2,0,1,3,4] ![1,2,0,3,4],
   mk5 ![0,1,2,3,4] ![0,1,2,3,4],
   mk5 ![2,3,4,0,1] ![3,4,0,1,2],
   mk5 ![2,3,1,4,0] ![4,2,0,1,3],
   mk5 ![3,1,2,4,0] ![4,1,2,0,3],
   mk5 ![2,0,3,4,1] ![1,4,0,2,3],
   mk5 ![4,1,2,0,3] ![3,1,2,4,0],
   mk5 ![0,1,4,2,3] ![0,1,3,4,2],
   mk5 ![3,4,0,1,2] ![2,3,4,0,1],
   mk5 ![1,4,0,2,3] ![2,0,3,4,1],
   mk5 ![0,1,3,4,2] ![0,1,4,2,3],
   mk5 ![4,2,0,1,3] ![2,3,1,4,0],
   mk5 ![3,4,2,0,1] ![3,4,2,0,1],
   mk5 ![4,2,3,0,1] ![3,4,1,2,0],
   mk5 ![3,1,4,0,2] ![3,1,4,0,2],
   mk5 ![0,2,3,1,4] ![0,3,1,2,4],
   mk5 ![1,2,4,0,3] ![3,0,1,4,2],
   mk5 ![0,3,1,2,4] ![0,2,3,1,4],
   mk5 ![0,3,4,1,2] ![0,3,4,1,2],
   mk5 ![0,3,2,4,1] ![0,4,2,1,3],
   mk5 ![3,2,0,4,1] ![2,4,1,0,3],
   mk5 ![3,4,1,2,0] ![4,2,3,0,1],
   mk5 ![2,4,1,0,3] ![3,2,0,4,1],
   mk5 ![1,4,2,3,0] ![4,0,2,3,1],
   mk5 ![3,0,1,4,2] ![1,2,4,0,3],
   mk5 ![4,0,3,1,2] ![1,3,4,2,0],
   mk5 ![4,0,2,3,1] ![1,4,2,3,0],
   mk5 ![1,3,4,2,0] ![4,0,3,1,2],
   mk5 ![1,3,0,4,2] ![2,0,4,1,3],
   mk5 ![2,0,4,1,3] ![1,3,0,4,2],
   mk5 ![0,4,2,1,3] ![0,3,2,4,1],
   mk5 ![2,3,0,1,4] ![2,3,0,1,4],
   mk5 ![1,4,3,0,2] ![3,0,4,2,1],
   mk5 ![4,3,1,0,2] ![3,2,4,1,0],
   mk5 ![3,0,2,1,4] ![1,3,2,0,4],
   mk5 ![2,4,0,3,1] ![2,4,0,3,1],
   mk5 ![3,1,0,2,4] ![2,1,3,0,4],
   mk5 ![1,0,3,2,4] ![1,0,3,2,4],
   mk5 ![3,2,4,1,0] ![4,3,1,0,2],
   mk5 ![1,3,2,0,4] ![3,0,2,1,4],
   mk5 ![4,1,3,2,0] ![4,1,3,2,0],
   mk5 ![4,1,0,3,2] ![2,1,4,3,0],
   mk5 ![4,2,1,3,0] ![4,2,1,3,0],
   mk5 ![2,1,4,3,0] ![4,1,0,3,2],
   mk5 ![0,2,4,3,1] ![0,4,1,3,2],
   mk5 ![3,0,4,2,1] ![1,4,3,0,2],
   mk5 ![2,1,3,0,4] ![3,1,0,2,4],
   mk5 ![0,4,1,3,2] ![0,2,4,3,1],
   mk5 ![4,3,0,2,1] ![2,4,3,1,0],
   mk5 ![2,4,3,1,0] ![4,3,0,2,1],
   mk5 ![0,2,1,4,3] ![0,2,1,4,3],
   mk5 ![1,0,2,4,3] ![1,0,2,4,3],
   mk5 ![4,3,2,1,0] ![4,3,2,1,0],
   mk5 ![3,2,1,0,4] ![3,2,1,0,4],
   mk5 ![1,0,4,3,2] ![1,0,4,3,2],
   mk5 ![0,4,3,2,1] ![0,4,3,2,1],
   mk5 ![2,1,0,4,3] ![2,1,0,4,3]]

set_option maxRecDepth 100000 in
theorem A5list_length : A5list.length = 60 := by decide

set_option maxRecDepth 100000 in
theorem A5list_nodup : A5list.Nodup := by decide

set_option maxRecDepth 100000 in
theorem A5list_sign : ∀ g ∈ A5list, Perm.sign g = 1 := by decide

theorem A5list_mem_alternating : ∀ g ∈ A5list, g ∈ alternatingGroup (Fin 5) :=
  fun g hg => (Perm.mem_alternatingGroup).2 (A5list_sign g hg)

theorem card_alternatingGroup_five : Fintype.card (alternatingGroup (Fin 5)) = 60 := by
  rw [card_alternatingGroup]; rfl

/-- The explicit list is exactly the alternating group. -/
theorem mem_A5list_iff (g : Perm (Fin 5)) : g ∈ A5list ↔ g ∈ alternatingGroup (Fin 5) := by
  classical
  constructor
  · exact A5list_mem_alternating g
  · intro hg
    by_contra hn
    have hsub : A5list.toFinset ⊆ (alternatingGroup (Fin 5) : Set (Perm (Fin 5))).toFinset := by
      intro x hx
      simpa using A5list_mem_alternating x (List.mem_toFinset.1 hx)
    have hcard : (alternatingGroup (Fin 5) : Set (Perm (Fin 5))).toFinset.card = 60 := by
      rw [Set.toFinset_card]
      simpa using card_alternatingGroup_five
    have h1 : A5list.toFinset.card = 60 := by
      rw [List.toFinset_card_of_nodup A5list_nodup, A5list_length]
    have hlt : A5list.toFinset ⊂ (alternatingGroup (Fin 5) : Set (Perm (Fin 5))).toFinset := by
      refine ⟨hsub, fun h => hn ?_⟩
      have := h (by simpa using hg)
      simpa using this
    have := Finset.card_lt_card hlt
    omega

/-- Checking a property on the explicit list checks it on `A₅`. -/
theorem forall_A5 {P : Perm (Fin 5) → Prop} (h : ∀ g ∈ A5list, P g) :
    ∀ g ∈ alternatingGroup (Fin 5), P g :=
  fun g hg => h g ((mem_A5list_iff g).2 hg)

/-! ## Fast equality of permutations -/

/-- Pointwise comparison of two permutations of `Fin 5`. -/
def peq (σ τ : Perm (Fin 5)) : Bool :=
  σ 0 == τ 0 && σ 1 == τ 1 && σ 2 == τ 2 && σ 3 == τ 3 && σ 4 == τ 4

theorem peq_iff {σ τ : Perm (Fin 5)} : peq σ τ = true ↔ σ = τ := by
  constructor
  · intro h
    simp only [peq, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := h
    ext i; fin_cases i <;> simp [h0, h1, h2, h3, h4]
  · rintro rfl; simp [peq]

/-- List membership through `peq`. -/
def pmem (σ : Perm (Fin 5)) (l : List (Perm (Fin 5))) : Bool := l.any (peq σ)

theorem pmem_iff {σ : Perm (Fin 5)} {l : List (Perm (Fin 5))} : pmem σ l = true ↔ σ ∈ l := by
  simp only [pmem, List.any_eq_true, peq_iff]
  exact ⟨fun ⟨a, ha, h⟩ => h ▸ ha, fun h => ⟨σ, h, rfl⟩⟩

end GC.A5Programs
