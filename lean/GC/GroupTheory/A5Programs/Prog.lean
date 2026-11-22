import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Induction
import Mathlib.Tactic.Common
import Mathlib.Algebra.Group.Subgroup.Defs

/-!
# Straight-line programs over a group

A program is a list of operations. Node `k` is the `k`-th operation; its operands are indices of
earlier nodes. `leaf a` reads a terminal or constant labelled `a` through a valuation
`ν : α → G`; `mul i j` is the product of nodes `i` and `j`; `inv i` is the inverse of node `i`.
Out-of-range operands read the identity (well-formed programs never do this).

Sharing is explicit: a node may be used by many later nodes, and the size of a program is its
length.
-/

namespace GC.A5Programs

/-- One node of a straight-line program over a group with leaves labelled by `α`. -/
inductive Op (α : Type) where
  | leaf : α → Op α
  | mul : ℕ → ℕ → Op α
  | inv : ℕ → Op α
  deriving DecidableEq, Repr

variable {α β : Type} {G H : Type*} [Group G] [Group H]

/-- The value of one operation, given the values of the earlier nodes. -/
def Op.step (ν : α → G) (vals : List G) : Op α → G
  | .leaf a => ν a
  | .mul i j => vals.getD i 1 * vals.getD j 1
  | .inv i => (vals.getD i 1)⁻¹

/-- The values of all nodes of a program. -/
def evalProg (ν : α → G) (ops : List (Op α)) : List G :=
  ops.foldl (fun vals op => vals ++ [op.step ν vals]) []

/-- The value of node `k`. -/
def val (ν : α → G) (ops : List (Op α)) (k : ℕ) : G := (evalProg ν ops).getD k 1

/-- A program is well formed if every operand is an earlier node. -/
def Op.WF (k : ℕ) : Op α → Prop
  | .leaf _ => True
  | .mul i j => i < k ∧ j < k
  | .inv i => i < k

/-- Every operand of node `k` refers to an earlier node. -/
def WellFormed (ops : List (Op α)) : Prop :=
  ∀ k (h : k < ops.length), (ops[k]'h).WF k

@[simp] theorem evalProg_nil (ν : α → G) : evalProg ν ([] : List (Op α)) = [] := rfl

theorem evalProg_append_single (ν : α → G) (ops : List (Op α)) (op : Op α) :
    evalProg ν (ops ++ [op]) = evalProg ν ops ++ [op.step ν (evalProg ν ops)] := by
  simp [evalProg, List.foldl_append]

@[simp] theorem length_evalProg (ν : α → G) (ops : List (Op α)) :
    (evalProg ν ops).length = ops.length := by
  induction ops using List.reverseRecOn with
  | nil => rfl
  | append_singleton ops op ih => simp [evalProg_append_single, ih]

theorem evalProg_append (ν : α → G) (ops more : List (Op α)) :
    ∃ l, evalProg ν (ops ++ more) = evalProg ν ops ++ l := by
  induction more using List.reverseRecOn with
  | nil => exact ⟨[], by simp⟩
  | append_singleton more op ih =>
    obtain ⟨l, hl⟩ := ih
    refine ⟨l ++ [op.step ν (evalProg ν (ops ++ more))], ?_⟩
    rw [← List.append_assoc, evalProg_append_single, hl, List.append_assoc]

/-- Appending nodes does not change the values of earlier nodes. -/
theorem val_append_of_lt (ν : α → G) (ops more : List (Op α)) {k : ℕ} (hk : k < ops.length) :
    val ν (ops ++ more) k = val ν ops k := by
  obtain ⟨l, hl⟩ := evalProg_append ν ops more
  unfold val
  rw [hl, List.getD_append _ _ _ _ (by simpa using hk)]

theorem val_append_single_self (ν : α → G) (ops : List (Op α)) (op : Op α) :
    val ν (ops ++ [op]) ops.length = op.step ν (evalProg ν ops) := by
  unfold val
  rw [evalProg_append_single, List.getD_append_right _ _ _ _ (by simp)]
  simp

theorem val_append_single_of_eq (ν : α → G) (ops : List (Op α)) (op : Op α) {n : ℕ}
    (h : n = ops.length) : val ν (ops ++ [op]) n = op.step ν (evalProg ν ops) := by
  subst h; exact val_append_single_self ν ops op

/-- The value of a new node in terms of the values of earlier nodes. -/
theorem step_eq (ν : α → G) (ops : List (Op α)) (op : Op α) :
    op.step ν (evalProg ν ops) =
      match op with
      | .leaf a => ν a
      | .mul i j => val ν ops i * val ν ops j
      | .inv i => (val ν ops i)⁻¹ := by
  cases op <;> rfl

@[simp] theorem val_snoc_leaf (ν : α → G) (ops : List (Op α)) (a : α) :
    val ν (ops ++ [.leaf a]) ops.length = ν a := by
  rw [val_append_single_self]; rfl

@[simp] theorem val_snoc_mul (ν : α → G) (ops : List (Op α)) (i j : ℕ) :
    val ν (ops ++ [.mul i j]) ops.length = val ν ops i * val ν ops j := by
  rw [val_append_single_self]; rfl

@[simp] theorem val_snoc_inv (ν : α → G) (ops : List (Op α)) (i : ℕ) :
    val ν (ops ++ [.inv i]) ops.length = (val ν ops i)⁻¹ := by
  rw [val_append_single_self]; rfl

/-- Values of a program on the last node of a nonempty prefix. -/
theorem val_of_lt (ν : α → G) (ops : List (Op α)) {k : ℕ} (hk : k < ops.length) :
    val ν ops k = (ops[k]'hk).step ν (evalProg ν (ops.take k)) := by
  have h : ops = ops.take k ++ [ops[k]'hk] ++ ops.drop (k + 1) := by
    simp
  conv_lhs => rw [h]
  rw [val_append_of_lt _ _ _ (by simp; omega)]
  exact val_append_single_of_eq ν _ _ (by simp; omega)

/-- Evaluation commutes with group homomorphisms. -/
theorem map_evalProg (f : G →* H) (ν : α → G) (ops : List (Op α)) :
    (evalProg ν ops).map f = evalProg (f ∘ ν) ops := by
  induction ops using List.reverseRecOn with
  | nil => rfl
  | append_singleton ops op ih =>
    rw [evalProg_append_single, evalProg_append_single, List.map_append, ih, ← ih]
    cases op with
    | leaf a => rfl
    | mul i j =>
      simp only [Op.step, List.map_cons, List.map_nil, map_mul]
      rw [← List.getD_map _ _ f, ← List.getD_map _ _ f, map_one]
    | inv i =>
      simp only [Op.step, List.map_cons, List.map_nil, map_inv]
      rw [← List.getD_map _ _ f, map_one]

theorem map_val (f : G →* H) (ν : α → G) (ops : List (Op α)) (k : ℕ) :
    f (val ν ops k) = val (f ∘ ν) ops k := by
  unfold val
  rw [← map_evalProg, ← List.getD_map _ _ f, map_one]

/-- Changing leaf labels. -/
def Op.mapLeaf (g : α → β) : Op α → Op β
  | .leaf a => .leaf (g a)
  | .mul i j => .mul i j
  | .inv i => .inv i

theorem evalProg_mapLeaf (g : α → β) (ν : β → G) (ops : List (Op α)) :
    evalProg ν (ops.map (Op.mapLeaf g)) = evalProg (ν ∘ g) ops := by
  induction ops using List.reverseRecOn with
  | nil => rfl
  | append_singleton ops op ih =>
    simp only [List.map_append, List.map_cons, List.map_nil]
    rw [evalProg_append_single, evalProg_append_single, ih]
    cases op <;> rfl

end GC.A5Programs

namespace GC.A5Programs

variable {α : Type} {G : Type*} [Group G]

/-- Value of a node of a program extended by one operation. -/
theorem val_snoc (ν : α → G) (ops : List (Op α)) (op : Op α) (k : ℕ) :
    val ν (ops ++ [op]) k =
      if k < ops.length then val ν ops k
      else if k = ops.length then
        (match op with
          | .leaf a => ν a
          | .mul i j => val ν ops i * val ν ops j
          | .inv i => (val ν ops i)⁻¹)
      else 1 := by
  split_ifs with h1 h2
  · exact val_append_of_lt ν ops [op] h1
  · subst h2; rw [val_append_single_self]; cases op <;> rfl
  · unfold val
    rw [List.getD_eq_default]
    simp; omega

theorem val_snoc_lt (ν : α → G) (ops : List (Op α)) (op : Op α) {k : ℕ}
    (h : k < ops.length) : val ν (ops ++ [op]) k = val ν ops k :=
  val_append_of_lt ν ops [op] h

theorem val_snoc_leaf_eq (ν : α → G) (ops : List (Op α)) (a : α) {k : ℕ}
    (h : k = ops.length) : val ν (ops ++ [.leaf a]) k = ν a := by
  subst h; simp

theorem val_snoc_mul_eq (ν : α → G) (ops : List (Op α)) (i j : ℕ) {k : ℕ}
    (h : k = ops.length) : val ν (ops ++ [.mul i j]) k = val ν ops i * val ν ops j := by
  subst h; simp

theorem val_snoc_inv_eq (ν : α → G) (ops : List (Op α)) (i : ℕ) {k : ℕ}
    (h : k = ops.length) : val ν (ops ++ [.inv i]) k = (val ν ops i)⁻¹ := by
  subst h; simp

@[simp] theorem wellFormed_nil : WellFormed ([] : List (Op α)) := fun k h => by simp at h

theorem wellFormed_append_single (ops : List (Op α)) (op : Op α) :
    WellFormed (ops ++ [op]) ↔ WellFormed ops ∧ op.WF ops.length := by
  constructor
  · intro h
    refine ⟨fun k hk => ?_, ?_⟩
    · have := h k (by simp; omega)
      rwa [List.getElem_append_left hk] at this
    · have := h ops.length (by simp)
      simpa using this
  · rintro ⟨h1, h2⟩ k hk
    simp at hk
    rcases Nat.lt_or_ge k ops.length with hk' | hk'
    · rw [List.getElem_append_left hk']; exact h1 k hk'
    · have : k = ops.length := by omega
      subst this; simpa using h2

end GC.A5Programs

namespace GC.A5Programs

variable {α : Type} {G : Type*} [Group G]

/-- Reading a node from inside an appended block: nodes below `L` come from `outer`. -/
def blockLook (outer : ℕ → G) (L : ℕ) (loc : List G) (r : ℕ) : G :=
  if r < L then outer r else loc.getD (r - L) 1

/-- One operation inside an appended block. -/
def blockStep (ν : α → G) (outer : ℕ → G) (L : ℕ) (loc : List G) : Op α → G
  | .leaf a => ν a
  | .mul i j => blockLook outer L loc i * blockLook outer L loc j
  | .inv i => (blockLook outer L loc i)⁻¹

/-- Values of a block appended after `L` nodes whose values are `outer`. -/
def evalBlock (ν : α → G) (outer : ℕ → G) (L : ℕ) (blk : List (Op α)) : List G :=
  blk.foldl (fun loc op => loc ++ [blockStep ν outer L loc op]) []

theorem evalBlock_append_single (ν : α → G) (outer : ℕ → G) (L : ℕ) (blk : List (Op α))
    (op : Op α) : evalBlock ν outer L (blk ++ [op]) =
      evalBlock ν outer L blk ++ [blockStep ν outer L (evalBlock ν outer L blk) op] := by
  simp [evalBlock, List.foldl_append]

theorem evalProg_append_block (ν : α → G) (ops blk : List (Op α)) :
    evalProg ν (ops ++ blk) = evalProg ν ops ++ evalBlock ν (val ν ops) ops.length blk := by
  induction blk using List.reverseRecOn with
  | nil => simp [evalBlock]
  | append_singleton blk op ih =>
    rw [← List.append_assoc, evalProg_append_single, ih, evalBlock_append_single,
      List.append_assoc]
    simp only [List.append_cancel_left_eq, List.cons.injEq, and_true]
    have hlook : ∀ r, (evalProg ν ops ++ evalBlock ν (val ν ops) ops.length blk).getD r 1 =
        blockLook (val ν ops) ops.length (evalBlock ν (val ν ops) ops.length blk) r := by
      intro r
      unfold blockLook
      split_ifs with h
      · rw [List.getD_append _ _ _ _ (by simpa using h)]; rfl
      · rw [List.getD_append_right _ _ _ _ (by simp; omega)]; simp
    cases op with
    | leaf a => rfl
    | mul i j => show _ * _ = _ * _; rw [hlook, hlook]
    | inv i => show (_)⁻¹ = (_)⁻¹; rw [hlook]

theorem val_append_block (ν : α → G) (ops blk : List (Op α)) (n : ℕ) :
    val ν (ops ++ blk) (ops.length + n) =
      (evalBlock ν (val ν ops) ops.length blk).getD n 1 := by
  unfold val
  rw [evalProg_append_block, List.getD_append_right _ _ _ _ (by simp), length_evalProg,
    Nat.add_sub_cancel_left]
  rfl

end GC.A5Programs

namespace GC.A5Programs

variable {α : Type} {G : Type*} [Group G]

theorem val_of_ge (ν : α → G) (ops : List (Op α)) {k : ℕ} (hk : ops.length ≤ k) :
    val ν ops k = 1 := by
  unfold val; rw [List.getD_eq_default]; simpa using hk

instance (k : ℕ) (op : Op α) : Decidable (op.WF k) := by
  cases op <;> unfold Op.WF <;> infer_instance

end GC.A5Programs

namespace GC.A5Programs

variable {α : Type} {G : Type*} [Group G]

/-- If every leaf value lies in a subgroup, every node value does. -/
theorem val_mem_of_leaves (H : Subgroup G) (ν : α → G) (ops : List (Op α))
    (h : ∀ a, Op.leaf a ∈ ops → ν a ∈ H) (k : ℕ) : val ν ops k ∈ H := by
  induction ops using List.reverseRecOn generalizing k with
  | nil => simp [val, H.one_mem]
  | append_singleton ops op ih =>
    have ih' := ih (fun a ha => h a (List.mem_append_left _ ha))
    rw [val_snoc]
    split_ifs
    · exact ih' k
    · cases op with
      | leaf a => exact h a (by simp)
      | mul i j => exact H.mul_mem (ih' i) (ih' j)
      | inv i => exact H.inv_mem (ih' i)
    · exact H.one_mem

/-- Values depend only on the valuation of the leaves that occur. -/
theorem val_congr_leaves (ν ν' : α → G) (ops : List (Op α))
    (h : ∀ a, Op.leaf a ∈ ops → ν a = ν' a) (k : ℕ) : val ν ops k = val ν' ops k := by
  induction ops using List.reverseRecOn generalizing k with
  | nil => simp [val]
  | append_singleton ops op ih =>
    have ih' := ih (fun a ha => h a (List.mem_append_left _ ha))
    rw [val_snoc, val_snoc]
    split_ifs
    · exact ih' k
    · cases op with
      | leaf a => exact h a (by simp)
      | mul i j => simp only [ih']
      | inv i => simp only [ih']
    · rfl

end GC.A5Programs
