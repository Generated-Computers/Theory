import GC.GroupTheory.A5Programs.Gadgets
import Mathlib.GroupTheory.FreeGroup.Basic

/-!
# The two-generator normal form

A shared library of 60 nodes over the terminals `P, Q` (values `p = (1 2 3 4 5)`,
`q = (1 2 3)`) computes every element of `A₅` (each by a word of length at most 6). Redirecting
every constant of an `A₅` circuit to the library gives a constant-free two-generator program of
size `s + 60` in which every node of the circuit has a copy with the same value
(004b, Theorem 3.1; 004a, Lemma 2.1).
-/

namespace GC.A5Programs

open Equiv

/-- Terminal values: `P ↦ p`, `Q ↦ q`. -/
def pq : Fin 2 → Perm (Fin 5) := ![pA, qA]

/-- The library: `P, Q, P⁻¹, Q⁻¹, P P⁻¹`, then one product per remaining element along a
breadth-first tree of the Cayley graph. -/
def libOps : List (Op (Fin 2)) :=
  [Op.leaf 0, Op.leaf 1, Op.inv 0, Op.inv 1, Op.mul 0 2, Op.mul 0 0, Op.mul 0 1, Op.mul 0 3, Op.mul 1 0, Op.mul 1 2, Op.mul 2 1, Op.mul 2 2, Op.mul 2 3, Op.mul 3 0, Op.mul 3 2, Op.mul 5 1, Op.mul 5 3, Op.mul 6 0, Op.mul 6 2, Op.mul 7 0, Op.mul 7 2, Op.mul 8 0, Op.mul 8 1, Op.mul 8 3, Op.mul 9 2, Op.mul 9 3, Op.mul 10 0, Op.mul 10 2, Op.mul 11 1, Op.mul 12 0, Op.mul 13 0, Op.mul 13 1, Op.mul 14 1, Op.mul 14 3, Op.mul 16 0, Op.mul 17 1, Op.mul 17 3, Op.mul 18 3, Op.mul 19 0, Op.mul 20 1, Op.mul 20 3, Op.mul 22 0, Op.mul 23 2, Op.mul 24 1, Op.mul 25 0, Op.mul 26 1, Op.mul 26 3, Op.mul 29 1, Op.mul 31 0, Op.mul 31 2, Op.mul 32 0, Op.mul 35 0, Op.mul 36 2, Op.mul 37 0, Op.mul 39 0, Op.mul 41 3, Op.mul 42 1, Op.mul 44 1, Op.mul 48 1, Op.mul 53 1]

theorem libOps_length : libOps.length = 60 := rfl

set_option maxRecDepth 100000 in
/-- The library computes exactly the list `A5list`, node by node. -/
theorem evalProg_libOps : evalProg pq libOps = A5list := by decide +kernel

theorem libOps_wellFormed : WellFormed libOps := by
  unfold WellFormed; decide

/-- Index of an element in the library (`4` is the identity node). -/
def libIdx (g : Perm (Fin 5)) : ℕ := A5list.idxOf g

theorem val_libOps_libIdx {g : Perm (Fin 5)} (hg : g ∈ alternatingGroup (Fin 5)) :
    val pq libOps (libIdx g) = g := by
  have hm := (mem_A5list_iff g).2 hg
  unfold val libIdx
  rw [evalProg_libOps, List.getD_eq_getElem _ _ (List.idxOf_lt_length_of_mem hm)]
  exact List.getElem_idxOf _

theorem libIdx_lt {g : Perm (Fin 5)} (hg : g ∈ alternatingGroup (Fin 5)) : libIdx g < 60 := by
  have := List.idxOf_lt_length_of_mem ((mem_A5list_iff g).2 hg)
  rwa [A5list_length] at this

theorem val_libOps_four : val pq libOps 4 = 1 := by
  unfold val; rw [evalProg_libOps]; decide

/-- Redirect one operation of an `A₅` circuit into the two-generator program: a constant `g`
becomes the copy `lib(g) · lib(e)`; other gates are shifted by 60. -/
def redirect : Op (Perm (Fin 5)) → Op (Fin 2)
  | .leaf g => .mul (libIdx g) 4
  | .mul i j => .mul (60 + i) (60 + j)
  | .inv i => .inv (60 + i)

/-- The two-generator normal form of an `A₅` circuit. -/
def normalForm (C : List (Op (Perm (Fin 5)))) : List (Op (Fin 2)) := libOps ++ C.map redirect

/-- The constants of a circuit lie in `A₅`. -/
def ConstsInA5 (C : List (Op (Perm (Fin 5)))) : Prop :=
  ∀ g, Op.leaf g ∈ C → g ∈ alternatingGroup (Fin 5)

/-- **Two-generator normal form** (004b, Theorem 3.1). For every `A₅` circuit `C` of size `s`
with constants in `A₅`, `normalForm C` is a constant-free program over the two terminals
`P, Q` of size `s + 60`, and node `60 + k` has the value of node `k` of `C`. Gate
sharing is preserved (gates are copied one for one) and well-formedness is preserved. -/
theorem normalForm_spec (C : List (Op (Perm (Fin 5)))) (hC : ConstsInA5 C) :
    (normalForm C).length = C.length + 60 ∧
    (WellFormed C → WellFormed (normalForm C)) ∧
    ∀ k < C.length, val pq (normalForm C) (60 + k) = val id C k := by
  refine ⟨by simp [normalForm, libOps_length]; omega, ?_, ?_⟩
  · induction C using List.reverseRecOn with
    | nil => intro _; simpa [normalForm] using libOps_wellFormed
    | append_singleton C op ih =>
      intro hwf
      rw [wellFormed_append_single] at hwf
      have hC' : ConstsInA5 C := fun g hg => hC g (List.mem_append_left _ hg)
      have h1 := ih hC' hwf.1
      simp only [normalForm, List.map_append, List.map_cons, List.map_nil,
        ← List.append_assoc] at h1 ⊢
      rw [wellFormed_append_single]
      refine ⟨h1, ?_⟩
      simp only [List.length_append, List.length_map, libOps_length]
      have h2 := hwf.2
      cases op with
      | leaf g =>
        have := libIdx_lt (hC g (by simp))
        simp only [redirect, Op.WF]; omega
      | mul i j => simp only [redirect, Op.WF] at h2 ⊢; omega
      | inv i => simp only [redirect, Op.WF] at h2 ⊢; omega
  · induction C using List.reverseRecOn with
    | nil => intro k hk; simp at hk
    | append_singleton C op ih =>
      have hC' : ConstsInA5 C := fun g hg => hC g (List.mem_append_left _ hg)
      intro k hk
      simp only [List.length_append, List.length_singleton] at hk
      have hNF : normalForm (C ++ [op]) = normalForm C ++ [redirect op] := by
        simp [normalForm]
      have hlen : (normalForm C).length = 60 + C.length := by
        simp [normalForm, libOps_length]
      rw [hNF]
      rcases Nat.lt_or_ge k C.length with hk' | hk'
      · rw [val_snoc_lt _ _ _ (by omega), val_snoc_lt _ _ _ hk']
        exact ih hC' k hk'
      · have hk2 : k = C.length := by omega
        subst hk2
        rw [val_snoc, if_neg (by omega), if_pos hlen.symm, val_snoc, if_neg (lt_irrefl _),
          if_pos rfl]
        have hlib : ∀ n < 60, val pq (normalForm C) n = val pq libOps n := fun n hn =>
          val_append_of_lt _ _ _ (by rw [libOps_length]; exact hn)
        have hcopy : ∀ i, val pq (normalForm C) (60 + i) = val id C i := by
          intro i
          by_cases hi : i < C.length
          · exact ih hC' i hi
          · rw [val_of_ge _ _ (by omega), val_of_ge _ _ (by omega)]
        cases op with
        | leaf g =>
          have hg := hC g (by simp)
          simp only [redirect, id]
          rw [hlib _ (libIdx_lt hg), hlib 4 (by norm_num), val_libOps_libIdx hg,
            val_libOps_four, mul_one]
        | mul i j =>
          simp only [redirect]
          rw [hcopy, hcopy]
        | inv i =>
          simp only [redirect]
          rw [hcopy]

end GC.A5Programs

namespace GC.A5Programs

open Equiv

theorem IsMulCircuit.constsInA5 {C : List (Op (Perm (Fin 5)))} (h : IsMulCircuit C) :
    ConstsInA5 C := fun g hg => h _ hg

/-- **Boolean circuits to constant-free two-generator programs** (004a, Lemma 2.2; 004d,
Theorem 6.1(ii)). Every well-formed Boolean circuit of size `s` becomes a well-formed
program over the two terminals `P ↦ p`, `Q ↦ q` of size at most `17 s + 60`, without constants,
in which the copy of every Boolean node evaluates to the encoding (`e` or `a`) of its value. -/
theorem boolean_to_twoGen (bs : List BOp) (hwf : BWellFormed bs) :
    WellFormed (normalForm (compile bs).1) ∧
    (normalForm (compile bs).1).length ≤ 17 * bs.length + 60 ∧
    ∀ k < bs.length,
      val pq (normalForm (compile bs).1) (60 + (compile bs).2.getD k 0) = enc (bval bs k) := by
  obtain ⟨hlen, hval, hsize, hmul, hwfC⟩ := compile_spec bs hwf
  obtain ⟨h1, h2, h3⟩ := normalForm_spec _ hmul.constsInA5
  refine ⟨h2 hwfC, by omega, fun k hk => ?_⟩
  rw [h3 _ (hval k hk).1]
  exact (hval k hk).2

end GC.A5Programs
