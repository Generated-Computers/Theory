import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Shared definitions for result family 003 (network flows and linear programs)

* `netOut` : the net outflow `∂f` of an arc vector at a vertex of a finite directed multigraph;
* `Conformal` : a vector that is a "part" of another one, arc by arc, with the same sign;
* `exists_conformal_path` : the flow-exchange path lemma. If `∂h(i) > 0` then there is a vector
  `χ`, conformal to `h`, whose net outflow is `e_i - e_k` for a vertex `k` with `∂h(k) < 0`.
  This is the walk argument of the proof of the boundary exchange theorem of manuscript 003a.
-/

namespace GC.FlowCircuits

open Finset

variable {V A : Type*} [Fintype A] [DecidableEq V]

/-- Incidence coefficient of arc `a` at vertex `v`: `+1` at the tail, `-1` at the head
(`0` for a loop). -/
def inc (tail head : A → V) (a : A) (v : V) : ℤ :=
  (if tail a = v then 1 else 0) - (if head a = v then 1 else 0)

/-- Net outflow `(∂h)(v) = ∑_{a ∈ δ⁺(v)} h_a - ∑_{a ∈ δ⁻(v)} h_a`. -/
def netOut (tail head : A → V) (h : A → ℤ) (v : V) : ℤ :=
  ∑ a, h a * inc tail head a v

/-- `χ` is conformal to `h`: on every arc, `χ_a` lies between `0` and `h_a`. -/
def Conformal (χ h : A → ℤ) : Prop :=
  ∀ a, (0 ≤ χ a ∧ χ a ≤ h a) ∨ (h a ≤ χ a ∧ χ a ≤ 0)

section lemmas

variable (tail head : A → V)

lemma netOut_add (h k : A → ℤ) (v : V) :
    netOut tail head (h + k) v = netOut tail head h v + netOut tail head k v := by
  simp [netOut, add_mul, sum_add_distrib]

lemma netOut_sub (h k : A → ℤ) (v : V) :
    netOut tail head (h - k) v = netOut tail head h v - netOut tail head k v := by
  simp [netOut, sub_mul, sum_sub_distrib]

lemma netOut_single [DecidableEq A] (a : A) (s : ℤ) (v : V) :
    netOut tail head (Pi.single a s) v = s * inc tail head a v := by
  unfold netOut
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb; simp [Pi.single_apply, hb]
  · simp

/-- The total mass `∑ |h_a|`, used as the induction measure. -/
def mass (h : A → ℤ) : ℕ := ∑ a, (h a).natAbs

lemma mass_sub_single [DecidableEq A] (h : A → ℤ) (a : A) (s : ℤ)
    (hs : s = 1 ∨ s = -1) (hpos : 0 < s * h a) :
    mass (h - Pi.single a s) + 1 = mass h := by
  unfold mass
  rw [← Finset.add_sum_erase _ _ (mem_univ a), ← Finset.add_sum_erase _ _ (mem_univ a)]
  have hrest : ∑ x ∈ univ.erase a, (((h - Pi.single a s : A → ℤ)) x).natAbs
      = ∑ x ∈ univ.erase a, (h x).natAbs := by
    apply sum_congr rfl
    intro x hx
    have : x ≠ a := ne_of_mem_erase hx
    simp [Pi.single_apply, this]
  rw [hrest]
  simp only [Pi.sub_apply, Pi.single_eq_same]
  rcases hs with rfl | rfl <;> omega

/-- If `∂h(i) > 0`, some arc leaves `i` in the residual sense: a non-loop arc with tail `i`
and `h_a > 0`, or a non-loop arc with head `i` and `h_a < 0`. We record it as a signed unit
step `s • e_a` with `∂(s • e_a) = e_i - e_v`. -/
lemma exists_step [DecidableEq A] (h : A → ℤ) (i : V) (hi : 0 < netOut tail head h i) :
    ∃ a s v, (s = 1 ∨ s = -1) ∧ v ≠ i ∧ 0 < s * h a ∧
      ∀ w, netOut tail head (Pi.single a s) w =
        (if w = i then 1 else 0) - (if w = v then 1 else 0) := by
  by_contra hcon
  push_neg at hcon
  have hle : ∀ a, h a * inc tail head a i ≤ 0 := by
    intro a
    unfold inc
    by_cases ht : tail a = i <;> by_cases hh : head a = i
    · simp [ht, hh]
    · -- tail = i, head ≠ i : step `+e_a` towards `head a`
      simp only [ht, hh, if_true, if_false, sub_zero, mul_one]
      by_contra hpos
      push_neg at hpos
      obtain ⟨w, hw⟩ := hcon a 1 (head a) (Or.inl rfl) hh (by simpa using hpos)
      apply hw
      rw [netOut_single]
      unfold inc
      by_cases h1 : tail a = w <;> by_cases h2 : head a = w <;>
        simp_all [eq_comm]
    · -- head = i, tail ≠ i : step `-e_a` towards `tail a`
      simp only [ht, hh, if_true, if_false, zero_sub, mul_neg, mul_one, neg_nonpos]
      by_contra hneg
      push_neg at hneg
      obtain ⟨w, hw⟩ := hcon a (-1) (tail a) (Or.inr rfl) ht (by linarith)
      apply hw
      rw [netOut_single]
      unfold inc
      by_cases h1 : tail a = w <;> by_cases h2 : head a = w <;>
        simp_all [eq_comm]
    · simp [ht, hh]
  have : netOut tail head h i ≤ 0 := Finset.sum_nonpos (fun a _ => hle a)
  omega

/-- **Path extraction.** If `∂h(i) > 0`, there is `χ` conformal to `h` with
`∂χ = e_i - e_k` for some vertex `k` with `∂h(k) < 0`. -/
theorem exists_conformal_path [DecidableEq A] :
    ∀ (h : A → ℤ) (i : V), 0 < netOut tail head h i →
      ∃ (χ : A → ℤ) (k : V), Conformal χ h ∧ netOut tail head h k < 0 ∧
        ∀ w, netOut tail head χ w = (if w = i then 1 else 0) - (if w = k then 1 else 0) := by
  intro h
  induction hm : mass h using Nat.strong_induction_on generalizing h with
  | _ m ih =>
  intro i hi
  obtain ⟨a, s, v, hs, hvi, hpos, hstep⟩ := exists_step tail head h i hi
  by_cases hv : netOut tail head h v < 0
  · refine ⟨Pi.single a s, v, ?_, hv, hstep⟩
    intro b
    by_cases hb : b = a
    · subst hb; rcases hs with rfl | rfl <;> simp <;> omega
    · simp [hb]; exact le_total 0 (h b)
  · push_neg at hv
    set h' := h - Pi.single a s with hh'
    have hmass : mass h' < m := by
      have := mass_sub_single h a s hs hpos; rw [← hh'] at this; omega
    have hnet : ∀ w, netOut tail head h' w = netOut tail head h w -
        ((if w = i then 1 else 0) - (if w = v then 1 else 0)) := by
      intro w; rw [hh', netOut_sub, hstep]
    have hv' : 0 < netOut tail head h' v := by
      have := hnet v; rw [if_neg hvi, if_pos rfl] at this; omega
    obtain ⟨χ', k, hconf, hk, hχ'⟩ := ih _ hmass h' rfl v hv'
    have hkv : k ≠ v := by intro hkv; subst hkv; omega
    have hki : k ≠ i := by
      intro hki; subst hki
      have := hnet k; simp [hvi.symm] at this; omega
    refine ⟨χ' + Pi.single a s, k, ?_, ?_, ?_⟩
    · intro b
      have hc := hconf b
      by_cases hb : b = a
      · subst hb
        simp only [hh', Pi.sub_apply, Pi.single_eq_same, Pi.add_apply] at hc ⊢
        rcases hs with rfl | rfl <;> omega
      · simp only [hh', Pi.sub_apply, Pi.add_apply, Pi.single_apply, hb, if_false,
          sub_zero, add_zero] at hc ⊢
        exact hc
    · have := hnet k; simp [hki, hkv] at this; omega
    · intro w
      rw [netOut_add, hχ', hstep]
      ring

end lemmas

end GC.FlowCircuits
