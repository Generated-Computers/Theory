import Mathlib.Data.List.ReduceOption
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Stable semisort and padded sorting: problem specifications

Manuscript 011a ("Stable Semisort Is Exactly as Hard as Padded Sorting").

An input consists of `n` records, identified by their positions `0, …, n-1`; record `i` has key
`key i`. Every output is the list of the original indices of the records, in output order (the
records themselves are moved along with their index). This file states the output specifications
of Definitions 2.1–2.2 of the paper.
-/

namespace GC.Semisort

variable {K : Type*}

/-- In `out`, records with equal keys form one contiguous interval. -/
def KeysContiguous (key : ℕ → K) (out : List ℕ) : Prop :=
  ∀ (p q r : ℕ) (hp : p < out.length) (hq : q < out.length) (hr : r < out.length),
    p < q → q < r → key out[p] = key out[r] → key out[q] = key out[p]

/-- In `out`, records with equal keys appear in increasing order of original index. -/
def KeysStable (key : ℕ → K) (out : List ℕ) : Prop :=
  ∀ (p q : ℕ) (hp : p < out.length) (hq : q < out.length),
    p < q → key out[p] = key out[q] → out[p] < out[q]

/-- Output specification of `USemi` (unstable semisort, Definition 2.1(a)): a rearrangement of
the records `0, …, n-1` in which records with equal keys are contiguous. -/
def IsSemisort (key : ℕ → K) (n : ℕ) (out : List ℕ) : Prop :=
  out.Perm (List.range n) ∧ KeysContiguous key out

/-- Output specification of `SS` (stable semisort, Definition 2.2(a)): a semisort in which
records with equal keys keep their input order. -/
def IsStableSemisort (key : ℕ → K) (n : ℕ) (out : List ℕ) : Prop :=
  IsSemisort key n out ∧ KeysStable key out

/-- Output specification of `IS` (stable integer sort, Definition 2.2(b)): the records sorted
by key, ties broken by position. (The key range `[0,n]` is a precondition on the instance.) -/
def IsStableIntSort (a : ℕ → ℕ) (n : ℕ) (out : List ℕ) : Prop :=
  out.Perm (List.range n) ∧ out.Pairwise (fun i j => a i < a j ∨ (a i = a j ∧ i < j))

/-- Output specification of `DS` (sorting distinct integer keys, Definition 2.2(c)). -/
def IsDistinctSort (z : ℕ → ℕ) (n : ℕ) (out : List ℕ) : Prop :=
  out.Perm (List.range n) ∧ out.Pairwise (fun i j => z i < z j)

/-- A valid instance of `PaddedSort(n,U)` and of `DS`: the keys of the records `0, …, n-1` are
distinct and lie in `[0,U)`. -/
def IsDistinctKeyInstance (z : ℕ → ℕ) (n U : ℕ) : Prop :=
  (∀ i < n, z i < U) ∧ ∀ i < n, ∀ j < n, z i = z j → i = j

/-- Output specification of `PaddedSort` (Definition 2.1(b)): an array of `c n` slots
(`c ≥ 1`), a slot being empty (`none`) or holding one record (`some i`), in which every record
occupies exactly one slot and the occupied slots appear in increasing key order. -/
def IsPaddedSort (z : ℕ → ℕ) (n : ℕ) (P : List (Option ℕ)) : Prop :=
  (∃ c : ℕ, 1 ≤ c ∧ P.length = c * n) ∧ P.reduceOption.Perm (List.range n) ∧
    P.reduceOption.Pairwise (fun i j => z i < z j)

/-- Compaction of a padded array (Lemma 2.4): keep the occupied slots, in order. -/
def compact (P : List (Option ℕ)) : List ℕ := P.reduceOption

/-- Lemma 2.4, padded output to sorted dense array. -/
theorem isDistinctSort_compact {z : ℕ → ℕ} {n : ℕ} {P : List (Option ℕ)}
    (h : IsPaddedSort z n P) : IsDistinctSort z n (compact P) :=
  ⟨h.2.1, h.2.2⟩

theorem reduceOption_map_some (l : List ℕ) : (l.map some).reduceOption = l := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.reduceOption_cons_of_some, ih]

/-- Lemma 2.4, sorted dense array to padded output (with `c = 1`). -/
theorem isPaddedSort_map_some {z : ℕ → ℕ} {n : ℕ} {out : List ℕ}
    (h : IsDistinctSort z n out) : IsPaddedSort z n (out.map some) := by
  have hr : (out.map some).reduceOption = out := reduceOption_map_some out
  refine ⟨⟨1, le_rfl, ?_⟩, ?_, ?_⟩
  · simp [h.1.length_eq]
  · rw [hr]; exact h.1
  · rw [hr]; exact h.2

/-! ### Elementary lemmas -/

theorem lt_of_mem_perm_range {n : ℕ} {out : List ℕ} (h : out.Perm (List.range n)) {i : ℕ}
    (hi : i ∈ out) : i < n :=
  List.mem_range.1 (h.subset hi)

/-- Lexicographic encoding: comparing `N * a + b` with `N * c + d`, for remainders `b, d < N`,
compares `a` with `c` first and `b` with `d` second. -/
theorem lex_encode_lt_iff {N a b c d : ℕ} (hb : b < N) (hd : d < N) :
    N * a + b < N * c + d ↔ a < c ∨ (a = c ∧ b < d) := by
  constructor
  · intro h
    rcases lt_trichotomy a c with hac | hac | hac
    · exact Or.inl hac
    · subst hac; exact Or.inr ⟨rfl, by omega⟩
    · exfalso
      have : N * (c + 1) ≤ N * a := Nat.mul_le_mul_left N hac
      rw [Nat.mul_add, Nat.mul_one] at this
      omega
  · rintro (h | ⟨rfl, h⟩)
    · have : N * (a + 1) ≤ N * c := Nat.mul_le_mul_left N h
      rw [Nat.mul_add, Nat.mul_one] at this
      omega
    · omega

theorem lex_encode_inj {N a b c d : ℕ} (hb : b < N) (hd : d < N)
    (h : N * a + b = N * c + d) : a = c ∧ b = d := by
  have h1 := lex_encode_lt_iff (a := a) (c := c) hb hd
  have h2 := lex_encode_lt_iff (a := c) (c := a) hd hb
  rcases lt_trichotomy a c with hac | rfl | hac
  · exact absurd (h1.2 (Or.inl hac)) (by omega)
  · exact ⟨rfl, by omega⟩
  · exact absurd (h2.2 (Or.inl hac)) (by omega)

end GC.Semisort
