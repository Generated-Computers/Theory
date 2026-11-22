import Mathlib.Data.Nat.Find
import Mathlib.Order.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Shared definitions for family 010

* Normalized append-only machines (Definition 2.1 of 010a, Definition 2.1 of 010c, Section 2.1
  of 010e).  The horizon `N` plays no role in the definitions: the real execution is defined for
  all stages, and statements restrict to `t ≤ N` where needed.
* An abstract greedy-cover lemma (Proposition 5.6 of 010b, Proposition 4.4 of 010c).
-/

namespace GC.Tabulation

/-- A normalized append-only machine.  `Option W` stands for `W ∪ {⊥}` (`none = ⊥`).
Stage `s ≥ 1` writes the cell `wr(s) = m + s - 1`.  The initial history is `Hin 0, …,
Hin (m-1)`; values of `Hin` at other indices are never used. -/
structure AppendMachine (Q W : Type*) where
  /-- length of the initial history -/
  m : ℕ
  /-- the initial history -/
  Hin : ℕ → W
  /-- the start configuration -/
  C0 : Q
  /-- the read-address map -/
  p : Q → ℤ
  /-- the written-word map -/
  w : Q → W
  /-- the transition maps `Φ_t` -/
  Φ : ℕ → Q → Option W → Q

namespace AppendMachine

variable {Q W : Type*} (M : AppendMachine Q W)

/-- The read result `h_Z(t, a)` at stage `t` for address `a`, answering internal reads from the
transcript `Z` (the cell `wr(s) = m + s - 1`, `1 ≤ s < t`, holds `w(Z_{s-1})`). -/
def read (Z : ℕ → Q) (t : ℕ) (a : ℤ) : Option W :=
  if 0 ≤ a ∧ a < M.m then some (M.Hin a.toNat)
  else if (M.m : ℤ) ≤ a ∧ a < M.m + t - 1 then some (M.w (Z (a - M.m).toNat))
  else none

lemma read_succ (Z : ℕ → Q) (t : ℕ) (a : ℤ) : M.read Z (t + 1) a =
    if 0 ≤ a ∧ a < M.m then some (M.Hin a.toNat)
    else if (M.m : ℤ) ≤ a ∧ a < M.m + t then some (M.w (Z (a - M.m).toNat)) else none := by
  simp only [read]
  push_cast
  rw [show (M.m : ℤ) + (t + 1) - 1 = M.m + t by ring]

/-- The real execution `C*`. -/
def real : ℕ → Q
  | 0 => M.C0
  | t + 1 =>
    M.Φ (t + 1) (real t)
      (if 0 ≤ M.p (real t) ∧ M.p (real t) < M.m then some (M.Hin (M.p (real t)).toNat)
       else if _h : (M.m : ℤ) ≤ M.p (real t) ∧ M.p (real t) < M.m + t then
         some (M.w (real (M.p (real t) - M.m).toNat))
       else none)
termination_by t => t
decreasing_by all_goals omega

lemma real_zero : M.real 0 = M.C0 := by rw [real]

/-- The defining recursion of the real execution: `C*_t = Φ_t(C*_{t-1}, h*_t)`. -/
lemma real_succ (t : ℕ) :
    M.real (t + 1) = M.Φ (t + 1) (M.real t) (M.read M.real (t + 1) (M.p (M.real t))) := by
  rw [real]
  simp only [read, dite_eq_ite]
  congr 3
  push_cast
  rw [show (M.m : ℤ) + (t + 1) - 1 = M.m + t by ring]

/-- The read at stage `t ≥ 1` is internal (with writer `s = (p(C*_{t-1}) - m) + 1`). -/
def IsInternal (t : ℕ) : Prop :=
  (M.m : ℤ) ≤ M.p (M.real (t - 1)) ∧ M.p (M.real (t - 1)) < M.m + t - 1

/-- The writer `s(t)` of stage `t` when its real read is internal (`none` otherwise, and for
`t = 0`). -/
noncomputable def writer (t : ℕ) : Option ℕ :=
  open Classical in
  if t ≠ 0 ∧ M.IsInternal t then some ((M.p (M.real (t - 1)) - M.m).toNat + 1) else none

lemma writer_lt {t s : ℕ} (h : M.writer t = some s) : 1 ≤ s ∧ s < t := by
  unfold writer IsInternal at h
  split_ifs at h with h1
  · simp only [Option.some.injEq] at h
    omega

end AppendMachine

/-! ### Greedy covers -/

section Greedy

open Classical

/-- The largest `b ≤ N` such that `(a, b]` is an admissible piece. -/
noncomputable def reach (ok : ℕ → ℕ → Prop) (N a : ℕ) : ℕ := Nat.findGreatest (fun b => ok a b) N

lemma reach_le (ok : ℕ → ℕ → Prop) (N a : ℕ) : reach ok N a ≤ N := Nat.findGreatest_le N

lemma le_reach (ok : ℕ → ℕ → Prop) {N a b : ℕ} (hb : b ≤ N) (h : ok a b) : b ≤ reach ok N a :=
  Nat.le_findGreatest hb h

lemma reach_spec (ok : ℕ → ℕ → Prop) {N a b : ℕ} (hb : b ≤ N) (h : ok a b) :
    ok a (reach ok N a) :=
  Nat.findGreatest_spec (P := fun b => ok a b) hb h

lemma not_ok_of_reach_lt (ok : ℕ → ℕ → Prop) {N a b : ℕ} (h : reach ok N a < b) (hb : b ≤ N) :
    ¬ ok a b :=
  Nat.findGreatest_is_greatest h hb

/-- The greedy cover: `g_0 = 0`, `g_{k+1} = reach(g_k)` while `g_k < N`. -/
noncomputable def greedySeq (ok : ℕ → ℕ → Prop) (N : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => if greedySeq ok N k < N then reach ok N (greedySeq ok N k) else greedySeq ok N k

lemma greedySeq_le (ok : ℕ → ℕ → Prop) (N : ℕ) (k : ℕ) : greedySeq ok N k ≤ N := by
  induction k with
  | zero => simp [greedySeq]
  | succ k ih =>
    simp only [greedySeq]
    split_ifs
    · exact Nat.findGreatest_le N
    · exact ih

/-- Each greedy piece is admissible and nonempty. -/
lemma greedySeq_piece (ok : ℕ → ℕ → Prop) (N : ℕ) (hstep : ∀ a, ok a (a + 1)) (k : ℕ)
    (hk : greedySeq ok N k < N) :
    greedySeq ok N k < greedySeq ok N (k + 1) ∧ ok (greedySeq ok N k) (greedySeq ok N (k + 1)) := by
  simp only [greedySeq, if_pos hk]
  have h1 : greedySeq ok N k + 1 ≤ reach ok N (greedySeq ok N k) :=
    Nat.le_findGreatest (by omega) (hstep _)
  refine ⟨by omega, ?_⟩
  exact Nat.findGreatest_spec (P := fun b => ok (greedySeq ok N k) b) (by omega) (hstep _)

/-- **Greedy optimality.** Suppose admissibility of a piece `(a, b]` is preserved when its left
end moves right (`a ≤ a' < b`), and single steps are admissible.  If `(0, N]` is covered by `k`
admissible pieces `0 = c_0 < c_1 < ⋯ < c_k = N`, then the greedy cover reaches `N` after at most
`k` pieces. -/
theorem greedy_optimal (ok : ℕ → ℕ → Prop) (N : ℕ)
    (hshrink : ∀ a a' b, ok a b → a ≤ a' → a' < b → ok a' b) (hstep : ∀ a, ok a (a + 1))
    (c : ℕ → ℕ) (k : ℕ) (hc0 : c 0 = 0) (hck : c k = N)
    (hc : ∀ j < k, c j < c (j + 1) ∧ ok (c j) (c (j + 1))) :
    greedySeq ok N k = N := by
  have hmono : ∀ j, j ≤ k → c j ≤ N := by
    intro j hj
    rw [← hck]
    obtain ⟨d, rfl⟩ : ∃ d, k = j + d := ⟨k - j, by omega⟩
    clear hck
    induction d with
    | zero => rfl
    | succ d ih =>
      exact (ih (fun i hi => hc i (by omega)) (by omega)).trans
        (hc (j + d) (by omega)).1.le
  have key : ∀ j, j ≤ k → c j ≤ greedySeq ok N j := by
    intro j
    induction j with
    | zero => intro _; simp [hc0, greedySeq]
    | succ j ih =>
      intro hj
      have ihj := ih (by omega)
      have hcj := hc j (by omega)
      have hcN := hmono (j + 1) hj
      simp only [greedySeq]
      split_ifs with hg
      · by_cases hge : c (j + 1) ≤ greedySeq ok N j
        · exact hge.trans (Nat.le_findGreatest (by omega) (hstep _) |>.trans' (by omega))
        · exact Nat.le_findGreatest hcN (hshrink _ _ _ hcj.2 ihj (by omega))
      · have := greedySeq_le ok N j
        omega
  have h1 := key k le_rfl
  have h2 := greedySeq_le ok N k
  omega

end Greedy

end GC.Tabulation
