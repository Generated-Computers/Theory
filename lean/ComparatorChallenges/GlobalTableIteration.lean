import Mathlib.Data.Nat.Find
import Mathlib.Order.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Logic.Function.Iterate
import Mathlib.Algebra.Order.Group.Nat

/-!
# Comparator challenge: parallel simulation where only nested reads cost depth (010a)

Self-contained copy of the definitions used by the statements, with the main theorems
stated `:= by sorry`. Solution module: `GC.Computability.Tabulation.Main`.
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

/-- The read at stage `t ≥ 1` is internal (with writer `s = (p(C*_{t-1}) - m) + 1`). -/
def IsInternal (t : ℕ) : Prop :=
  (M.m : ℤ) ≤ M.p (M.real (t - 1)) ∧ M.p (M.real (t - 1)) < M.m + t - 1

/-- The writer `s(t)` of stage `t` when its real read is internal (`none` otherwise, and for
`t = 0`). -/
noncomputable def writer (t : ℕ) : Option ℕ :=
  open Classical in
  if t ≠ 0 ∧ M.IsInternal t then some ((M.p (M.real (t - 1)) - M.m).toNat + 1) else none

end AppendMachine

section Greedy

open Classical

/-- The largest `b ≤ N` such that `(a, b]` is an admissible piece. -/
noncomputable def reach (ok : ℕ → ℕ → Prop) (N a : ℕ) : ℕ := Nat.findGreatest (fun b => ok a b) N

/-- The greedy cover: `g_0 = 0`, `g_{k+1} = reach(g_k)` while `g_k < N`. -/
noncomputable def greedySeq (ok : ℕ → ℕ → Prop) (N : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => if greedySeq ok N k < N then reach ok N (greedySeq ok N k) else greedySeq ok N k

end Greedy

end GC.Tabulation

namespace GC.Tabulation

namespace AppendMachine

variable {Q W : Type*} (M : AppendMachine Q W)

/-- The table `F^Z_t : 𝒬 → 𝒬`, `F^Z_t(c) = Φ_t(c, h_Z(t, p(c)))` (Definition 3.1). -/
def table (Z : ℕ → Q) (t : ℕ) (c : Q) : Q := M.Φ t c (M.read Z t (M.p c))

/-- The global table operator `ℋ` (Definition 3.1): `ℋ(Z)_0 = C_0`,
`ℋ(Z)_t = F^Z_t(ℋ(Z)_{t-1})`. -/
def globalOp (Z : ℕ → Q) : ℕ → Q
  | 0 => M.C0
  | t + 1 => M.table Z (t + 1) (globalOp Z t)

/-- Prefix compositions `P_t = F^Z_t ∘ ⋯ ∘ F^Z_1`. -/
def prefixComp (Z : ℕ → Q) : ℕ → Q → Q
  | 0 => id
  | t + 1 => M.table Z (t + 1) ∘ prefixComp Z t

/-- Segment compositions `F^Z_{t+k} ∘ ⋯ ∘ F^Z_{t+1}`. -/
def segComp (Z : ℕ → Q) (t : ℕ) : ℕ → Q → Q
  | 0 => id
  | k + 1 => M.table Z (t + k + 1) ∘ segComp Z t k

/-- **Lemma 3.2 (one round), algebraic content.** `ℋ(Z)_t = P_t(C_0)`: the transcript is read
off the prefix compositions of the tables. -/
theorem globalOp_eq_prefixComp (Z : ℕ → Q) (t : ℕ) :
    M.globalOp Z t = M.prefixComp Z t M.C0 := by
  sorry

/-- The read-adaptivity rank `a(t)` (Definition 4.1): `a(0) = 0`; `a(t) = a(t-1)` if the real
read at stage `t` is not internal, and `max(a(t-1), 1 + a(s(t)-1))` if it is internal with
writer `s(t)`. Here `s(t) - 1 = p(C*_{t-1}) - m`. -/
def rank : ℕ → ℕ
  | 0 => 0
  | t + 1 =>
    if _h : (M.m : ℤ) ≤ M.p (M.real t) ∧ M.p (M.real t) < M.m + t then
      max (rank t) (1 + rank (M.p (M.real t) - M.m).toNat)
    else rank t
termination_by t => t
decreasing_by all_goals omega

/-- **Lemma 4.3 (unique fixed point), first part.** `ℋ(C*) = C*`. -/
theorem globalOp_real : M.globalOp M.real = M.real := by
  sorry

/-- **Lemma 4.3 (unique fixed point), second part, with a horizon `N`.** If a candidate
transcript satisfies `ℋ(Z)_t = Z_t` for all `t ≤ N`, then `Z_t = C*_t` for all `t ≤ N`. -/
theorem eq_real_of_fixed (Z : ℕ → Q) (N : ℕ) (hfix : ∀ t ≤ N, M.globalOp Z t = Z t) :
    ∀ t ≤ N, Z t = M.real t := by
  sorry

/-- **Theorem 4.2 (global table iteration).** For every candidate transcript `Z`, every `r` and
every stage `t` of read-adaptivity rank `a(t) ≤ r`, the `(r+1)`-st iterate `ℋ^{r+1}(Z)` is exact
at `t`. (The hypothesis `Z_0 = C_0` of the paper is not needed: `ℋ` resets coordinate `0`.) -/
theorem globalOp_iterate_exact (Z : ℕ → Q) :
    ∀ r t, M.rank t ≤ r → (M.globalOp)^[r + 1] Z t = M.real t := by
  sorry

/-- **Corollary 4.4 (parameterized compiler), correctness of the stopping rule.** Iterating
`ℋ` from any candidate: (1) after `A_N + 2` applications the test `Z^{(r+1)} = Z^{(r)}` on
`[0, N]` succeeds at `r = A_N + 1`; (2) whenever the test succeeds, the output is the real
execution on `[0, N]`. -/
theorem stopping_rule (Z : ℕ → Q) (N : ℕ) :
    (∀ t ≤ N, (M.globalOp)^[M.rank N + 2] Z t = (M.globalOp)^[M.rank N + 1] Z t) ∧
      ∀ r, (∀ t ≤ N, (M.globalOp)^[r + 1] Z t = (M.globalOp)^[r] Z t) →
        ∀ t ≤ N, (M.globalOp)^[r] Z t = M.real t := by
  sorry

end AppendMachine

/-- The copy program `v_t = v_{t-d}` as a normalized append-only machine (Section 5.1):
`m = d`, configurations `(t, v)`, `C_0 = (0, v_0)` with `v_0 = H_in[d-1]`, `w(t, v) = v`,
read address `t - 1` at stages `t ≤ d` and `t` at stages `t > d`, and `Φ_t((t-1, v), h) = (t, h)`. -/
def copyMachine {W : Type*} (d : ℕ) (Hin : ℕ → W) : AppendMachine (ℕ × W) W where
  m := d
  Hin := Hin
  C0 := (0, Hin (d - 1))
  p := fun c => if c.1 + 1 ≤ d then (c.1 : ℤ) else (c.1 : ℤ) + 1
  w := fun c => c.2
  Φ := fun t _ h => (t, h.getD (Hin (d - 1)))

section Copy

variable {W : Type*} {d : ℕ} (hd : 2 ≤ d) (Hin : ℕ → W)

include hd

/-- **Proposition 5.1(c).** The real execution of the copy program is
`C*_t = (t, H_in[(t-1) mod d])` for `t ≥ 1`: all values are read off by residue arithmetic. -/
theorem copy_real (t : ℕ) : (copyMachine d Hin).real (t + 1) = (t + 1, Hin (t % d)) := by
  sorry

/-- **Proposition 5.1(a).** The read-adaptivity rank of the copy program is
`a(t) = ⌊(t-1)/d⌋` for `t ≥ 1`; hence `A_N = ⌊(N-1)/d⌋`. -/
theorem copy_rank (t : ℕ) : (copyMachine d Hin).rank (t + 1) = t / d := by
  sorry

end Copy

/-- The all-zero candidate `Z^{(0)}_t = (t, 0)` for `t ≥ 1`, `Z^{(0)}_0 = C_0 = (0, 1)`. -/
def copyZ0 : ℕ → ℕ × Bool := fun t => if t = 0 then (0, true) else (t, false)

section CopyBool

variable {d : ℕ} (hd : 2 ≤ d)

include hd

/-- **Proposition 5.1(b).** For the copy program with all initial words `1`, started from the
all-zero candidate, the iterate `ℋ^r(Z^{(0)})` equals the real execution on `[0, N]` iff
`N ≤ r d`. -/
theorem copy_rounds (N r : ℕ) :
    (∀ t ≤ N, (copyMachine d (fun _ => true)).globalOp^[r] copyZ0 t =
      (copyMachine d (fun _ => true)).real t) ↔ N ≤ r * d := by
  sorry

/-- **Proposition 5.1(b), round count.** For `N ≥ 1`, the iterate `ℋ^r(Z^{(0)})` is exact on
`[0, N]` iff `r ≥ A_N + 1`, where `A_N = a(N)` is the read-adaptivity rank; so the first exact
round is `A_N + 1 = ⌈N/d⌉`. -/
theorem copy_first_exact_round (N r : ℕ) (hN : 1 ≤ N) :
    (∀ t ≤ N, (copyMachine d (fun _ => true)).globalOp^[r] copyZ0 t =
      (copyMachine d (fun _ => true)).real t) ↔
      (copyMachine d (fun _ => true)).rank N + 1 ≤ r := by
  sorry

end CopyBool

end GC.Tabulation
