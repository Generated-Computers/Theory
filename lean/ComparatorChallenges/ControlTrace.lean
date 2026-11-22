import Mathlib.Data.Nat.Find
import Mathlib.Order.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Abel

/-!
# Comparator challenge: strict P-completeness reduces to the control trace (010d)

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

open Matrix

/-- A normalized register–stack machine (Definition 2.1): control set `Q`, registers indexed by
`ι`; the designated registers `r0` (receives the read result), `r1` (address), `r2` (appended
word) and `r3` (sign test) play the roles of `x_0, x_1, x_2, x_3`. For each `(q, b)` a next state
`δ q b`, an integer matrix `A q b` and an integer vector `a q b`. -/
structure RSMachine (Q ι : Type*) where
  δ : Q → Bool → Q
  A : Q → Bool → Matrix ι ι ℤ
  a : Q → Bool → ι → ℤ
  r0 : ι
  r1 : ι
  r2 : ι
  r3 : ι

namespace RSMachine

variable {Q ι : Type*} [Fintype ι] [DecidableEq ι] (R : RSMachine Q ι)

/-- One stage: with `b = 1[x_3 > 0]`, `x ↦ A_{q,b} x + h e_0 + a_{q,b}` and `q ↦ δ(q, b)`. -/
def step (c : Q × (ι → ℤ)) (h : ℤ) : Q × (ι → ℤ) :=
  (R.δ c.1 (decide (0 < c.2 R.r3)),
    fun i => (R.A c.1 (decide (0 < c.2 R.r3)) *ᵥ c.2) i + (if i = R.r0 then h else 0) +
      R.a c.1 (decide (0 < c.2 R.r3)) i)

/-- The machine on input (initial stack `H[0..m-1]`, initial registers `x0`, start state `q0`) as
an append-only machine: stage `t` reads `H[p_t]` with `p_t = x_1` (the value `0` for an address
that is neither initial nor written at an earlier stage) and appends `x_2`. -/
def toAppend (m : ℕ) (H : ℕ → ℤ) (q0 : Q) (x0 : ι → ℤ) : AppendMachine (Q × (ι → ℤ)) ℤ where
  m := m
  Hin := H
  C0 := (q0, x0)
  p := fun c => c.2 R.r1
  w := fun c => c.2 R.r2
  Φ := fun _ c h => R.step c (h.getD 0)

variable (m : ℕ) (H : ℕ → ℤ) (q0 : Q) (x0 : ι → ℤ)

/-- The execution `(q_t, x^{(t)})`. -/
def run (t : ℕ) : Q × (ι → ℤ) := (R.toAppend m H q0 x0).real t

/-- The control trace `b_t = 1[x^{(t-1)}_3 > 0]` (`t ≥ 1`). -/
def ctrlTrace (t : ℕ) : Bool := decide (0 < (R.run m H q0 x0 (t - 1)).2 R.r3)

/-- The address trace `p_t = x^{(t-1)}_1` (`t ≥ 1`). -/
def addrTrace (t : ℕ) : ℤ := (R.run m H q0 x0 (t - 1)).2 R.r1

variable {m H q0 x0}

/-- Control states computed from a control trace alone: `q_t = δ(q_{t-1}, b_t)`, that is
`q_t = (f_t ∘ ⋯ ∘ f_1)(q_0)` with `f_t = δ(·, b_t)`. -/
def ctrlOf (q0 : Q) (b : ℕ → Bool) : ℕ → Q
  | 0 => q0
  | t + 1 => R.δ (ctrlOf q0 b t) (b (t + 1))

/-- **Proposition 2.4 (control-trace sufficiency).** The control states are determined by the
control trace: `q_t = (f_t ∘ ⋯ ∘ f_1)(q_0)`. -/
theorem run_ctrl_eq (t : ℕ) : (R.run m H q0 x0 t).1 = R.ctrlOf q0 (R.ctrlTrace m H q0 x0) t := by
  sorry

/-- **Proposition 2.4, acceptance.** Two inputs whose executions have the same control trace up
to the horizon `N` (and the same start state) end in the same control state; acceptance
`q_N ∈ Q_f` is a function of the control trace. -/
theorem accept_of_ctrlTrace {H' : ℕ → ℤ} {x0' : ι → ℤ} {m' : ℕ} (N : ℕ)
    (htr : ∀ t, 1 ≤ t → t ≤ N → R.ctrlTrace m H q0 x0 t = R.ctrlTrace m' H' q0 x0' t)
    (Qf : Set Q) :
    (R.run m H q0 x0 N).1 ∈ Qf ↔ (R.run m' H' q0 x0' N).1 ∈ Qf := by
  sorry

variable (m H q0 x0)

variable {N : ℕ}

/-- The stage-`(t+1)` read is internal (`m ≤ p_{t+1} < m + t`), given the address trace. -/
def internalAt (p : ℕ → ℤ) (t : ℕ) : Prop := (m : ℤ) ≤ p (t + 1) ∧ p (t + 1) < m + t

instance (p : ℕ → ℤ) (t : ℕ) : Decidable (internalAt m p t) := by
  unfold internalAt; infer_instance

/-- The matrix `L` built from the address–control trace `(p, b)`: the row of register `i` at
stage `t + 1` (index `(t, i)`, `t : Fin N`) has the coefficients `(A_{q_t, b_{t+1}})_{ij}` on the
registers of stage `t` (when `t ≥ 1`) and a coefficient `1` on register `x_2` of stage
`s - 1 = p_{t+1} - m` for an internal read with `s ≥ 2`. -/
def trL (p : ℕ → ℤ) (b : ℕ → Bool) : Matrix (Fin N × ι) (Fin N × ι) ℤ := fun ti tj =>
  (if tj.1.val + 1 = ti.1.val then R.A (R.ctrlOf q0 b ti.1.val) (b (ti.1.val + 1)) ti.2 tj.2
    else 0) +
  (if ti.2 = R.r0 ∧ tj.2 = R.r2 ∧ internalAt m p ti.1.val ∧
      (p (ti.1.val + 1) - m).toNat = tj.1.val + 1 then 1 else 0)

/-- The known part of the read result at stage `t + 1`. -/
def knownRead (p : ℕ → ℤ) (t : ℕ) : ℤ :=
  if 0 ≤ p (t + 1) ∧ p (t + 1) < m then H (p (t + 1)).toNat
  else if internalAt m p t ∧ (p (t + 1) - m).toNat = 0 then x0 R.r2 else 0

/-- The vector `d` built from the trace and the known numbers (input words and `x^{(0)}`). -/
def trD (p : ℕ → ℤ) (b : ℕ → Bool) : Fin N × ι → ℤ := fun ti =>
  (if ti.1.val = 0 then (R.A (R.ctrlOf q0 b 0) (b 1) *ᵥ x0) ti.2 else 0) +
  (if ti.2 = R.r0 then R.knownRead m H x0 p ti.1.val else 0) +
  R.a (R.ctrlOf q0 b ti.1.val) (b (ti.1.val + 1)) ti.2

/-- The register values `y_{(t,i)} = x^{(t+1)}_i`, `t < N`. -/
def regVec : Fin N × ι → ℤ := fun ti => (R.run m H q0 x0 (ti.1.val + 1)).2 ti.2

omit [Fintype ι] in
/-- **Theorem 3.1 (triangularization), structure.** `L` is strictly lower triangular in time:
an entry `L_{(t,i),(t',j)}` can be nonzero only if `t' < t`. -/
theorem trL_lower (p : ℕ → ℤ) (b : ℕ → Bool) (ti tj : Fin N × ι)
    (h : R.trL m q0 p b ti tj ≠ 0) : tj.1 < ti.1 := by
  sorry

/-- **Theorem 3.1 (triangularization), equation.** If `(p, b)` is the address–control trace of
the execution, the register values satisfy `y = L y + d`, where `L` and `d` are built from the
trace, the input words and `x^{(0)}` only. -/
theorem regVec_eq (p : ℕ → ℤ) (b : ℕ → Bool) (hp : ∀ t, p t = R.addrTrace m H q0 x0 t)
    (hb : ∀ t, b t = R.ctrlTrace m H q0 x0 t) :
    R.regVec (N := N) m H q0 x0 = R.trL m q0 p b *ᵥ R.regVec m H q0 x0 + R.trD m H q0 x0 p b := by
  sorry

end RSMachine

section Doubling

variable {S : Type*} [Ring S]

/-- `P_0 = L`, `P_{j+1} = P_j²`. -/
def dblP (L : S) : ℕ → S
  | 0 => L
  | j + 1 => dblP L j * dblP L j

/-- `S_0 = 1`, `S_{j+1} = S_j + P_j S_j`. -/
def dblS (L : S) : ℕ → S
  | 0 => 1
  | j + 1 => dblS L j + dblP L j * dblS L j

/-- **Lemma 3.2 (nilpotent doubling).** `P_j = L^{2^j}` and `S_j = ∑_{k < 2^j} L^k`. -/
theorem dblS_eq (L : S) (j : ℕ) : dblS L j = ∑ k ∈ Finset.range (2 ^ j), L ^ k := by
  sorry

/-- **Lemma 3.2, inverse.** If `L^M = 0` and `M ≤ 2^R`, then `S_R = (1 - L)⁻¹`. -/
theorem dblS_inverse (L : S) (M R : ℕ) (hL : L ^ M = 0) (hR : M ≤ 2 ^ R) :
    (1 - L) * dblS L R = 1 ∧ dblS L R * (1 - L) = 1 := by
  sorry

end Doubling

namespace RSMachine

variable {Q ι : Type*} [Fintype ι] [DecidableEq ι] (R : RSMachine Q ι)

variable (m : ℕ) (H : ℕ → ℤ) (q0 : Q) (x0 : ι → ℤ) {N : ℕ}

/-- `L` is nilpotent: `L^N = 0`. -/
theorem trL_nilpotent (p : ℕ → ℤ) (b : ℕ → Bool) : R.trL (N := N) m q0 p b ^ N = 0 := by
  sorry

/-- **Theorem 3.3 (payload reconstruction).** Given the address–control trace `(p, b)` of an
`N`-stage execution, all register values `x^{(t)}_i` (`1 ≤ t ≤ N`) are `y = S_R d`, where
`S_R` is computed from the trace matrix `L` by `R` rounds of nilpotent doubling, for any `R`
with `N ≤ 2^R` (in particular `R = ⌈log₂ M⌉`, `M = (c+1)N ≥ N`). -/
theorem payload_reconstruction (p : ℕ → ℤ) (b : ℕ → Bool)
    (hp : ∀ t, p t = R.addrTrace m H q0 x0 t) (hb : ∀ t, b t = R.ctrlTrace m H q0 x0 t)
    (Rr : ℕ) (hR : N ≤ 2 ^ Rr) :
    R.regVec (N := N) m H q0 x0 = dblS (R.trL m q0 p b) Rr *ᵥ R.trD m H q0 x0 p b := by
  sorry

end RSMachine

end GC.Tabulation
