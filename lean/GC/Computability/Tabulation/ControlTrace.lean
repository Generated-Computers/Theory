import GC.Computability.Tabulation.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Abel

/-!
# Strict P-completeness reduces to the control trace (manuscript 010d)

A normalized register–stack machine is an append-only machine whose local configurations are a
control state and a register vector.  We formalize

* control-trace sufficiency (Proposition 2.4): the control states, hence acceptance, are a
  function of the control trace alone;
* triangularization (Theorem 3.1): given the address–control trace, the register values solve
  `y = L y + d` with `L` strictly lower triangular in time, `L` and `d` built from the trace;
* nilpotent doubling (Lemma 3.2) and payload reconstruction (Theorem 3.3): `y = S_R d`.

The conditional transfer theorem (Theorem 4.2), which rests on Reinhardt's framework (Fact 4.1),
the MCP/USIARV equivalence, the PRAM costs and the integer bit bound are not formalized.
-/

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

lemma toAppend_m : (R.toAppend m H q0 x0).m = m := rfl
lemma toAppend_Hin : (R.toAppend m H q0 x0).Hin = H := rfl
lemma toAppend_w (c : Q × (ι → ℤ)) : (R.toAppend m H q0 x0).w c = c.2 R.r2 := rfl

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

lemma run_succ (t : ℕ) : R.run m H q0 x0 (t + 1) =
    R.step (R.run m H q0 x0 t)
      (((R.toAppend m H q0 x0).read (R.toAppend m H q0 x0).real (t + 1)
        ((R.run m H q0 x0 t).2 R.r1)).getD 0) := by
  simp only [run]
  rw [AppendMachine.real_succ]
  rfl

/-- **Proposition 2.4 (control-trace sufficiency).** The control states are determined by the
control trace: `q_t = (f_t ∘ ⋯ ∘ f_1)(q_0)`. -/
theorem run_ctrl_eq (t : ℕ) : (R.run m H q0 x0 t).1 = R.ctrlOf q0 (R.ctrlTrace m H q0 x0) t := by
  induction t with
  | zero => simp [run, AppendMachine.real_zero, toAppend, ctrlOf]
  | succ t ih => rw [run_succ, ctrlOf, ← ih]; rfl

/-- **Proposition 2.4, acceptance.** Two inputs whose executions have the same control trace up
to the horizon `N` (and the same start state) end in the same control state; acceptance
`q_N ∈ Q_f` is a function of the control trace. -/
theorem accept_of_ctrlTrace {H' : ℕ → ℤ} {x0' : ι → ℤ} {m' : ℕ} (N : ℕ)
    (htr : ∀ t, 1 ≤ t → t ≤ N → R.ctrlTrace m H q0 x0 t = R.ctrlTrace m' H' q0 x0' t)
    (Qf : Set Q) :
    (R.run m H q0 x0 N).1 ∈ Qf ↔ (R.run m' H' q0 x0' N).1 ∈ Qf := by
  have : ∀ t ≤ N, (R.run m H q0 x0 t).1 = (R.run m' H' q0 x0' t).1 := by
    intro t ht
    rw [run_ctrl_eq, run_ctrl_eq]
    induction t with
    | zero => rfl
    | succ t ih => simp only [ctrlOf]; rw [ih (by omega), htr (t + 1) (by omega) ht]
  rw [this N le_rfl]

/-! ### Triangularization (Theorem 3.1) -/

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
  simp only [trL] at h
  by_contra hlt
  push_neg at hlt
  have hlt' : ti.1.val ≤ tj.1.val := hlt
  rw [if_neg (by omega), if_neg] at h
  · simp at h
  · rintro ⟨-, -, ⟨h1, h2⟩, h3⟩
    omega

omit [DecidableEq ι] in
lemma sum_part1 (t : Fin N) (c : ι → ℤ) (g : Fin N → ι → ℤ) :
    ∑ t' : Fin N, ∑ j : ι, (if t'.val + 1 = t.val then c j else 0) * g t' j =
      if h : t.val = 0 then 0 else ∑ j, c j * g ⟨t.val - 1, by omega⟩ j := by
  split_ifs with h
  · apply Finset.sum_eq_zero
    intro t' _
    apply Finset.sum_eq_zero
    intro j _
    rw [if_neg (by omega), zero_mul]
  · rw [Finset.sum_eq_single ⟨t.val - 1, by omega⟩]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [if_pos (by simp; omega)]
    · intro t' _ ht'
      apply Finset.sum_eq_zero
      intro j _
      rw [if_neg, zero_mul]
      intro h'
      exact ht' (Fin.ext (by simp; omega))
    · simp

lemma sum_part2 (P Q' : Prop) [Decidable P] [Decidable Q'] (k : ℕ) (r : ι) (g : Fin N → ι → ℤ) :
    ∑ t' : Fin N, ∑ j : ι, (if P ∧ j = r ∧ Q' ∧ k = t'.val + 1 then (1 : ℤ) else 0) * g t' j =
      if h : P ∧ Q' ∧ 1 ≤ k ∧ k ≤ N then g ⟨k - 1, by omega⟩ r else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨k - 1, by omega⟩]
    · rw [Finset.sum_eq_single r]
      · rw [if_pos ⟨h.1, rfl, h.2.1, by simp; omega⟩, one_mul]
      · intro j _ hj
        rw [if_neg (by tauto), zero_mul]
      · simp
    · intro t' _ ht'
      apply Finset.sum_eq_zero
      intro j _
      rw [if_neg, zero_mul]
      rintro ⟨-, -, -, hk⟩
      exact ht' (Fin.ext (by simp; omega))
    · simp
  · apply Finset.sum_eq_zero
    intro t' _
    apply Finset.sum_eq_zero
    intro j _
    rw [if_neg, zero_mul]
    rintro ⟨h1, -, h3, h4⟩
    exact h ⟨h1, h3, by omega, by have := t'.isLt; omega⟩

/-- **Theorem 3.1 (triangularization), equation.** If `(p, b)` is the address–control trace of
the execution, the register values satisfy `y = L y + d`, where `L` and `d` are built from the
trace, the input words and `x^{(0)}` only. -/
theorem regVec_eq (p : ℕ → ℤ) (b : ℕ → Bool) (hp : ∀ t, p t = R.addrTrace m H q0 x0 t)
    (hb : ∀ t, b t = R.ctrlTrace m H q0 x0 t) :
    R.regVec (N := N) m H q0 x0 = R.trL m q0 p b *ᵥ R.regVec m H q0 x0 + R.trD m H q0 x0 p b := by
  funext ti
  obtain ⟨t, i⟩ := ti
  have hq : (R.run m H q0 x0 t.val).1 = R.ctrlOf q0 b t.val := by
    rw [run_ctrl_eq]
    congr 1
    funext k; rw [hb]
  have hbt : decide (0 < (R.run m H q0 x0 t.val).2 R.r3) = b (t.val + 1) := by
    rw [hb]; rfl
  have hpt : (R.run m H q0 x0 t.val).2 R.r1 = p (t.val + 1) := by
    rw [hp]; rfl
  have hx0 : (R.run m H q0 x0 0).2 = x0 := by simp [run, AppendMachine.real_zero, toAppend]
  simp only [regVec]
  rw [run_succ, hpt]
  simp only [step, hq, hbt]
  simp only [Matrix.mulVec, dotProduct, trL, trD, add_mul, Finset.sum_add_distrib,
    Fintype.sum_prod_type, Pi.add_apply]
  rw [sum_part1, sum_part2]
  have hA : (∑ x, R.A (R.ctrlOf q0 b t.val) (b (t.val + 1)) i x * (R.run m H q0 x0 t.val).2 x) =
      (if h : t.val = 0 then 0 else ∑ j, R.A (R.ctrlOf q0 b t.val) (b (t.val + 1)) i j *
        R.regVec m H q0 x0 (⟨t.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) t.isLt⟩, j)) +
      (if t.val = 0 then ∑ x, R.A (R.ctrlOf q0 b 0) (b 1) i x * x0 x else 0) := by
    by_cases ht : t.val = 0
    · simp only [ht, dite_true, if_true, zero_add, hx0]
    · simp only [ht, dite_false, if_false, add_zero, regVec]
      rw [Nat.sub_add_cancel (by omega)]
  have hread : (if i = R.r0 then ((R.toAppend m H q0 x0).read (R.toAppend m H q0 x0).real
      (t.val + 1) (p (t.val + 1))).getD 0 else 0) =
      (if h : i = R.r0 ∧ internalAt m p t.val ∧ 1 ≤ (p (t.val + 1) - (m : ℤ)).toNat ∧
          (p (t.val + 1) - (m : ℤ)).toNat ≤ N then
        R.regVec (N := N) m H q0 x0 (⟨(p (t.val + 1) - (m : ℤ)).toNat - 1, by
          have h4 := h.2.2.2; have h3 := h.2.2.1; omega⟩, R.r2) else 0) +
      (if i = R.r0 then R.knownRead m H x0 p t.val else 0) := by
    by_cases hi : i = R.r0
    · simp only [hi, true_and, if_true]
      rw [AppendMachine.read_succ]
      simp only [knownRead]
      by_cases h1 : 0 ≤ p (t.val + 1) ∧ p (t.val + 1) < m
      · rw [if_pos (show 0 ≤ p (t.val + 1) ∧ p (t.val + 1) < ((R.toAppend m H q0 x0).m : ℤ)
          from h1), if_pos h1, dif_neg (fun h => by have := h.1.1; omega)]
        simp [toAppend_Hin]
      · rw [if_neg (show ¬(0 ≤ p (t.val + 1) ∧ p (t.val + 1) < ((R.toAppend m H q0 x0).m : ℤ))
          from h1), if_neg h1]
        by_cases h2 : internalAt m p t.val
        · rw [if_pos (show ((R.toAppend m H q0 x0).m : ℤ) ≤ p (t.val + 1) ∧
            p (t.val + 1) < (R.toAppend m H q0 x0).m + t.val from h2)]
          simp only [Option.getD_some, toAppend_w, toAppend_m]
          by_cases hk : (p (t.val + 1) - m).toNat = 0
          · rw [dif_neg (by omega), if_pos ⟨h2, hk⟩, hk, zero_add]
            show (R.run m H q0 x0 0).2 R.r2 = x0 R.r2
            rw [hx0]
          · have hk' : 1 ≤ (p (t.val + 1) - m).toNat ∧ (p (t.val + 1) - m).toNat ≤ N :=
              ⟨by omega, by have := t.isLt; have := h2.2; omega⟩
            rw [dif_pos ⟨h2, hk'.1, hk'.2⟩, if_neg (by tauto), add_zero]
            simp only [regVec]
            rw [Nat.sub_add_cancel (by omega)]
            rfl
        · rw [if_neg (show ¬(((R.toAppend m H q0 x0).m : ℤ) ≤ p (t.val + 1) ∧
            p (t.val + 1) < (R.toAppend m H q0 x0).m + t.val) from h2),
            dif_neg (by tauto), if_neg (by tauto)]
          simp
    · simp [hi]
  rw [hA, hread, add_add_add_comm, add_assoc]

end RSMachine

/-! ### Nilpotent doubling (Lemma 3.2) -/

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

lemma dblP_eq (L : S) (j : ℕ) : dblP L j = L ^ (2 ^ j) := by
  induction j with
  | zero => simp [dblP]
  | succ j ih => rw [dblP, ih, ← pow_add, pow_succ, mul_two]

/-- **Lemma 3.2 (nilpotent doubling).** `P_j = L^{2^j}` and `S_j = ∑_{k < 2^j} L^k`. -/
theorem dblS_eq (L : S) (j : ℕ) : dblS L j = ∑ k ∈ Finset.range (2 ^ j), L ^ k := by
  induction j with
  | zero => simp [dblS]
  | succ j ih =>
    rw [dblS, ih, dblP_eq, Finset.mul_sum, pow_succ, mul_two, Finset.sum_range_add]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← pow_add, add_comm]

/-- **Lemma 3.2, inverse.** If `L^M = 0` and `M ≤ 2^R`, then `S_R = (1 - L)⁻¹`. -/
theorem dblS_inverse (L : S) (M R : ℕ) (hL : L ^ M = 0) (hR : M ≤ 2 ^ R) :
    (1 - L) * dblS L R = 1 ∧ dblS L R * (1 - L) = 1 := by
  have hz : L ^ (2 ^ R) = 0 := by
    rw [show 2 ^ R = M + (2 ^ R - M) by omega, pow_add, hL, zero_mul]
  rw [dblS_eq]
  constructor
  · have := mul_neg_geom_sum L (2 ^ R)
    rw [hz, sub_zero] at this
    exact this
  · have := geom_sum_mul_neg L (2 ^ R)
    rw [hz, sub_zero] at this
    exact this

end Doubling

namespace RSMachine

variable {Q ι : Type*} [Fintype ι] [DecidableEq ι] (R : RSMachine Q ι)
variable (m : ℕ) (H : ℕ → ℤ) (q0 : Q) (x0 : ι → ℤ) {N : ℕ}

lemma trL_pow_entry (p : ℕ → ℤ) (b : ℕ → Bool) (k : ℕ) :
    ∀ ti tj : Fin N × ι, (R.trL m q0 p b ^ k) ti tj ≠ 0 → tj.1.val + k ≤ ti.1.val := by
  induction k with
  | zero =>
    intro ti tj h
    rw [pow_zero, Matrix.one_apply] at h
    split_ifs at h with hij
    · rw [hij]; simp
    · simp at h
  | succ k ih =>
    intro ti tj h
    rw [pow_succ, Matrix.mul_apply] at h
    obtain ⟨u, -, hu⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have h1 := ih ti u (left_ne_zero_of_mul hu)
    have h2 := R.trL_lower m q0 p b u tj (right_ne_zero_of_mul hu)
    have : tj.1.val < u.1.val := h2
    omega

/-- `L` is nilpotent: `L^N = 0`. -/
theorem trL_nilpotent (p : ℕ → ℤ) (b : ℕ → Bool) : R.trL (N := N) m q0 p b ^ N = 0 := by
  ext ti tj
  by_contra h
  have := R.trL_pow_entry m q0 p b N ti tj h
  have := ti.1.isLt
  simp only [Matrix.zero_apply] at *
  omega

/-- **Theorem 3.3 (payload reconstruction).** Given the address–control trace `(p, b)` of an
`N`-stage execution, all register values `x^{(t)}_i` (`1 ≤ t ≤ N`) are `y = S_R d`, where
`S_R` is computed from the trace matrix `L` by `R` rounds of nilpotent doubling, for any `R`
with `N ≤ 2^R` (in particular `R = ⌈log₂ M⌉`, `M = (c+1)N ≥ N`). -/
theorem payload_reconstruction (p : ℕ → ℤ) (b : ℕ → Bool)
    (hp : ∀ t, p t = R.addrTrace m H q0 x0 t) (hb : ∀ t, b t = R.ctrlTrace m H q0 x0 t)
    (Rr : ℕ) (hR : N ≤ 2 ^ Rr) :
    R.regVec (N := N) m H q0 x0 = dblS (R.trL m q0 p b) Rr *ᵥ R.trD m H q0 x0 p b := by
  have hy := R.regVec_eq m H q0 x0 p b hp hb (N := N)
  have hd : R.trD m H q0 x0 p b = (1 - R.trL m q0 p b) *ᵥ R.regVec (N := N) m H q0 x0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, eq_sub_iff_add_eq, add_comm]
    exact hy.symm
  rw [hd, Matrix.mulVec_mulVec,
    (dblS_inverse (R.trL m q0 p b) N Rr (R.trL_nilpotent m q0 p b) hR).2, Matrix.one_mulVec]

end RSMachine

end GC.Tabulation
