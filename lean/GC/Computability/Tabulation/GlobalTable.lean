import GC.Computability.Tabulation.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Algebra.Order.Group.Nat

/-!
# Parallel simulation where only nested reads cost depth (manuscript 010a)

The global table operator `ℋ`, the read-adaptivity rank, the main theorem (after `r + 1`
applications every stage of rank `≤ r` is exact), the unique fixed point, the stopping rule, and
the fixed-lag copy program.  PRAM costs are not formalized.
-/

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
  induction t with
  | zero => rfl
  | succ t ih => simp [globalOp, prefixComp, ih]

/-- Prefix compositions split along any boundary (this is what a parallel prefix scan uses). -/
theorem prefixComp_add (Z : ℕ → Q) (t k : ℕ) :
    M.prefixComp Z (t + k) = M.segComp Z t k ∘ M.prefixComp Z t := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← add_assoc, prefixComp, ih, segComp]
    rfl

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

lemma rank_zero : M.rank 0 = 0 := by rw [rank]

lemma rank_succ (t : ℕ) : M.rank (t + 1) =
    if (M.m : ℤ) ≤ M.p (M.real t) ∧ M.p (M.real t) < M.m + t then
      max (M.rank t) (1 + M.rank (M.p (M.real t) - M.m).toNat)
    else M.rank t := by
  rw [rank]; simp only [dite_eq_ite]

lemma globalOp_fst_of_Φ {W' : Type*} (M' : AppendMachine (ℕ × W') W')
    (hΦ : ∀ t c h, (M'.Φ t c h).1 = t) (hC0 : M'.C0.1 = 0) (Z : ℕ → ℕ × W') (t : ℕ) :
    (M'.globalOp Z t).1 = t := by
  cases t with
  | zero => simpa [globalOp] using hC0
  | succ t => simp [globalOp, table, hΦ]

lemma rank_le_succ (t : ℕ) : M.rank t ≤ M.rank (t + 1) := by
  rw [rank_succ]; split_ifs <;> simp

lemma rank_mono {s t : ℕ} (h : s ≤ t) : M.rank s ≤ M.rank t := by
  induction t with
  | zero => rw [Nat.le_zero.mp h]
  | succ t ih =>
    rcases Nat.lt_or_ge s (t + 1) with h' | h'
    · exact (ih (by omega)).trans (M.rank_le_succ t)
    · rw [show s = t + 1 by omega]

/-- If `Z` agrees with the real execution below `t`, then `ℋ(Z)_t` is exact. -/
lemma globalOp_eq_real_of_agree (Z : ℕ → Q) :
    ∀ t, (∀ k < t, Z k = M.real k) → M.globalOp Z t = M.real t := by
  intro t
  induction t with
  | zero => intro _; rw [globalOp, real_zero]
  | succ t ih =>
    intro hZ
    rw [globalOp, ih (fun k hk => hZ k (by omega)), real_succ, table]
    congr 1
    simp only [read]
    split_ifs with h1 h2
    · rfl
    · rw [hZ _ (by push_cast at h2; omega)]
    · rfl

/-- **Lemma 4.3 (unique fixed point), first part.** `ℋ(C*) = C*`. -/
theorem globalOp_real : M.globalOp M.real = M.real :=
  funext fun t => M.globalOp_eq_real_of_agree M.real t (fun _ _ => rfl)

/-- **Lemma 4.3 (unique fixed point), second part, with a horizon `N`.** If a candidate
transcript satisfies `ℋ(Z)_t = Z_t` for all `t ≤ N`, then `Z_t = C*_t` for all `t ≤ N`. -/
theorem eq_real_of_fixed (Z : ℕ → Q) (N : ℕ) (hfix : ∀ t ≤ N, M.globalOp Z t = Z t) :
    ∀ t ≤ N, Z t = M.real t := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro ht
    rw [← hfix t ht]
    exact M.globalOp_eq_real_of_agree Z t (fun k hk => ih k hk (by omega))

/-- **Theorem 4.2 (global table iteration).** For every candidate transcript `Z`, every `r` and
every stage `t` of read-adaptivity rank `a(t) ≤ r`, the `(r+1)`-st iterate `ℋ^{r+1}(Z)` is exact
at `t`. (The hypothesis `Z_0 = C_0` of the paper is not needed: `ℋ` resets coordinate `0`.) -/
theorem globalOp_iterate_exact (Z : ℕ → Q) :
    ∀ r t, M.rank t ≤ r → (M.globalOp)^[r + 1] Z t = M.real t := by
  intro r
  induction r with
  | zero =>
    intro t
    induction t with
    | zero => intro _; rw [Function.iterate_one, globalOp, real_zero]
    | succ t ih =>
      intro ht
      have hrt := M.rank_le_succ t
      rw [Function.iterate_one] at ih ⊢
      rw [globalOp, ih (by omega), real_succ, table, read_succ, read_succ]
      by_cases h1 : 0 ≤ M.p (M.real t) ∧ M.p (M.real t) < M.m
      · simp only [if_pos h1]
      · simp only [if_neg h1]
        by_cases h2 : (M.m : ℤ) ≤ M.p (M.real t) ∧ M.p (M.real t) < M.m + t
        · rw [rank_succ, if_pos h2] at ht
          omega
        · simp only [if_neg h2]
  | succ r ihr =>
    intro t
    induction t with
    | zero => intro _; rw [Function.iterate_succ_apply', globalOp, real_zero]
    | succ t ih =>
      intro ht
      have hrt := M.rank_le_succ t
      rw [Function.iterate_succ_apply'] at ih ⊢
      rw [globalOp, ih (by omega), real_succ, table, read_succ, read_succ]
      by_cases h1 : 0 ≤ M.p (M.real t) ∧ M.p (M.real t) < M.m
      · simp only [if_pos h1]
      · simp only [if_neg h1]
        by_cases h2 : (M.m : ℤ) ≤ M.p (M.real t) ∧ M.p (M.real t) < M.m + t
        · rw [rank_succ, if_pos h2] at ht
          simp only [if_pos h2]
          rw [ihr _ (by omega)]
        · simp only [if_neg h2]

/-- **Theorem 4.2, consequence.** With horizon `N` and `A_N = max_{t ≤ N} a(t) = a(N)`,
`ℋ^{A_N+1}(Z)_t = C*_t` for all `t ≤ N`. -/
theorem globalOp_iterate_rank_exact (Z : ℕ → Q) (N : ℕ) :
    ∀ t ≤ N, (M.globalOp)^[M.rank N + 1] Z t = M.real t :=
  fun t ht => M.globalOp_iterate_exact Z _ t (M.rank_mono ht)

/-- `a(N)` is the maximal rank `A_N = max_{0 ≤ t ≤ N} a(t)`. -/
theorem rank_le_rank_horizon {N t : ℕ} (ht : t ≤ N) : M.rank t ≤ M.rank N := M.rank_mono ht

/-- **Corollary 4.4 (parameterized compiler), correctness of the stopping rule.** Iterating
`ℋ` from any candidate: (1) after `A_N + 2` applications the test `Z^{(r+1)} = Z^{(r)}` on
`[0, N]` succeeds at `r = A_N + 1`; (2) whenever the test succeeds, the output is the real
execution on `[0, N]`. -/
theorem stopping_rule (Z : ℕ → Q) (N : ℕ) :
    (∀ t ≤ N, (M.globalOp)^[M.rank N + 2] Z t = (M.globalOp)^[M.rank N + 1] Z t) ∧
      ∀ r, (∀ t ≤ N, (M.globalOp)^[r + 1] Z t = (M.globalOp)^[r] Z t) →
        ∀ t ≤ N, (M.globalOp)^[r] Z t = M.real t := by
  refine ⟨fun t ht => ?_, fun r hr => ?_⟩
  · rw [M.globalOp_iterate_rank_exact Z N t ht, Function.iterate_succ_apply']
    apply M.globalOp_eq_real_of_agree
    intro k hk
    exact M.globalOp_iterate_rank_exact Z N k (by omega)
  · apply M.eq_real_of_fixed _ N
    intro t ht
    rw [← Function.iterate_succ_apply' M.globalOp]
    exact hr t ht

end AppendMachine

/-! ### Section 5: the fixed-lag copy program -/

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

omit hd in
lemma copy_p (c : ℕ × W) :
    (copyMachine d Hin).p c = if c.1 + 1 ≤ d then (c.1 : ℤ) else (c.1 : ℤ) + 1 := rfl
omit hd in
lemma copy_w (c : ℕ × W) : (copyMachine d Hin).w c = c.2 := rfl
omit hd in
lemma copy_Φ (t : ℕ) (c : ℕ × W) (h : Option W) :
    (copyMachine d Hin).Φ t c h = (t, h.getD (Hin (d - 1))) := rfl
omit hd in
lemma copy_m : (copyMachine d Hin).m = d := rfl
omit hd in
lemma copy_Hin : (copyMachine d Hin).Hin = Hin := rfl

omit hd in
lemma copy_real_fst (t : ℕ) : ((copyMachine d Hin).real t).1 = t := by
  cases t with
  | zero => simp [AppendMachine.real_zero, copyMachine]
  | succ t => simp [AppendMachine.real_succ, copy_Φ]

omit hd in
/-- The address read at stage `t + 1`. -/
lemma copy_addr (t : ℕ) : (copyMachine d Hin).p ((copyMachine d Hin).real t) =
    if t + 1 ≤ d then (t : ℤ) else (t : ℤ) + 1 := by
  rw [copy_p, copy_real_fst]

/-- **Proposition 5.1(c).** The real execution of the copy program is
`C*_t = (t, H_in[(t-1) mod d])` for `t ≥ 1`: all values are read off by residue arithmetic. -/
theorem copy_real (t : ℕ) : (copyMachine d Hin).real (t + 1) = (t + 1, Hin (t % d)) := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    rw [AppendMachine.real_succ, AppendMachine.read_succ, copy_addr, copy_Φ, copy_m, copy_Hin]
    by_cases ht : t + 1 ≤ d
    · rw [if_pos ht, if_pos (by omega)]
      simp [Nat.mod_eq_of_lt (show t < d by omega)]
    · rw [if_neg ht, if_neg (by omega), if_pos (by omega)]
      have : ((t : ℤ) + 1 - (d : ℤ)).toNat = (t - d) + 1 := by omega
      rw [this, copy_w, ih (t - d) (by omega)]
      simp only [Option.getD_some]
      have hmod : (t - d) % d = t % d := by
        conv_rhs => rw [show t = (t - d) + d by omega, Nat.add_mod_right]
      rw [hmod]

/-- **Proposition 5.1(a).** The read-adaptivity rank of the copy program is
`a(t) = ⌊(t-1)/d⌋` for `t ≥ 1`; hence `A_N = ⌊(N-1)/d⌋`. -/
theorem copy_rank (t : ℕ) : (copyMachine d Hin).rank (t + 1) = t / d := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    rw [AppendMachine.rank_succ, copy_addr, copy_m]
    by_cases ht : t + 1 ≤ d
    · rw [if_pos ht, if_neg (by omega)]
      rcases t with _ | t
      · simp [AppendMachine.rank_zero]
      · rw [ih t (by omega), Nat.div_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega)]
    · rw [if_neg ht, if_pos (by omega)]
      have : ((t : ℤ) + 1 - (d : ℤ)).toNat = (t - d) + 1 := by omega
      rw [this, ih (t - d) (by omega)]
      rcases t with _ | t
      · omega
      · rw [ih t (by omega)]
        have h1 : (t + 1) / d = (t + 1 - d) / d + 1 := Nat.div_eq_sub_div (by omega) (by omega)
        have h2 : t / d ≤ (t + 1) / d := Nat.div_le_div_right (by omega)
        omega

end Copy

/-- The all-zero candidate `Z^{(0)}_t = (t, 0)` for `t ≥ 1`, `Z^{(0)}_0 = C_0 = (0, 1)`. -/
def copyZ0 : ℕ → ℕ × Bool := fun t => if t = 0 then (0, true) else (t, false)

section CopyBool

variable {d : ℕ} (hd : 2 ≤ d)

include hd

lemma copy_iterate (r : ℕ) (t : ℕ) :
    (copyMachine d (fun _ => true)).globalOp^[r] copyZ0 t =
      if t = 0 then (0, true) else (t, decide (t ≤ r * d)) := by
  induction r generalizing t with
  | zero =>
    simp only [Function.iterate_zero, id, copyZ0, zero_mul, nonpos_iff_eq_zero]
    split_ifs with h <;> simp [h]
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    cases t with
    | zero => rfl
    | succ t =>
      have hfst := AppendMachine.globalOp_fst_of_Φ (copyMachine d (fun _ => true))
        (fun _ _ _ => rfl) rfl ((copyMachine d (fun _ => true)).globalOp^[r] copyZ0) t
      simp only [AppendMachine.globalOp, AppendMachine.table]
      rw [copy_p, hfst, AppendMachine.read_succ, copy_Φ, copy_m]
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false]
      have hrd : (r + 1) * d = r * d + d := by ring
      by_cases ht : t + 1 ≤ d
      · rw [if_pos ht, if_pos (by omega)]
        simp only [Option.getD_some, Prod.mk.injEq, true_and, copy_Hin]
        symm
        simpa [hrd] using (show t + 1 ≤ r * d + d by omega)
      · rw [if_neg ht, if_neg (by omega), if_pos (by omega)]
        have : ((t : ℤ) + 1 - (d : ℤ)).toNat = (t - d) + 1 := by omega
        rw [this, copy_w, ih]
        simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, Option.getD_some,
          Prod.mk.injEq, true_and, hrd]
        exact decide_eq_decide.mpr (by omega)

/-- **Proposition 5.1(b).** For the copy program with all initial words `1`, started from the
all-zero candidate, the iterate `ℋ^r(Z^{(0)})` equals the real execution on `[0, N]` iff
`N ≤ r d`. -/
theorem copy_rounds (N r : ℕ) :
    (∀ t ≤ N, (copyMachine d (fun _ => true)).globalOp^[r] copyZ0 t =
      (copyMachine d (fun _ => true)).real t) ↔ N ≤ r * d := by
  have hreal : ∀ t, (copyMachine d (fun _ => true)).real t =
      if t = 0 then (0, true) else (t, true) := by
    intro t
    cases t with
    | zero => simp [AppendMachine.real_zero, copyMachine]
    | succ t => simp [copy_real hd]
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos N with hN | hN
    · omega
    · have := h N le_rfl
      rw [copy_iterate hd, hreal, if_neg (by omega), if_neg (by omega)] at this
      simpa using this
  · intro h t ht
    rw [copy_iterate hd, hreal]
    split_ifs
    · rfl
    · simp only [Prod.mk.injEq, true_and, decide_eq_true_eq]; omega

/-- **Proposition 5.1(b), round count.** For `N ≥ 1`, the iterate `ℋ^r(Z^{(0)})` is exact on
`[0, N]` iff `r ≥ A_N + 1`, where `A_N = a(N)` is the read-adaptivity rank; so the first exact
round is `A_N + 1 = ⌈N/d⌉`. -/
theorem copy_first_exact_round (N r : ℕ) (hN : 1 ≤ N) :
    (∀ t ≤ N, (copyMachine d (fun _ => true)).globalOp^[r] copyZ0 t =
      (copyMachine d (fun _ => true)).real t) ↔
      (copyMachine d (fun _ => true)).rank N + 1 ≤ r := by
  rw [copy_rounds hd]
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  rw [copy_rank hd]
  rw [Nat.add_one_le_iff]
  exact ⟨fun h => by have := (Nat.div_lt_iff_lt_mul (by omega)).mpr h; omega,
    fun h => (Nat.div_lt_iff_lt_mul (by omega)).mp (by omega)⟩

end CopyBool

end GC.Tabulation
