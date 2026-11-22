import Mathlib.Data.Fin.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel

/-!
# NOR shift registers are tiling rotations (manuscript 010b)

Rows of width `D` are functions `Fin D → Bool`; position `s : Fin D` is the paper's
coordinate `s + 1`.  Cyclic words of length `D + 1` are functions `Fin (D + 1) → Bool`, with
cyclic index arithmetic of `Fin (D + 1)`.
-/

namespace GC.Tabulation

open Fin.NatCast

/-- `NOR(u, v) = ¬(u ∨ v)`. -/
def nor (u v : Bool) : Bool := !(u || v)

/-- Entry `s` (0-based) of a row; `false` outside the row. -/
def rowGet {D : ℕ} (x : Fin D → Bool) (s : ℕ) : Bool :=
  if h : s < D then x ⟨s, h⟩ else false

/-- The sweep values `y_0 = x_D`, `y_{s+1} = G(y_s, x_{s+1})` (paper's 1-based `x`). -/
def sweepVal (G : Bool → Bool → Bool) {D : ℕ} (x : Fin D → Bool) : ℕ → Bool
  | 0 => rowGet x (D - 1)
  | s + 1 => G (sweepVal G x s) (rowGet x s)

/-- The sweep map `F_{G,D}` (Definition 2.1): `F_{G,D}(x) = (y_1, …, y_D)`. -/
def sweep (G : Bool → Bool → Bool) {D : ℕ} (x : Fin D → Bool) : Fin D → Bool :=
  fun s => sweepVal G x (s.val + 1)

/-- A uniform-lag sequence with gate `G` and lag `D`: `x_i = G(x_{i-1}, x_{i-D})` for `i ≥ D`;
the first `D` values are arbitrary. -/
def IsLagSeq (G : Bool → Bool → Bool) (D : ℕ) (x : ℕ → Bool) : Prop :=
  ∀ i, D ≤ i → x i = G (x (i - 1)) (x (i - D))

/-- Row `q` of a sequence: `x^{(q)} = (x_{qD}, …, x_{qD+D-1})`. -/
def rowOf (D : ℕ) (x : ℕ → Bool) (q : ℕ) : Fin D → Bool :=
  fun s => x (q * D + s.val)

/-- Cyclic tilings `𝒯_{D+1}` by the blocks `10` and `100`: no cyclic `11` and no cyclic `000`
(Definition 3.1). -/
def IsTiling {D : ℕ} (w : Fin (D + 1) → Bool) : Prop :=
  ∀ i : Fin (D + 1), ¬(w i = true ∧ w (i + 1) = true) ∧
    ¬(w i = false ∧ w (i + 1) = false ∧ w (i + 2) = false)

/-- `π(w) = (w_1, …, w_D)` deletes coordinate `0`. -/
def proj {D : ℕ} (w : Fin (D + 1) → Bool) : Fin D → Bool := fun s => w s.succ

/-- The cyclic right rotation `ρ(w) = (w_D, w_0, …, w_{D-1})`. -/
def rotR {D : ℕ} (w : Fin (D + 1) → Bool) : Fin (D + 1) → Bool := fun i => w (i - 1)

/-! ### Lemma 2.2: uniform-lag instances are wavefronts -/

lemma sweepVal_eq_of_rec (G : Bool → Bool → Bool) {D : ℕ} (hD : 1 ≤ D) (x : ℕ → Bool) (q : ℕ)
    (hx : ∀ i, (q + 1) * D ≤ i → i < (q + 2) * D → x i = G (x (i - 1)) (x (i - D))) :
    ∀ s, s ≤ D → sweepVal G (rowOf D x q) s = x (q * D + D - 1 + s) := by
  have e1 : (q + 1) * D = q * D + D := by ring
  have e2 : (q + 2) * D = q * D + D + D := by ring
  simp only [e1, e2] at hx
  intro s
  induction s with
  | zero =>
    intro _
    simp only [sweepVal, rowGet, rowOf]
    rw [dif_pos (by omega)]
    congr 1; omega
  | succ s ih =>
    intro hs
    simp only [sweepVal]
    rw [ih (by omega)]
    simp only [rowGet, rowOf]
    rw [dif_pos (by omega)]
    have := hx (q * D + D - 1 + (s + 1)) (by omega) (by omega)
    rw [this]
    congr 2 <;> omega

/-- Lemma 2.2 (local form): if the recurrence holds on row `q + 1`, then row `q + 1` is the
sweep of row `q`. -/
theorem rowOf_succ_eq_sweep (G : Bool → Bool → Bool) {D : ℕ} (hD : 1 ≤ D) (x : ℕ → Bool)
    (q : ℕ) (hx : ∀ i, (q + 1) * D ≤ i → i < (q + 2) * D → x i = G (x (i - 1)) (x (i - D))) :
    rowOf D x (q + 1) = sweep G (rowOf D x q) := by
  funext s
  simp only [sweep]
  rw [sweepVal_eq_of_rec G hD x q hx _ (by omega)]
  simp only [rowOf]
  congr 1
  have e1 : (q + 1) * D = q * D + D := by ring
  rw [e1]; omega

/-- **Lemma 2.2.** The rows of a uniform-lag sequence satisfy `x^{(q+1)} = F_{G,D}(x^{(q)})`. -/
theorem lagSeq_rows (G : Bool → Bool → Bool) {D : ℕ} (hD : 1 ≤ D) {x : ℕ → Bool}
    (hx : IsLagSeq G D x) (q : ℕ) : rowOf D x (q + 1) = sweep G (rowOf D x q) :=
  rowOf_succ_eq_sweep G hD x q (fun i hi _ => hx i (by rw [Nat.add_mul] at hi; omega))

theorem lagSeq_rows_iterate (G : Bool → Bool → Bool) {D : ℕ} (hD : 1 ≤ D) {x : ℕ → Bool}
    (hx : IsLagSeq G D x) (q : ℕ) : rowOf D x q = (sweep G)^[q] (rowOf D x 0) := by
  induction q with
  | zero => rfl
  | succ q ih => rw [lagSeq_rows G hD hx q, ih, Function.iterate_succ_apply']

/-- The uniform-lag sequence with first row `x0` (used to realize every row). -/
def lagSeq (G : Bool → Bool → Bool) (D : ℕ) (x0 : Fin D → Bool) : ℕ → Bool
  | i => if h : i < D ∨ D = 0 then rowGet x0 i else
      G (lagSeq G D x0 (i - 1)) (lagSeq G D x0 (i - D))
termination_by i => i
decreasing_by all_goals omega

lemma lagSeq_isLagSeq (G : Bool → Bool → Bool) {D : ℕ} (hD : 1 ≤ D) (x0 : Fin D → Bool) :
    IsLagSeq G D (lagSeq G D x0) := by
  intro i hi
  rw [lagSeq, dif_neg (by omega)]

lemma lagSeq_row_zero (G : Bool → Bool → Bool) {D : ℕ} (x0 : Fin D → Bool) :
    rowOf D (lagSeq G D x0) 0 = x0 := by
  funext s
  simp only [rowOf, zero_mul, zero_add]
  rw [lagSeq, dif_pos (Or.inl s.isLt)]
  simp [rowGet, s.isLt]

/-! ### NOR sequences -/

section NorSeq

variable {D : ℕ} {x : ℕ → Bool}

lemma nor_step (hx : IsLagSeq nor D x) (j : ℕ) : x (j + D) = nor (x (j + D - 1)) (x j) := by
  have := hx (j + D) (by omega)
  rwa [Nat.add_sub_cancel] at this

/-- No `11` from index `D` on. -/
lemma nor_no11 (hx : IsLagSeq nor D x) (i : ℕ) (hi : D ≤ i) :
    ¬(x i = true ∧ x (i + 1) = true) := by
  rintro ⟨h1, h2⟩
  have := hx (i + 1) (by omega)
  rw [Nat.add_sub_cancel, h1] at this
  simp [nor, h2] at this

/-- No `000` centred at an index `≥ 2D`. -/
lemma nor_no000 (hD : 1 ≤ D) (hx : IsLagSeq nor D x) (i : ℕ) (hi : 2 * D ≤ i + 1) :
    ¬(x i = false ∧ x (i + 1) = false ∧ x (i + 2) = false) := by
  rintro ⟨h0, h1, h2⟩
  -- x_{i+1} = NOR(x_i, x_{i+1-D}) = ¬x_{i+1-D}, so x_{i+1-D} = 1
  have e1 := hx (i + 1) (by omega)
  rw [Nat.add_sub_cancel, h0, h1] at e1
  -- x_{i+2-D} = 0 because i+1-D ≥ D
  have e2 := nor_no11 hx (i + 1 - D) (by omega)
  have e3 := hx (i + 2) (by omega)
  rw [show i + 2 - 1 = i + 1 by omega, h1, h2, show i + 2 - D = i + 1 - D + 1 by omega] at e3
  revert e1 e2 e3
  generalize x (i + 1 - D) = a
  generalize x (i + 1 - D + 1) = b
  revert a b; decide

/-- The local rule `x_j = NOR(x_{j-1}, x_{j+1})` for `j ≥ 2D`. -/
lemma nor_local (hD : 1 ≤ D) (hx : IsLagSeq nor D x) (j : ℕ) (hj : 2 * D ≤ j) :
    x j = nor (x (j - 1)) (x (j + 1)) := by
  have a1 := nor_no11 hx (j - 1) (by omega)
  have a2 := nor_no11 hx j (by omega)
  have a3 := nor_no000 hD hx (j - 1) (by omega)
  rw [show j - 1 + 1 = j by omega] at a1 a3
  rw [show j - 1 + 2 = j + 1 by omega] at a3
  revert a1 a2 a3
  generalize x (j - 1) = a
  generalize x j = b
  generalize x (j + 1) = c
  revert a b c; decide

/-- The wrap-around identity `x_{3D} = x_{2D-1}`. -/
lemma nor_wrap (hD : 1 ≤ D) (hx : IsLagSeq nor D x) : x (3 * D) = x (2 * D - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, D = n + 1 := ⟨D - 1, by omega⟩
  rcases n with _ | n
  · -- D = 1: x_i = ¬x_{i-1}
    have h3 := hx 3 (by omega)
    have h2 := hx 2 (by omega)
    simp only [show (3 : ℕ) - 1 = 2 by rfl, show (2 : ℕ) - 1 = 1 by rfl] at h3 h2
    simp only [show 3 * (0 + 1) = 3 by rfl, show 2 * (0 + 1) - 1 = 1 by rfl]
    rw [h3, h2]
    cases x 1 <;> rfl
  · -- D = n + 2
    have s := fun j => nor_step hx j
    have h1 : x (3 * n + 6) = nor (x (3 * n + 5)) (x (2 * n + 4)) := by
      have := s (2 * n + 4); rwa [show 2 * n + 4 + (n + 1 + 1) = 3 * n + 6 by ring,
        show 3 * n + 6 - 1 = 3 * n + 5 by omega] at this
    have h2 : x (3 * n + 5) = nor (x (3 * n + 4)) (x (2 * n + 3)) := by
      have := s (2 * n + 3); rwa [show 2 * n + 3 + (n + 1 + 1) = 3 * n + 5 by ring,
        show 3 * n + 5 - 1 = 3 * n + 4 by omega] at this
    have h3 : x (3 * n + 4) = nor (x (3 * n + 3)) (x (2 * n + 2)) := by
      have := s (2 * n + 2); rwa [show 2 * n + 2 + (n + 1 + 1) = 3 * n + 4 by ring,
        show 3 * n + 4 - 1 = 3 * n + 3 by omega] at this
    have h4 : x (2 * n + 3) = nor (x (2 * n + 2)) (x (n + 1)) := by
      have := s (n + 1); rwa [show n + 1 + (n + 1 + 1) = 2 * n + 3 by ring,
        show 2 * n + 3 - 1 = 2 * n + 2 by omega] at this
    have h5 : x (n + 2) = nor (x (n + 1)) (x 0) := by
      have := s 0; rwa [show 0 + (n + 1 + 1) = n + 2 by ring,
        show n + 2 - 1 = n + 1 by omega] at this
    have h6 : x (2 * n + 4) = nor (x (2 * n + 3)) (x (n + 2)) := by
      have := s (n + 2); rwa [show n + 2 + (n + 1 + 1) = 2 * n + 4 by ring,
        show 2 * n + 4 - 1 = 2 * n + 3 by omega] at this
    rw [show 3 * (n + 1 + 1) = 3 * n + 6 by ring, show 2 * (n + 1 + 1) - 1 = 2 * n + 3 by omega]
    revert h1 h2 h3 h4 h5 h6
    generalize x (3 * n + 6) = a6
    generalize x (3 * n + 5) = a5
    generalize x (3 * n + 4) = a4
    generalize x (3 * n + 3) = a3
    generalize x (2 * n + 4) = b4
    generalize x (2 * n + 3) = b3
    generalize x (2 * n + 2) = b2
    generalize x (n + 2) = c2
    generalize x (n + 1) = c1
    generalize x 0 = c0
    revert a6 a5 a4 a3 b4 b3 b2 c2 c1 c0; decide

/-- **Corollary 3.5 (periodicity), strengthened by one index.** For a uniform-lag NOR sequence
with arbitrary first values, `x_{i+D+1} = x_i` for all `i ≥ 2D - 1` (the paper states
`i ≥ 2D`). -/
theorem nor_periodic (hD : 1 ≤ D) (hx : IsLagSeq nor D x) :
    ∀ i, 2 * D - 1 ≤ i → x (i + D + 1) = x i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases Nat.eq_or_lt_of_le hi with h | _
    · subst h
      rw [show 2 * D - 1 + D + 1 = 3 * D by omega]
      exact nor_wrap hD hx
    · have e := hx (i + D + 1) (by omega)
      rw [show i + D + 1 - 1 = (i - 1) + D + 1 by omega, ih (i - 1) (by omega) (by omega),
        show i + D + 1 - D = i + 1 by omega] at e
      rw [e, ← nor_local hD hx i (by omega)]

lemma nor_periodic_mod (hD : 1 ≤ D) (hx : IsLagSeq nor D x) (k : ℕ) :
    x (2 * D - 1 + k % (D + 1)) = x (2 * D - 1 + k) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases lt_or_ge k (D + 1) with h | h
    · rw [Nat.mod_eq_of_lt h]
    · rw [show k = (k - (D + 1)) + (D + 1) by omega, Nat.add_mod_right,
        ih _ (by omega), show 2 * D - 1 + (k - (D + 1) + (D + 1)) = 2 * D - 1 + (k - (D + 1))
          + D + 1 by omega, nor_periodic hD hx _ (by omega)]

/-- From index `2D - 1` on, every window of consecutive values has no `11` and no `000`. -/
lemma nor_window (hD : 1 ≤ D) (hx : IsLagSeq nor D x) (i : ℕ) (hi : 2 * D - 1 ≤ i) :
    ¬(x i = true ∧ x (i + 1) = true) ∧
      ¬(x i = false ∧ x (i + 1) = false ∧ x (i + 2) = false) :=
  ⟨nor_no11 hx i (by omega), nor_no000 hD hx i (by omega)⟩

end NorSeq

/-! ### Cyclic words -/

section Cyclic

variable {D : ℕ}

lemma fin_val_add_nat (i : Fin (D + 1)) (k : ℕ) :
    ((i + (k : Fin (D + 1)) : Fin (D + 1)) : ℕ) = (i.val + k) % (D + 1) := by
  rw [Fin.val_add, Fin.val_natCast, Nat.add_mod_mod]

/-- **Lemma 3.2 (unique cyclic extension).** In a cyclic tiling, a coordinate is `1` iff both
cyclic neighbours are `0`. -/
theorem tiling_local {w : Fin (D + 1) → Bool} (hw : IsTiling w) (i : Fin (D + 1)) :
    w i = nor (w (i - 1)) (w (i + 1)) := by
  have a1 := (hw (i - 1)).1
  have a2 := (hw i).1
  have a3 := (hw (i - 1)).2
  rw [sub_add_cancel] at a1 a3
  rw [show i - 1 + 2 = i + 1 by rw [← one_add_one_eq_two]; abel] at a3
  revert a1 a2 a3
  generalize w (i - 1) = a
  generalize w i = b
  generalize w (i + 1) = c
  revert a b c; decide

/-- `π` is injective on `𝒯_{D+1}` (Lemma 3.2). -/
theorem proj_injOn {w w' : Fin (D + 1) → Bool} (hw : IsTiling w) (hw' : IsTiling w')
    (h : proj w = proj w') : w = w' := by
  have hs : ∀ s : Fin D, w s.succ = w' s.succ := fun s => congrFun h s
  funext i
  by_cases hi : i = 0
  · subst hi
    rw [tiling_local hw 0, tiling_local hw' 0]
    rcases D with _ | D
    · -- `D = 0`: `𝒯_1` is empty
      exfalso
      have := hw 0
      revert this
      simp only [show (0 : Fin 1) + 1 = 0 from rfl, show (0 : Fin 1) + 2 = 0 from rfl]
      cases w 0 <;> simp
    · have e1 : (0 : Fin (D + 2)) - 1 = (Fin.last D).succ := by
        ext; simp [Fin.val_sub]
      have e2 : (0 : Fin (D + 2)) + 1 = (0 : Fin (D + 1)).succ := by ext; simp
      rw [e1, e2, hs, hs]
  · obtain ⟨s, rfl⟩ := Fin.exists_succ_eq.mpr hi
    exact hs s

lemma rotR_tiling {w : Fin (D + 1) → Bool} (hw : IsTiling w) : IsTiling (rotR w) := by
  intro i
  have := hw (i - 1)
  simp only [rotR]
  rwa [show i + 1 - 1 = i - 1 + 1 by abel, show i + 2 - 1 = i - 1 + 2 by abel]

lemma rotR_iterate (w : Fin (D + 1) → Bool) (k : ℕ) :
    (rotR)^[k] w = fun i => w (i - (k : Fin (D + 1))) := by
  induction k with
  | zero => funext i; simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    funext i
    simp only [rotR, Nat.cast_succ]
    congr 1; abel

lemma rotR_iterate_period (w : Fin (D + 1) → Bool) : (rotR)^[D + 1] w = w := by
  rw [rotR_iterate]
  funext i
  simp

/-- **Theorem 3.4 (NOR tiling rotation).** For every `w ∈ 𝒯_{D+1}`, `F_D(π(w)) = π(ρ(w))`. -/
theorem sweep_proj_tiling {w : Fin (D + 1) → Bool} (hw : IsTiling w) :
    sweep nor (proj w) = proj (rotR w) := by
  rcases Nat.eq_zero_or_pos D with hD | hD
  · subst hD; funext s; exact s.elim0
  have key : ∀ s, s ≤ D → sweepVal nor (proj w) s = w ((s : Fin (D + 1)) - 1) := by
    intro s
    induction s with
    | zero =>
      intro _
      simp only [sweepVal, rowGet, proj, Nat.cast_zero]
      rw [dif_pos (by omega)]
      congr 1
      ext
      simp [Fin.val_sub]
      omega
    | succ s ih =>
      intro hs
      simp only [sweepVal]
      rw [ih (by omega)]
      simp only [rowGet, proj]
      rw [dif_pos (by omega)]
      have hloc := tiling_local hw (s : Fin (D + 1))
      have e1 : ((s + 1 : ℕ) : Fin (D + 1)) - 1 = (s : Fin (D + 1)) := by
        push_cast; abel
      have e2 : (⟨s, by omega⟩ : Fin D).succ = (s : Fin (D + 1)) + 1 := by
        rw [← Nat.cast_one (R := Fin (D + 1)), ← Nat.cast_add]
        ext
        rw [Fin.val_natCast, Fin.val_succ, Nat.mod_eq_of_lt (by omega)]
      rw [e1, e2, hloc]
  funext s
  simp only [sweep, proj, rotR]
  rw [key _ (by omega)]
  have e3 : ((s.val + 1 : ℕ) : Fin (D + 1)) = s.succ := by
    ext
    rw [Fin.val_natCast, Fin.val_succ, Nat.mod_eq_of_lt (by omega)]
  rw [e3]

lemma sweep_iterate_proj_tiling {w : Fin (D + 1) → Bool} (hw : IsTiling w) (k : ℕ) :
    (sweep nor)^[k] (proj w) = proj ((rotR)^[k] w) := by
  induction k generalizing w with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, sweep_proj_tiling hw, ih (rotR_tiling hw),
      Function.iterate_succ_apply]

end Cyclic

/-! ### Two-sweep landing and the orbit structure -/

/-- **Lemma 3.3 (two-sweep landing).** For every `D ≥ 1` and every row `x`, `F_D²(x)` is the
projection of a cyclic tiling. -/
theorem two_sweep_landing {D : ℕ} (hD : 1 ≤ D) (x : Fin D → Bool) :
    ∃ w : Fin (D + 1) → Bool, IsTiling w ∧ (sweep nor)^[2] x = proj w := by
  set y := lagSeq nor D x
  have hy : IsLagSeq nor D y := lagSeq_isLagSeq nor hD x
  refine ⟨fun j => y (2 * D - 1 + j.val), ?_, ?_⟩
  · intro i
    have hw := nor_window hD hy (2 * D - 1 + i.val) (by omega)
    have e1 : y (2 * D - 1 + (i + 1 : Fin (D + 1)).val) = y (2 * D - 1 + i.val + 1) := by
      rw [show ((i + 1 : Fin (D + 1)) : ℕ) = (i.val + 1) % (D + 1) by
          rw [Fin.val_add]; simp [Fin.val_one', Nat.add_mod_mod],
        nor_periodic_mod hD hy]; rfl
    have e2 : y (2 * D - 1 + (i + 2 : Fin (D + 1)).val) = y (2 * D - 1 + i.val + 2) := by
      have : ((i + 2 : Fin (D + 1)) : ℕ) = (i.val + 2) % (D + 1) := by
        have := fin_val_add_nat i 2
        simpa using this
      rw [this, nor_periodic_mod hD hy]; rfl
    simp only
    rw [e1, e2]
    exact hw
  · rw [← lagSeq_row_zero nor x, ← lagSeq_rows_iterate nor hD hy]
    funext s
    simp only [rowOf, proj, Fin.val_succ]
    congr 1
    omega

/-- **Theorem 3.4, second part.** `F_D^{D+1}(F_D²(x)) = F_D²(x)` for every row `x`: every orbit
of `F_D` has preperiod at most `2` and period dividing `D + 1`. -/
theorem sweep_orbit {D : ℕ} (hD : 1 ≤ D) (x : Fin D → Bool) :
    (sweep nor)^[D + 1] ((sweep nor)^[2] x) = (sweep nor)^[2] x := by
  obtain ⟨w, hw, hx⟩ := two_sweep_landing hD x
  rw [hx, sweep_iterate_proj_tiling hw, rotR_iterate_period]

/-- **Corollary 3.5 (periodicity of the lag sequence).** Let `x` be a uniform-lag NOR sequence
with arbitrary first `D` values and let `w ∈ 𝒯_{D+1}` with `π(w) = (x_{2D}, …, x_{3D-1})`. Then
`x_i = w_{(i+3) mod (D+1)}` for all `i ≥ 2D`, and `x_{i+D+1} = x_i` for all `i ≥ 2D`. -/
theorem nor_lag_sequence_tiling {D : ℕ} (hD : 1 ≤ D) {x : ℕ → Bool} (hx : IsLagSeq nor D x)
    {w : Fin (D + 1) → Bool} (hw : IsTiling w) (hproj : proj w = rowOf D x 2) :
    (∀ i, 2 * D ≤ i → x i = w ((i + 3 : ℕ) : Fin (D + 1))) ∧
      (∀ i, 2 * D ≤ i → x (i + D + 1) = x i) := by
  refine ⟨?_, fun i hi => nor_periodic hD hx i (by omega)⟩
  -- the word read off the sequence from index `2D - 1`
  set w' : Fin (D + 1) → Bool := fun j => x (2 * D - 1 + j.val) with hw'def
  have hw' : IsTiling w' := by
    intro i
    have hwin := nor_window hD hx (2 * D - 1 + i.val) (by omega)
    have e1 : x (2 * D - 1 + (i + 1 : Fin (D + 1)).val) = x (2 * D - 1 + i.val + 1) := by
      have : ((i + 1 : Fin (D + 1)) : ℕ) = (i.val + 1) % (D + 1) := by
        have := fin_val_add_nat i 1; simpa using this
      rw [this, nor_periodic_mod hD hx]; rfl
    have e2 : x (2 * D - 1 + (i + 2 : Fin (D + 1)).val) = x (2 * D - 1 + i.val + 2) := by
      have : ((i + 2 : Fin (D + 1)) : ℕ) = (i.val + 2) % (D + 1) := by
        have := fin_val_add_nat i 2; simpa using this
      rw [this, nor_periodic_mod hD hx]; rfl
    simp only [hw'def]
    rw [e1, e2]
    exact hwin
  have hpw' : proj w' = rowOf D x 2 := by
    funext s
    simp only [proj, rowOf, hw'def, Fin.val_succ]
    congr 1; omega
  have hww' : w = w' := proj_injOn hw hw' (hproj.trans hpw'.symm)
  intro i hi
  rw [hww']
  simp only [hw'def, Fin.val_natCast]
  rw [nor_periodic_mod hD hx]
  have : 2 * D - 1 + (i + 3) % (D + 1) = 2 * D - 1 + (i - (2 * D - 1)) % (D + 1) := by
    congr 1
    rw [show i + 3 = (i - (2 * D - 1)) + 2 * (D + 1) by omega, Nat.add_mul_mod_self_right]
  rw [← nor_periodic_mod hD hx, this, nor_periodic_mod hD hx]
  congr 1; omega

end GC.Tabulation
