import Mathlib.Data.Nat.Find
import Mathlib.Order.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Fin.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Abel

/-!
# Comparator challenge: NOR shift registers are tiling rotations (010b)

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

/-- **Lemma 2.2.** The rows of a uniform-lag sequence satisfy `x^{(q+1)} = F_{G,D}(x^{(q)})`. -/
theorem lagSeq_rows (G : Bool → Bool → Bool) {D : ℕ} (hD : 1 ≤ D) {x : ℕ → Bool}
    (hx : IsLagSeq G D x) (q : ℕ) : rowOf D x (q + 1) = sweep G (rowOf D x q) := by
  sorry

/-- The uniform-lag sequence with first row `x0` (used to realize every row). -/
def lagSeq (G : Bool → Bool → Bool) (D : ℕ) (x0 : Fin D → Bool) : ℕ → Bool
  | i => if h : i < D ∨ D = 0 then rowGet x0 i else
      G (lagSeq G D x0 (i - 1)) (lagSeq G D x0 (i - D))
termination_by i => i
decreasing_by all_goals omega

section NorSeq

variable {D : ℕ} {x : ℕ → Bool}

/-- **Corollary 3.5 (periodicity), strengthened by one index.** For a uniform-lag NOR sequence
with arbitrary first values, `x_{i+D+1} = x_i` for all `i ≥ 2D - 1` (the paper states
`i ≥ 2D`). -/
theorem nor_periodic (hD : 1 ≤ D) (hx : IsLagSeq nor D x) :
    ∀ i, 2 * D - 1 ≤ i → x (i + D + 1) = x i := by
  sorry

end NorSeq

section Cyclic

variable {D : ℕ}

/-- **Lemma 3.2 (unique cyclic extension).** In a cyclic tiling, a coordinate is `1` iff both
cyclic neighbours are `0`. -/
theorem tiling_local {w : Fin (D + 1) → Bool} (hw : IsTiling w) (i : Fin (D + 1)) :
    w i = nor (w (i - 1)) (w (i + 1)) := by
  sorry

/-- `π` is injective on `𝒯_{D+1}` (Lemma 3.2). -/
theorem proj_injOn {w w' : Fin (D + 1) → Bool} (hw : IsTiling w) (hw' : IsTiling w')
    (h : proj w = proj w') : w = w' := by
  sorry

/-- **Theorem 3.4 (NOR tiling rotation).** For every `w ∈ 𝒯_{D+1}`, `F_D(π(w)) = π(ρ(w))`. -/
theorem sweep_proj_tiling {w : Fin (D + 1) → Bool} (hw : IsTiling w) :
    sweep nor (proj w) = proj (rotR w) := by
  sorry

end Cyclic

/-- **Lemma 3.3 (two-sweep landing).** For every `D ≥ 1` and every row `x`, `F_D²(x)` is the
projection of a cyclic tiling. -/
theorem two_sweep_landing {D : ℕ} (hD : 1 ≤ D) (x : Fin D → Bool) :
    ∃ w : Fin (D + 1) → Bool, IsTiling w ∧ (sweep nor)^[2] x = proj w := by
  sorry

/-- **Theorem 3.4, second part.** `F_D^{D+1}(F_D²(x)) = F_D²(x)` for every row `x`: every orbit
of `F_D` has preperiod at most `2` and period dividing `D + 1`. -/
theorem sweep_orbit {D : ℕ} (hD : 1 ≤ D) (x : Fin D → Bool) :
    (sweep nor)^[D + 1] ((sweep nor)^[2] x) = (sweep nor)^[2] x := by
  sorry

/-- **Corollary 3.5 (periodicity of the lag sequence).** Let `x` be a uniform-lag NOR sequence
with arbitrary first `D` values and let `w ∈ 𝒯_{D+1}` with `π(w) = (x_{2D}, …, x_{3D-1})`. Then
`x_i = w_{(i+3) mod (D+1)}` for all `i ≥ 2D`, and `x_{i+D+1} = x_i` for all `i ≥ 2D`. -/
theorem nor_lag_sequence_tiling {D : ℕ} (hD : 1 ≤ D) {x : ℕ → Bool} (hx : IsLagSeq nor D x)
    {w : Fin (D + 1) → Bool} (hw : IsTiling w) (hproj : proj w = rowOf D x 2) :
    (∀ i, 2 * D ≤ i → x i = w ((i + 3 : ℕ) : Fin (D + 1))) ∧
      (∀ i, 2 * D ≤ i → x (i + D + 1) = x i) := by
  sorry

end GC.Tabulation

namespace GC.Tabulation

/-- The complement conjugate `Ḡ(u, v) = ¬G(¬u, ¬v)`. -/
def conjGate (G : Bool → Bool → Bool) : Bool → Bool → Bool := fun u v => !(G (!u) (!v))

/-- `𝖢_D`: complement all bits of a row. -/
def cmpRow {D : ℕ} (x : Fin D → Bool) : Fin D → Bool := fun s => !(x s)

/-- **Lemma 4.1 (complement conjugation).** `F_{Ḡ,D} = 𝖢_D ∘ F_{G,D} ∘ 𝖢_D`. -/
theorem sweep_conjGate (G : Bool → Bool → Bool) {D : ℕ} (x : Fin D → Bool) :
    sweep (conjGate G) x = cmpRow (sweep G (cmpRow x)) := by
  sorry

/-- `P(u, v) = v ∧ ¬u`. -/
def gateP (u v : Bool) : Bool := v && !u

/-- `Q(u, v) = u ∧ ¬v`. -/
def gateQ (u v : Bool) : Bool := u && !v

/-- `A(u, v) = u ∧ v`. -/
def gateA (u v : Bool) : Bool := u && v

section Collapse

variable {D : ℕ}

/-- **Lemma 4.2, rule `P`.** `F_P² = F_P`. -/
theorem sweep_P_idem (x : Fin D → Bool) : sweep gateP (sweep gateP x) = sweep gateP x := by
  sorry

/-- **Lemma 4.2, rule `Q`.** `F_Q²(x) = 0^D`. -/
theorem sweep_Q_two (x : Fin D → Bool) :
    sweep gateQ (sweep gateQ x) = fun _ => false := by
  sorry

/-- **Lemma 4.2, rule `A`.** `F_A²(x) = 1^D` if `x = 1^D` and `0^D` otherwise. -/
theorem sweep_A_two (x : Fin D → Bool) :
    sweep gateA (sweep gateA x) =
      if x = (fun _ => true) then (fun _ => true) else (fun _ => false) := by
  sorry

/-- **Lemma 4.2, last claim.** For the six collapsing non-affine rules `P, Q, A` and their
complement conjugates, `F³ = F²`: every row from the second one on equals the second row. -/
theorem collapse_six (G : Bool → Bool → Bool)
    (hG : G = gateP ∨ G = gateQ ∨ G = gateA ∨
      G = conjGate gateP ∨ G = conjGate gateQ ∨ G = conjGate gateA) (x : Fin D → Bool) :
    (sweep G)^[3] x = (sweep G)^[2] x := by
  sorry

end Collapse

/-- Affine binary gates `αu ⊕ βv ⊕ γ`. -/
def IsAffineGate (G : Bool → Bool → Bool) : Prop :=
  ∃ α β γ : Bool, ∀ u v : Bool, G u v = xor (xor (α && u) (β && v)) γ

/-- The gate `NOR(u ⊕ a, v ⊕ b) ⊕ c` with polarity triple `(a, b, c)`. -/
def norPol (a b c : Bool) : Bool → Bool → Bool := fun u v => xor (nor (xor u a) (xor v b)) c

/-- **Lemma 5.1 (unique NOR polarity), existence part.** A binary gate is non-affine iff it is
`NOR(u ⊕ a, v ⊕ b) ⊕ c` for some triple `(a, b, c)`. -/
theorem nonaffine_iff_norPol (G : Bool → Bool → Bool) :
    ¬ IsAffineGate G ↔ ∃ a b c : Bool, G = norPol a b c := by
  sorry

/-- **Lemma 5.1, uniqueness part.** The polarity triple is unique. -/
theorem norPol_injective {a b c a' b' c' : Bool} (h : norPol a b c = norPol a' b' c') :
    a = a' ∧ b = b' ∧ c = c' := by
  sorry

/-- A uniform-lag grid with varying gates, in reading order: cell `i` (row `i / D`, column
`i % D + 1`) has west input `i - 1` and north input `i - D`. The rows `a + 1, …, b` form an
`H`-gauge-consistent slab with labels `η`, for `H = norPol A B C` (Definition 5.2): every gate in
them is `norPol (η_W ⊕ A) (η_N ⊕ B) (η ⊕ C)`. (By Lemma 5.1 this says that the gate is
non-affine with polarity triple `(η_W ⊕ A, η_N ⊕ B, η ⊕ C)`.) -/
def GaugeConsistent (D : ℕ) (Gs : ℕ → Bool → Bool → Bool) (A B C : Bool) (a b : ℕ)
    (η : ℕ → Bool) : Prop :=
  ∀ i, (a + 1) * D ≤ i → i < (b + 1) * D →
    Gs i = norPol (xor (η (i - 1)) A) (xor (η (i - D)) B) (xor (η i) C)

/-- **Theorem 5.3 (polarity-gauge conjugacy).** On an `H`-gauge-consistent slab of a uniform-lag
grid, the gauged values `z = x ⊕ η` form a homogeneous `H`-wavefront: each row of the slab is the
`H`-sweep of the previous row. -/
theorem gauge_conjugacy {D : ℕ} (hD : 1 ≤ D) (Gs : ℕ → Bool → Bool → Bool) (x η : ℕ → Bool)
    (A B C : Bool) (a b : ℕ) (hcons : GaugeConsistent D Gs A B C a b η)
    (hx : ∀ i, (a + 1) * D ≤ i → i < (b + 1) * D → x i = Gs i (x (i - 1)) (x (i - D))) :
    ∀ q, a ≤ q → q < b →
      rowOf D (fun i => xor (x i) (η i)) (q + 1) =
        sweep (norPol A B C) (rowOf D (fun i => xor (x i) (η i)) q) := by
  sorry

/-- A gauge piece: a single fallback row `(a, a + 1]`, or a slab that is `H`-gauge-consistent
for some non-affine target `H = norPol A B C` and some labels. -/
def GaugePiece (D : ℕ) (Gs : ℕ → Bool → Bool → Bool) (a b : ℕ) : Prop :=
  b = a + 1 ∨ ∃ (A B C : Bool) (η : ℕ → Bool), GaugeConsistent D Gs A B C a b η

/-- **Proposition 5.6 (finding a minimum cover), optimality part.** If rows `1, …, R` are covered
by `k` consecutive gauge pieces, the greedy cover (always taking the longest admissible next
piece) covers them with at most `k` pieces. -/
theorem gauge_greedy_optimal (D : ℕ) (Gs : ℕ → Bool → Bool → Bool) (R : ℕ) (c : ℕ → ℕ) (k : ℕ)
    (hc0 : c 0 = 0) (hck : c k = R)
    (hc : ∀ j < k, c j < c (j + 1) ∧ GaugePiece D Gs (c j) (c (j + 1))) :
    greedySeq (GaugePiece D Gs) R k = R := by
  sorry

end GC.Tabulation
