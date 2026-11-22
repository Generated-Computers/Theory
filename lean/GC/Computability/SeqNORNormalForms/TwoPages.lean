import GC.Computability.SeqNORNormalForms.Basic

/-!
# 006a: alternating-direction NOR/OR arrays and the serpentine two-page compilation

Definition 7.1, the sources of a cell (equation (sources) of Section 7.4), the instance `Φ` of Section 7.4 (Table 2), Lemmas 7.6,
7.7 (values), 7.8, 7.9, 7.10 and Theorem 7.11 (two pages).
-/

namespace GC.SeqNORNormalForms

/-- The six cell types of an alternating-direction array. -/
inductive CellType
  | N | C | X | Y | R | O
  deriving DecidableEq, Repr

namespace CellType

/-- Value of a cell from `a = v(t-1,s)` and `b = v(t-1,σ(t,s))`. -/
def eval : CellType → Bool → Bool → Bool
  | N, a, _ => !a
  | C, a, _ => a
  | X, _, b => !b
  | Y, _, b => b
  | R, a, b => nor a b
  | O, a, b => a || b

/-- The types that read the neighbour. -/
def readsNbr : CellType → Bool
  | X => true
  | Y => true
  | R => true
  | O => true
  | _ => false

/-- OR-type cells (`C`, `Y`, `O`); the others are NOR-type. -/
def isOr : CellType → Bool
  | C => true
  | Y => true
  | O => true
  | _ => false

end CellType

/-- The neighbour column `σ(t,s)`: `s - 1` on odd layers, `s + 1` on even layers. -/
def nbr (t s : ℕ) : ℕ := if t % 2 = 1 then s - 1 else s + 1

/-- An alternating-direction NOR/OR array of width `k` and depth `d` (Definition 7.1):
constants `init s = v(0,s)` on layer `0` and a type for every cell `(t,s)`, `t ≥ 1`. -/
structure NorOrArray where
  k : ℕ
  d : ℕ
  init : ℕ → Bool
  type : ℕ → ℕ → CellType

/-- Well-formedness: `k, d ≥ 1`, and types reading the neighbour only where
`0 ≤ σ(t,s) < k`. -/
def NorOrArray.Valid (A : NorOrArray) : Prop :=
  1 ≤ A.k ∧ 1 ≤ A.d ∧
    ∀ t s, 1 ≤ t → t ≤ A.d → s < A.k → (A.type t s).readsNbr = true →
      (t % 2 = 1 → 1 ≤ s) ∧ (t % 2 = 0 → s + 1 < A.k)

/-- The value `v(t,s)` of a cell. -/
def NorOrArray.val (A : NorOrArray) : ℕ → ℕ → Bool
  | 0, s => A.init s
  | t + 1, s => (A.type (t + 1) s).eval (A.val t s) (A.val t (nbr (t + 1) s))

/-- First source `π` of a cell (equation (sources) of 006a, Section 7.4). -/
def src1 (ty : CellType) (t s : ℕ) : ℕ :=
  match ty with
  | CellType.X => nbr t s
  | CellType.Y => nbr t s
  | _ => s

/-- Second source `κ` of a cell (equation (sources) of 006a, Section 7.4). -/
def src2 (ty : CellType) (t s : ℕ) : ℕ :=
  match ty with
  | CellType.N => s
  | CellType.C => s
  | _ => nbr t s

/-- Index `e` of cell `(t,s)` in the emission order of layer `t` (serpentine order: odd
layers right to left, even layers left to right). -/
def emitIdx (k t s : ℕ) : ℕ := if t % 2 = 1 then k - 1 - s else s

/-- Start `c(t,s) = 2 + 2k + 8 (k (t-1) + e)` of the block of cell `(t,s)`. -/
def blockStart (k t s : ℕ) : ℕ := 2 + 2 * k + 8 * (k * (t - 1) + emitIdx k t s)

/-- The output position `o(t,s)`. -/
def NorOrArray.out (A : NorOrArray) : ℕ → ℕ → ℕ
  | 0, s => if A.init s then 2 + 2 * s else 2 + 2 * s + 1
  | t + 1, s => blockStart A.k (t + 1) s + (if (A.type (t + 1) s).isOr then 5 else 4)

/-- Start `m = 2 + 2k + 8kd` of the tail. -/
def NorOrArray.tailStart (A : NorOrArray) : ℕ := 2 + 2 * A.k + 8 * (A.k * A.d)

/-- The length `n = m + 3` of `Φ`. -/
def NorOrArray.len (A : NorOrArray) : ℕ := A.tailStart + 3

/-- Parent of position `c + r` (`r < 8`) inside block number `b` (Table 2); the block
belongs to the cell `(t,s)` emitted `e`-th in layer `t`, with `b = k (t-1) + e`. -/
def NorOrArray.blockEntry (A : NorOrArray) (b r : ℕ) : ℕ :=
  let t := b / A.k + 1
  let e := b % A.k
  let s := if t % 2 = 1 then A.k - 1 - e else e
  let c := 2 + 2 * A.k + 8 * b
  let ty := A.type t s
  if r = 0 then A.out (t - 1) (src1 ty t s)
  else if r ≤ 3 then c
  else if r = 4 then A.out (t - 1) (src2 ty t s)
  else if r = 5 then c + 4
  else c + 5

/-- The instance `Φ` of Section 7.4: positions `0,1` with `j_1 = 0`; constant blocks
`j_c = c-1, j_{c+1} = c` at `c = 2 + 2s`; one 8-position block per cell in serpentine
order; the tail `j_m = o(d, s_out)`, `j_{m+1} = j_{m+2} = j_{m+3} = m`. -/
def NorOrArray.serp (A : NorOrArray) (sout : ℕ) (i : ℕ) : ℕ :=
  if i < 2 then 0
  else if i < 2 + 2 * A.k then i - 1
  else if i < A.tailStart then
    A.blockEntry ((i - (2 + 2 * A.k)) / 8) ((i - (2 + 2 * A.k)) % 8)
  else if i = A.tailStart then A.out A.d sout
  else A.tailStart

/-- The two-page assignment of Theorem 7.11 (page `0` is the paper's page 1): transition
arcs (entering `c` or `c+4` of a block) of odd layers and all short arcs on page `0`,
transition arcs of even layers on page `1`, the tail arc on page `0` iff `d` is even. -/
def NorOrArray.page (A : NorOrArray) (i : ℕ) : Fin 2 :=
  if 2 + 2 * A.k ≤ i ∧ i < A.tailStart ∧
      ((i - (2 + 2 * A.k)) % 8 = 0 ∨ (i - (2 + 2 * A.k)) % 8 = 4) then
    (if ((i - (2 + 2 * A.k)) / 8 / A.k + 1) % 2 = 1 then 0 else 1)
  else if i = A.tailStart then (if A.d % 2 = 0 then 0 else 1)
  else 0

/-! ### The block of Table 2 (Lemma 7.6) -/

/-- **Lemma 7.6.** If `p, q < c` and `x_{c-1} = 0`, the block of Table 2 has
`x_{c+4} = NOR(x_p, x_q)`, `x_{c+5} = x_p ∨ x_q` and `x_{c+7} = 0`. -/
theorem block_values (j : ℕ → ℕ) (c p q : ℕ) (hc : 1 ≤ c) (hp : p < c) (hq : q < c)
    (h0 : j c = p) (h1 : j (c + 1) = c) (h2 : j (c + 2) = c) (h3 : j (c + 3) = c)
    (h4 : j (c + 4) = q) (h5 : j (c + 5) = c + 4) (h6 : j (c + 6) = c + 5)
    (h7 : j (c + 7) = c + 5) (hz : trace j (c - 1) = false) :
    trace j (c + 4) = nor (trace j p) (trace j q) ∧
      trace j (c + 5) = (trace j p || trace j q) ∧ trace j (c + 7) = false := by
  have e0 := trace_step j c p hc h0 hp
  have e1 := trace_step j (c + 1) c (by omega) h1 (by omega)
  have e2 := trace_step j (c + 2) c (by omega) h2 (by omega)
  have e3 := trace_step j (c + 3) c (by omega) h3 (by omega)
  have e4 := trace_step j (c + 4) q (by omega) h4 (by omega)
  have e5 := trace_step j (c + 5) (c + 4) (by omega) h5 (by omega)
  have e6 := trace_step j (c + 6) (c + 5) (by omega) h6 (by omega)
  have e7 := trace_step j (c + 7) (c + 5) (by omega) h7 (by omega)
  simp only [show c + 1 - 1 = c by omega, show c + 2 - 1 = c + 1 by omega,
    show c + 3 - 1 = c + 2 by omega, show c + 4 - 1 = c + 3 by omega,
    show c + 5 - 1 = c + 4 by omega, show c + 6 - 1 = c + 5 by omega,
    show c + 7 - 1 = c + 6 by omega] at e1 e2 e3 e4 e5 e6 e7
  rw [hz] at e0
  rw [e7, e6, e5, e4, e3, e2, e1, e0]
  cases trace j p <;> cases trace j q <;> simp [nor]

/-! ### Arithmetic of the layout -/

/-- Start of the region of layer `t ≥ 1`. -/
def layerBase (k t : ℕ) : ℕ := 2 + 2 * k + 8 * (k * (t - 1))

theorem emitIdx_lt {k t s : ℕ} (hs : s < k) : emitIdx k t s < k := by
  unfold emitIdx; split <;> omega

theorem blockStart_eq (k t s : ℕ) : blockStart k t s = layerBase k t + 8 * emitIdx k t s := by
  unfold blockStart layerBase; ring

theorem layerBase_succ (k t : ℕ) (ht : 1 ≤ t) : layerBase k (t + 1) = layerBase k t + 8 * k := by
  unfold layerBase
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  simp [Nat.mul_succ]; ring

theorem layerBase_mono (k : ℕ) {t t' : ℕ} (h : t ≤ t') : layerBase k t ≤ layerBase k t' := by
  unfold layerBase
  have : k * (t - 1) ≤ k * (t' - 1) := Nat.mul_le_mul_left _ (by omega)
  omega

theorem layerBase_one (k : ℕ) : layerBase k 1 = 2 + 2 * k := by simp [layerBase]

theorem tailStart_eq (A : NorOrArray) : A.tailStart = layerBase A.k (A.d + 1) := by
  simp [NorOrArray.tailStart, layerBase]

/-- Block index of the cell `(t,s)`. -/
def cellIdx (k t s : ℕ) : ℕ := k * (t - 1) + emitIdx k t s

theorem blockStart_cellIdx (k t s : ℕ) : blockStart k t s = 2 + 2 * k + 8 * cellIdx k t s := rfl

theorem cellIdx_div {k t s : ℕ} (hs : s < k) : cellIdx k t s / k = t - 1 := by
  have hk : 0 < k := by omega
  unfold cellIdx
  rw [show k * (t - 1) + emitIdx k t s = emitIdx k t s + k * (t - 1) by ring,
    Nat.add_mul_div_left _ _ hk, Nat.div_eq_of_lt (emitIdx_lt hs)]
  simp

theorem cellIdx_mod {k t s : ℕ} (hs : s < k) : cellIdx k t s % k = emitIdx k t s := by
  unfold cellIdx
  rw [show k * (t - 1) + emitIdx k t s = emitIdx k t s + k * (t - 1) by ring,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (emitIdx_lt hs)]

theorem cellIdx_lt {k d t s : ℕ} (hs : s < k) (ht : t ≤ d) (ht1 : 1 ≤ t) :
    cellIdx k t s < k * d := by
  unfold cellIdx
  have h1 := emitIdx_lt (t := t) hs
  have : k * (t - 1) + k ≤ k * d := by
    rw [show k * (t - 1) + k = k * (t - 1 + 1) by ring]
    exact Nat.mul_le_mul_left _ (by omega)
  omega

/-- Decoding a block index `b < k d` gives back a cell. -/
theorem decode_cell {k d b : ℕ} (hk : 1 ≤ k) (hb : b < k * d) :
    let t := b / k + 1
    let e := b % k
    let s := if t % 2 = 1 then k - 1 - e else e
    1 ≤ t ∧ t ≤ d ∧ s < k ∧ cellIdx k t s = b := by
  intro t e s
  have he : e < k := Nat.mod_lt _ (by omega)
  have hdiv : b / k < d := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]; rw [Nat.mul_comm]; exact hb
  have hs : s < k := by simp only [s]; split <;> omega
  refine ⟨Nat.le_add_left _ _, by show b / k + 1 ≤ d; omega, hs, ?_⟩
  have hem : emitIdx k t s = e := by
    unfold emitIdx; simp only [s]; split_ifs <;> omega
  unfold cellIdx; rw [hem]
  simp only [t, e, Nat.add_sub_cancel]
  exact Nat.div_add_mod b k

/-- The cell of block index `cellIdx k t s` is `(t,s)`. -/
theorem cell_of_cellIdx {k t s : ℕ} (hs : s < k) (ht : 1 ≤ t) :
    cellIdx k t s / k + 1 = t ∧
      (if (cellIdx k t s / k + 1) % 2 = 1 then k - 1 - cellIdx k t s % k
        else cellIdx k t s % k) = s := by
  rw [cellIdx_div hs, cellIdx_mod hs]
  refine ⟨by omega, ?_⟩
  rw [show t - 1 + 1 = t by omega]
  unfold emitIdx; split <;> omega

/-! ### Decoding `Φ` -/

section Decode

variable (A : NorOrArray) (sout : ℕ)

theorem serp_one : A.serp sout 1 = 0 := by simp [NorOrArray.serp]

theorem serp_const {i : ℕ} (h2 : 2 ≤ i) (hi : i < 2 + 2 * A.k) : A.serp sout i = i - 1 := by
  unfold NorOrArray.serp; rw [if_neg (by omega), if_pos hi]

theorem serp_block {b r : ℕ} (hb : b < A.k * A.d) (hr : r < 8) :
    A.serp sout (2 + 2 * A.k + 8 * b + r) = A.blockEntry b r := by
  unfold NorOrArray.serp
  rw [if_neg (by omega), if_neg (by omega),
    if_pos (by unfold NorOrArray.tailStart; omega)]
  congr 1 <;> omega

theorem serp_tail : A.serp sout A.tailStart = A.out A.d sout := by
  unfold NorOrArray.serp
  rw [if_neg (by unfold NorOrArray.tailStart; omega), if_neg (by unfold NorOrArray.tailStart; omega),
    if_neg (lt_irrefl _), if_pos rfl]

theorem serp_tail' {r : ℕ} (hr1 : 1 ≤ r) : A.serp sout (A.tailStart + r) = A.tailStart := by
  unfold NorOrArray.serp
  rw [if_neg (by unfold NorOrArray.tailStart; omega), if_neg (by unfold NorOrArray.tailStart; omega),
    if_neg (by omega), if_neg (by omega)]

/-- The eight parents of the block of cell `(t,s)` (Table 2). -/
theorem serp_cell {t s : ℕ} (hk : 1 ≤ A.k) (ht1 : 1 ≤ t) (ht : t ≤ A.d) (hs : s < A.k) :
    let c := blockStart A.k t s
    let ty := A.type t s
    A.serp sout c = A.out (t - 1) (src1 ty t s) ∧ A.serp sout (c + 1) = c ∧
    A.serp sout (c + 2) = c ∧ A.serp sout (c + 3) = c ∧
    A.serp sout (c + 4) = A.out (t - 1) (src2 ty t s) ∧ A.serp sout (c + 5) = c + 4 ∧
    A.serp sout (c + 6) = c + 5 ∧ A.serp sout (c + 7) = c + 5 := by
  intro c ty
  have hb := cellIdx_lt (d := A.d) hs ht ht1
  obtain ⟨hT, hS⟩ := cell_of_cellIdx hs ht1
  have key : ∀ r, r < 8 → A.serp sout (c + r) = A.blockEntry (cellIdx A.k t s) r := by
    intro r hr
    have := serp_block A sout hb hr
    simpa [c, blockStart_cellIdx] using this
  have hc : c = 2 + 2 * A.k + 8 * cellIdx A.k t s := rfl
  rw [hT] at hS
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := key 0 (by omega); simp only [Nat.add_zero] at this
    rw [this]; unfold NorOrArray.blockEntry; simp only [hT, hS]; simp [ty]
  · rw [key 1 (by omega)]; unfold NorOrArray.blockEntry; simp [hc]
  · rw [key 2 (by omega)]; unfold NorOrArray.blockEntry; simp [hc]
  · rw [key 3 (by omega)]; unfold NorOrArray.blockEntry; simp [hc]
  · rw [key 4 (by omega)]; unfold NorOrArray.blockEntry; simp only [hT, hS]; simp [ty]
  · rw [key 5 (by omega)]; unfold NorOrArray.blockEntry; simp [hc]
  · rw [key 6 (by omega)]; unfold NorOrArray.blockEntry; simp [hc]
  · rw [key 7 (by omega)]; unfold NorOrArray.blockEntry; simp [hc]

end Decode


theorem decode_cell' {k d b : ℕ} (hk : 1 ≤ k) (hb : b < k * d) :
    ∃ t s, 1 ≤ t ∧ t ≤ d ∧ s < k ∧ cellIdx k t s = b :=
  ⟨_, _, decode_cell hk hb⟩

/-! ### Sources -/

theorem src1_cases (ty : CellType) (t s : ℕ) : src1 ty t s = s ∨ src1 ty t s = nbr t s := by
  cases ty <;> simp [src1]

theorem src2_cases (ty : CellType) (t s : ℕ) : src2 ty t s = s ∨ src2 ty t s = nbr t s := by
  cases ty <;> simp [src2]

/-- A binary cell reads its own column through its first source: if the first source is the
neighbour, so is the second. -/
theorem src_pair (ty : CellType) (t s : ℕ) : src1 ty t s ≠ s → src2 ty t s = src1 ty t s := by
  cases ty <;> simp [src1, src2]

theorem src_lt (A : NorOrArray) (hA : A.Valid) {t s : ℕ} (ht1 : 1 ≤ t) (ht : t ≤ A.d)
    (hs : s < A.k) : src1 (A.type t s) t s < A.k ∧ src2 (A.type t s) t s < A.k := by
  have hv := hA.2.2 t s ht1 ht hs
  refine ⟨?_, ?_⟩ <;> cases h : A.type t s <;>
    simp [src1, src2, nbr, CellType.readsNbr, h] at hv ⊢ <;> (try split_ifs) <;> omega

/-- The value of a cell through its sources: `NOR` of the sources for NOR-type cells, `OR`
for OR-type cells. -/
theorem val_succ_src (A : NorOrArray) (t s : ℕ) :
    A.val (t + 1) s =
      if (A.type (t + 1) s).isOr then
        (A.val t (src1 (A.type (t + 1) s) (t + 1) s) || A.val t (src2 (A.type (t + 1) s) (t + 1) s))
      else nor (A.val t (src1 (A.type (t + 1) s) (t + 1) s))
        (A.val t (src2 (A.type (t + 1) s) (t + 1) s)) := by
  simp only [NorOrArray.val]
  cases A.type (t + 1) s <;> simp [CellType.eval, CellType.isOr, src1, src2, nor] <;>
    cases A.val t s <;> simp

/-! ### Values (Lemma 7.7) -/

section Values

variable (A : NorOrArray) (sout : ℕ)

theorem out_lt (hk : 1 ≤ A.k) {t u : ℕ} (hu : u < A.k) : A.out t u < layerBase A.k (t + 1) := by
  cases t with
  | zero => simp only [NorOrArray.out, zero_add, layerBase_one]; split <;> omega
  | succ t =>
    simp only [NorOrArray.out]
    rw [blockStart_eq, layerBase_succ A.k (t + 1) (by omega)]
    have := emitIdx_lt (k := A.k) (t := t + 1) hu
    split <;> omega

theorem out_ge {t u : ℕ} (ht : 1 ≤ t) : layerBase A.k t + 4 ≤ A.out t u := by
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  simp only [NorOrArray.out]
  rw [blockStart_eq]
  split <;> omega

theorem out_mono_even {t u u' : ℕ} (ht : t % 2 = 0) (hu : u < u') (hu' : u' < A.k) :
    A.out t u < A.out t u' := by
  cases t with
  | zero => simp only [NorOrArray.out]; split_ifs <;> omega
  | succ t =>
    simp only [NorOrArray.out, blockStart_eq, emitIdx]
    split_ifs <;> omega

theorem out_mono_odd {t u u' : ℕ} (ht : t % 2 = 1) (hu : u < u') (hu' : u' < A.k) :
    A.out t u' < A.out t u := by
  cases t with
  | zero => omega
  | succ t =>
    simp only [NorOrArray.out, blockStart_eq, emitIdx]
    split_ifs <;> omega

theorem trace_const (hk : 1 ≤ A.k) :
    ∀ i, 1 ≤ i → i < 2 + 2 * A.k → trace (A.serp sout) i = decide (i % 2 = 0) := by
  intro i
  induction i with
  | zero => intro h; omega
  | succ i ih =>
    intro h1 h2
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [trace_step _ 1 0 le_rfl (serp_one A sout) (by omega)]; simp [trace_zero, nor]
    · rw [trace_step _ (i + 1) i (by omega)
        (by rw [serp_const A sout (by omega) h2]; omega) (by omega)]
      simp only [Nat.add_sub_cancel]
      rw [ih (by omega) (by omega)]
      by_cases h : i % 2 = 0
      · simp [nor, h]; omega
      · simp [nor, h]; omega

theorem trace_zero_before (hA : A.Valid) :
    ∀ b, b ≤ A.k * A.d → trace (A.serp sout) (2 + 2 * A.k + 8 * b - 1) = false := by
  intro b
  induction b with
  | zero =>
    intro _
    have := trace_const A sout hA.1 (2 * A.k + 1) (by omega) (by omega)
    rw [show 2 + 2 * A.k + 8 * 0 - 1 = 2 * A.k + 1 by omega, this]
    simp
  | succ b ih =>
    intro hb
    obtain ⟨t, s, ht1, htd, hs, hcell⟩ := decode_cell' hA.1 (show b < A.k * A.d by omega)
    have hc : blockStart A.k t s = 2 + 2 * A.k + 8 * b := by rw [blockStart_cellIdx, hcell]
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := serp_cell A sout hA.1 ht1 htd hs
    obtain ⟨hs1, hs2⟩ := src_lt A hA ht1 htd hs
    have hp := out_lt A hA.1 (t := t - 1) hs1
    have hq := out_lt A hA.1 (t := t - 1) hs2
    rw [show t - 1 + 1 = t by omega] at hp hq
    have hlb : layerBase A.k t ≤ blockStart A.k t s := by rw [blockStart_eq]; omega
    rw [hc] at h0 h1 h2 h3 h4 h5 h6 h7 hlb
    have hv := block_values (A.serp sout) _ _ _ (by omega) (by omega) (by omega)
      h0 h1 h2 h3 h4 h5 h6 h7 (ih (by omega))
    rw [show 2 + 2 * A.k + 8 * (b + 1) - 1 = 2 + 2 * A.k + 8 * b + 7 by omega]
    exact hv.2.2

/-- **Lemma 7.7 (values).** `x_{o(t,s)} = v(t,s)` for every cell. -/
theorem trace_out (hA : A.Valid) :
    ∀ t, t ≤ A.d → ∀ s, s < A.k → trace (A.serp sout) (A.out t s) = A.val t s := by
  intro t
  induction t with
  | zero =>
    intro _ s hs
    simp only [NorOrArray.out, NorOrArray.val]
    split
    · next h => rw [trace_const A sout hA.1 _ (by omega) (by omega)]; simp [h]
    · next h => rw [trace_const A sout hA.1 _ (by omega) (by omega)]; simp [h]; omega
  | succ t ih =>
    intro htd s hs
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := serp_cell A sout hA.1 (t := t + 1) (by omega) htd hs
    obtain ⟨hs1, hs2⟩ := src_lt A hA (t := t + 1) (by omega) htd hs
    have hp := out_lt A hA.1 (t := t) hs1
    have hq := out_lt A hA.1 (t := t) hs2
    have hlb : layerBase A.k (t + 1) ≤ blockStart A.k (t + 1) s := by rw [blockStart_eq]; omega
    have hz : trace (A.serp sout) (blockStart A.k (t + 1) s - 1) = false := by
      rw [blockStart_cellIdx]
      exact trace_zero_before A sout hA _ (le_of_lt (cellIdx_lt hs htd (by omega)))
    simp only [Nat.add_sub_cancel] at h0 h4
    have hv := block_values (A.serp sout) _ _ _ (by omega) (by omega) (by omega)
      h0 h1 h2 h3 h4 h5 h6 h7 hz
    rw [ih (by omega) _ hs1, ih (by omega) _ hs2] at hv
    rw [val_succ_src]
    simp only [NorOrArray.out]
    split
    · exact hv.2.1
    · exact hv.1

/-- **Lemma 7.7 (output).** `x_n = v(d, s_out)`. -/
theorem trace_len (hA : A.Valid) (hs : sout < A.k) :
    trace (A.serp sout) A.len = A.val A.d sout := by
  have hz : trace (A.serp sout) (A.tailStart - 1) = false := by
    have := trace_zero_before A sout hA (A.k * A.d) le_rfl
    simpa [NorOrArray.tailStart] using this
  have ho := trace_out A sout hA A.d le_rfl sout hs
  have hlt := out_lt A hA.1 (t := A.d) hs
  rw [← tailStart_eq] at hlt
  have hm1 : 1 ≤ A.tailStart := by unfold NorOrArray.tailStart; omega
  have e0 := trace_step (A.serp sout) A.tailStart _ hm1 (serp_tail A sout) hlt
  have e1 := trace_step (A.serp sout) (A.tailStart + 1) _ (by omega)
    (serp_tail' A sout (r := 1) le_rfl) (by omega)
  have e2 := trace_step (A.serp sout) (A.tailStart + 2) _ (by omega)
    (serp_tail' A sout (r := 2) (by omega)) (by omega)
  have e3 := trace_step (A.serp sout) (A.tailStart + 3) _ (by omega)
    (serp_tail' A sout (r := 3) (by omega)) (by omega)
  simp only [Nat.add_sub_cancel, show A.tailStart + 2 - 1 = A.tailStart + 1 by omega,
    show A.tailStart + 3 - 1 = A.tailStart + 2 by omega] at e1 e2 e3
  rw [hz, ho] at e0
  unfold NorOrArray.len
  rw [e3, e2, e1, e0]
  cases A.val A.d sout <;> simp [nor]

/-- Every position `1 ≤ i ≤ n` is position `1`, in a constant block, in a cell block, or in
the tail. -/
theorem pos_cases (hk : 1 ≤ A.k) (i : ℕ) (h1 : 1 ≤ i) (hn : i ≤ A.len) :
    i = 1 ∨ (2 ≤ i ∧ i < 2 + 2 * A.k) ∨
      (∃ t s r, 1 ≤ t ∧ t ≤ A.d ∧ s < A.k ∧ r < 8 ∧ i = blockStart A.k t s + r) ∨
      (∃ r, r ≤ 3 ∧ i = A.tailStart + r) := by
  by_cases hi1 : i = 1
  · exact Or.inl hi1
  by_cases hi2 : i < 2 + 2 * A.k
  · exact Or.inr (Or.inl ⟨by omega, hi2⟩)
  by_cases hi3 : i < A.tailStart
  · refine Or.inr (Or.inr (Or.inl ?_))
    have hb : (i - (2 + 2 * A.k)) / 8 < A.k * A.d := by
      unfold NorOrArray.tailStart at hi3; omega
    obtain ⟨t, s, ht1, htd, hs, hcell⟩ := decode_cell' hk hb
    refine ⟨t, s, (i - (2 + 2 * A.k)) % 8, ht1, htd, hs, Nat.mod_lt _ (by omega), ?_⟩
    rw [blockStart_cellIdx, hcell]; omega
  · refine Or.inr (Or.inr (Or.inr ⟨i - A.tailStart, ?_, ?_⟩)) <;>
      unfold NorOrArray.len at hn <;> omega

/-- `Φ` is a parent array. -/
theorem serp_isParentArray (hA : A.Valid) (hs : sout < A.k) :
    IsParentArray A.len (A.serp sout) := by
  intro i h1 hn
  rcases pos_cases A hA.1 i h1 hn with rfl | ⟨h2, h3⟩ | ⟨t, s, r, ht1, htd, hs', hr, rfl⟩ |
      ⟨r, hr, rfl⟩
  · rw [serp_one]; omega
  · rw [serp_const A sout h2 h3]; omega
  · obtain ⟨h0, e1, e2, e3, h4, e5, e6, e7⟩ := serp_cell A sout hA.1 ht1 htd hs'
    obtain ⟨hs1, hs2⟩ := src_lt A hA ht1 htd hs'
    have hp := out_lt A hA.1 (t := t - 1) hs1
    have hq := out_lt A hA.1 (t := t - 1) hs2
    rw [show t - 1 + 1 = t by omega] at hp hq
    have hlb : layerBase A.k t ≤ blockStart A.k t s := by rw [blockStart_eq]; omega
    interval_cases r
    · simp only [Nat.add_zero]; rw [h0]; omega
    · rw [e1]; omega
    · rw [e2]; omega
    · rw [e3]; omega
    · rw [h4]; omega
    · rw [e5]; omega
    · rw [e6]; omega
    · rw [e7]; omega
  · have hlt := out_lt A hA.1 (t := A.d) hs
    rw [← tailStart_eq] at hlt
    interval_cases r
    · simp only [Nat.add_zero]; rw [serp_tail]; exact hlt
    all_goals rw [serp_tail' A sout (by omega)]; omega

end Values


/-! ### Pages (Lemmas 7.8–7.10, Theorem 7.11) -/

/-- Source column of the transition arc entering position `c(t,s) + r` (`r = 0` or `4`). -/
def NorOrArray.arcSrc (A : NorOrArray) (t s r : ℕ) : ℕ :=
  if r = 0 then src1 (A.type t s) t s else src2 (A.type t s) t s

/-- Positions that occur as parents in `Φ`. -/
def NorOrArray.ParentPos (A : NorOrArray) (y : ℕ) : Prop :=
  y < 2 + 2 * A.k ∨
    (2 + 2 * A.k ≤ y ∧ y < A.tailStart ∧
      ((y - (2 + 2 * A.k)) % 8 = 0 ∨ (y - (2 + 2 * A.k)) % 8 = 4 ∨
        (y - (2 + 2 * A.k)) % 8 = 5)) ∨
    y = A.tailStart

section Pages

variable (A : NorOrArray) (sout : ℕ)

theorem arcSrc_lt (hA : A.Valid) {t s r : ℕ} (ht1 : 1 ≤ t) (ht : t ≤ A.d) (hs : s < A.k) :
    A.arcSrc t s r < A.k := by
  have := src_lt A hA ht1 ht hs
  unfold NorOrArray.arcSrc; split
  · exact this.1
  · exact this.2

theorem arcSrc_cases (t s r : ℕ) : A.arcSrc t s r = s ∨ A.arcSrc t s r = nbr t s := by
  unfold NorOrArray.arcSrc; split
  · exact src1_cases _ _ _
  · exact src2_cases _ _ _

theorem arcSrc_pair (t s : ℕ) : A.arcSrc t s 0 ≠ s → A.arcSrc t s 4 = A.arcSrc t s 0 := by
  unfold NorOrArray.arcSrc; simp only [if_true, show (4 : ℕ) ≠ 0 by decide, if_false]
  exact src_pair _ _ _

theorem blockStart_lt (hk : 1 ≤ A.k) {t s : ℕ} (hs : s < A.k) (ht1 : 1 ≤ t) :
    blockStart A.k t s + 7 < layerBase A.k (t + 1) := by
  rw [blockStart_eq, layerBase_succ _ _ ht1]
  have := emitIdx_lt (k := A.k) (t := t) hs
  omega

theorem out_parentPos (hk : 1 ≤ A.k) {t u : ℕ} (ht : t ≤ A.d) (hu : u < A.k) :
    A.ParentPos (A.out t u) := by
  cases t with
  | zero =>
    left; simp only [NorOrArray.out]; split <;> omega
  | succ t =>
    right; left
    have hb := cellIdx_lt (d := A.d) (t := t + 1) hu ht (by omega)
    simp only [NorOrArray.out, blockStart_cellIdx, NorOrArray.tailStart]
    split <;> omega

/-- **Lemma 7.8, first half.** Every parent of `Φ` is a constant-block position, a position
`c`, `c+4` or `c+5` of a block, or `m`. -/
theorem serp_parentPos (hA : A.Valid) (hs : sout < A.k) (i : ℕ) (h1 : 1 ≤ i)
    (hn : i ≤ A.len) : A.ParentPos (A.serp sout i) := by
  rcases pos_cases A hA.1 i h1 hn with rfl | ⟨h2, h3⟩ | ⟨t, s, r, ht1, htd, hs', hr, rfl⟩ |
      ⟨r, hr, rfl⟩
  · rw [serp_one]; left; omega
  · rw [serp_const A sout h2 h3]; left; omega
  · obtain ⟨h0, e1, e2, e3, h4, e5, e6, e7⟩ := serp_cell A sout hA.1 ht1 htd hs'
    obtain ⟨hs1, hs2⟩ := src_lt A hA ht1 htd hs'
    have hb := cellIdx_lt (d := A.d) hs' htd ht1
    have hP : ∀ r', r' = 0 ∨ r' = 4 ∨ r' = 5 → A.ParentPos (blockStart A.k t s + r') := by
      intro r' hr'
      right; left
      simp only [blockStart_cellIdx, NorOrArray.tailStart]
      omega
    interval_cases r
    · simp only [Nat.add_zero]; rw [h0]; exact out_parentPos A hA.1 (by omega) hs1
    · rw [e1]; simpa using hP 0 (by omega)
    · rw [e2]; simpa using hP 0 (by omega)
    · rw [e3]; simpa using hP 0 (by omega)
    · rw [h4]; exact out_parentPos A hA.1 (by omega) hs2
    · rw [e5]; exact hP 4 (by omega)
    · rw [e6]; exact hP 5 (by omega)
    · rw [e7]; exact hP 5 (by omega)
  · interval_cases r
    · simp only [Nat.add_zero]; rw [serp_tail]; exact out_parentPos A hA.1 le_rfl hs
    all_goals rw [serp_tail' A sout (by omega)]; right; right; rfl

theorem page_trans (hk : 1 ≤ A.k) {t s r : ℕ} (ht1 : 1 ≤ t) (ht : t ≤ A.d) (hs : s < A.k)
    (hr : r = 0 ∨ r = 4) :
    A.page (blockStart A.k t s + r) = if t % 2 = 1 then 0 else 1 := by
  have hb := cellIdx_lt (d := A.d) hs ht ht1
  obtain ⟨hT, -⟩ := cell_of_cellIdx hs ht1
  unfold NorOrArray.page
  have e1 : blockStart A.k t s + r - (2 + 2 * A.k) = 8 * cellIdx A.k t s + r := by
    rw [blockStart_cellIdx]; omega
  rw [if_pos (by rw [e1]; refine ⟨by rw [blockStart_cellIdx]; omega,
    by rw [blockStart_cellIdx]; unfold NorOrArray.tailStart; omega, by omega⟩), e1,
    show (8 * cellIdx A.k t s + r) / 8 = cellIdx A.k t s by omega, hT]

theorem page_other (i : ℕ) (hi : i ≠ A.tailStart)
    (hnt : ¬ (2 + 2 * A.k ≤ i ∧ i < A.tailStart ∧
      ((i - (2 + 2 * A.k)) % 8 = 0 ∨ (i - (2 + 2 * A.k)) % 8 = 4))) : A.page i = 0 := by
  unfold NorOrArray.page; rw [if_neg hnt, if_neg hi]

theorem page_tail : A.page A.tailStart = if A.d % 2 = 0 then 0 else 1 := by
  unfold NorOrArray.page; rw [if_neg (by omega), if_pos rfl]

/-- Classification of the arcs of `Φ` into short arcs, transition arcs and the tail arc,
with their pages. For a short arc `(j_i, i)`, every position strictly inside it has the same
parent and is not a parent of any position (this is the content of Lemma 7.8). -/
theorem classify (hA : A.Valid) (i : ℕ) (h1 : 1 ≤ i) (hn : i ≤ A.len) :
    (A.page i = 0 ∧ ∀ y, A.serp sout i < y → y < i →
        A.serp sout y = A.serp sout i ∧ ¬ A.ParentPos y) ∨
    (∃ t s r, 1 ≤ t ∧ t ≤ A.d ∧ s < A.k ∧ (r = 0 ∨ r = 4) ∧ i = blockStart A.k t s + r ∧
      A.serp sout i = A.out (t - 1) (A.arcSrc t s r) ∧
      A.page i = if t % 2 = 1 then 0 else 1) ∨
    (i = A.tailStart ∧ A.serp sout i = A.out A.d sout ∧
      A.page i = if A.d % 2 = 0 then 0 else 1) := by
  have hk := hA.1
  have htail : 2 + 2 * A.k ≤ A.tailStart := by unfold NorOrArray.tailStart; omega
  rcases pos_cases A hA.1 i h1 hn with rfl | ⟨h2, h3⟩ | ⟨t, s, r, ht1, htd, hs', hr, rfl⟩ |
      ⟨r, hr, rfl⟩
  · left
    refine ⟨page_other A 1 (by omega) (by omega), ?_⟩
    intro y hy1 hy2; rw [serp_one] at hy1; omega
  · left
    refine ⟨page_other A i (by omega) (by omega), ?_⟩
    intro y hy1 hy2; rw [serp_const A sout h2 h3] at hy1; omega
  · obtain ⟨h0, e1, e2, e3, h4, e5, e6, e7⟩ := serp_cell A sout hA.1 ht1 htd hs'
    have hb := cellIdx_lt (d := A.d) hs' htd ht1
    have hc := blockStart_cellIdx A.k t s
    have hts : A.tailStart = 2 + 2 * A.k + 8 * (A.k * A.d) := rfl
    have hnot : ∀ r', r' = 1 ∨ r' = 2 ∨ r' = 6 → ¬ A.ParentPos (blockStart A.k t s + r') := by
      intro r' hr' hP
      unfold NorOrArray.ParentPos at hP
      rw [hc] at hP
      omega
    have hpo : ∀ r', r' < 8 → r' ≠ 0 → r' ≠ 4 → A.page (blockStart A.k t s + r') = 0 := by
      intro r' hr' h0 h4
      apply page_other
      · omega
      · rw [hc]; omega
    by_cases hr04 : r = 0 ∨ r = 4
    · right; left
      refine ⟨t, s, r, ht1, htd, hs', hr04, rfl, ?_, page_trans A hk ht1 htd hs' hr04⟩
      rcases hr04 with rfl | rfl
      · simpa [NorOrArray.arcSrc] using h0
      · simpa [NorOrArray.arcSrc] using h4
    · left
      refine ⟨hpo r hr (by omega) (by omega), ?_⟩
      intro y hy1 hy2
      interval_cases r
      · omega
      · rw [e1] at hy1; omega
      · rw [e2] at hy1 ⊢
        obtain rfl : y = blockStart A.k t s + 1 := by omega
        exact ⟨e1, hnot 1 (by omega)⟩
      · rw [e3] at hy1 ⊢
        rcases (show y = blockStart A.k t s + 1 ∨ y = blockStart A.k t s + 2 by omega) with
          rfl | rfl
        · exact ⟨e1, hnot 1 (by omega)⟩
        · exact ⟨e2, hnot 2 (by omega)⟩
      · omega
      · rw [e5] at hy1; omega
      · rw [e6] at hy1; omega
      · rw [e7] at hy1 ⊢
        obtain rfl : y = blockStart A.k t s + 6 := by omega
        exact ⟨e6, hnot 6 (by omega)⟩
  · interval_cases r
    · right; right
      exact ⟨by simp, by simpa using serp_tail A sout, by simpa using page_tail A⟩
    all_goals
      left
      refine ⟨page_other A _ (by omega) (by omega), ?_⟩
      intro y hy1 hy2
      rw [serp_tail' A sout (by omega)] at hy1 ⊢
      refine ⟨serp_tail' A sout (r := y - A.tailStart) (by omega) ▸ by congr 1; omega, ?_⟩
      unfold NorOrArray.ParentPos; omega

/-- **Lemma 7.8.** A short arc crosses no arc of `Φ`. -/
theorem short_noncross {a b a' b' : ℕ} (P : ℕ → Prop) (j : ℕ → ℕ) (hab : j b = a)
    (hshort : ∀ y, a < y → y < b → j y = a ∧ ¬ P y) (hb' : j b' = a') (hP : P a') :
    ¬ Cross a b a' b' := by
  rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
  · exact (hshort a' h1 h2).2 hP
  · have := (hshort b' h2 h3).1; omega

theorem noncross_of_lt {a b a' b' : ℕ} (h : b < a') : ¬ Cross a b a' b' := by
  unfold Cross; omega

/-- The key inequality of Lemma 7.9: within one layer, a transition arc with a smaller source
has a larger entry. -/
theorem trans_key (hA : A.Valid) {t sa sb ra rb : ℕ} (ht1 : 1 ≤ t) (ht : t ≤ A.d)
    (hsa : sa < A.k) (hsb : sb < A.k) (hra : ra = 0 ∨ ra = 4) (hrb : rb = 0 ∨ rb = 4)
    (hlt : A.out (t - 1) (A.arcSrc t sa ra) < A.out (t - 1) (A.arcSrc t sb rb)) :
    blockStart A.k t sb + rb < blockStart A.k t sa + ra := by
  have hua := arcSrc_lt A hA (r := ra) ht1 ht hsa
  have hub := arcSrc_lt A hA (r := rb) ht1 ht hsb
  have hca := arcSrc_cases A t sa ra
  have hcb := arcSrc_cases A t sb rb
  have hpair : sa = sb → ra = 0 → rb = 4 → A.arcSrc t sa ra ≠ sa →
      A.arcSrc t sb rb = A.arcSrc t sa ra := by
    rintro rfl rfl rfl h; exact arcSrc_pair A t sa h
  have hsame : sa = sb → ra = rb → A.arcSrc t sa ra = A.arcSrc t sb rb := by
    rintro rfl rfl; rfl
  generalize A.arcSrc t sa ra = ua at *
  generalize A.arcSrc t sb rb = ub at *
  rw [blockStart_eq, blockStart_eq]
  unfold emitIdx
  unfold nbr at hca hcb
  rcases Nat.mod_two_eq_zero_or_one t with hpar | hpar
  · -- even layer: layer `t-1` is odd, emitted right to left
    have hu : ub < ua := by
      rcases lt_trichotomy ua ub with h | h | h
      · exact absurd hlt (not_lt.2 (le_of_lt (out_mono_odd A (by omega) h hub)))
      · rw [h] at hlt; exact absurd hlt (lt_irrefl _)
      · exact h
    simp only [hpar, show (0 : ℕ) ≠ 1 by decide, if_false] at hca hcb ⊢
    omega
  · -- odd layer: layer `t-1` is even, emitted left to right
    have hu : ua < ub := by
      rcases lt_trichotomy ua ub with h | h | h
      · exact h
      · rw [h] at hlt; exact absurd hlt (lt_irrefl _)
      · exact absurd hlt (not_lt.2 (le_of_lt (out_mono_even A (by omega) h hua)))
    simp only [hpar, if_true] at hca hcb ⊢
    omega

/-- **Lemma 7.9.** The transition arcs of one layer are pairwise non-crossing. -/
theorem trans_same_layer (hA : A.Valid) {t sa sb ra rb : ℕ} (ht1 : 1 ≤ t) (ht : t ≤ A.d)
    (hsa : sa < A.k) (hsb : sb < A.k) (hra : ra = 0 ∨ ra = 4) (hrb : rb = 0 ∨ rb = 4) :
    ¬ Cross (A.out (t - 1) (A.arcSrc t sa ra)) (blockStart A.k t sa + ra)
      (A.out (t - 1) (A.arcSrc t sb rb)) (blockStart A.k t sb + rb) := by
  rintro (⟨h1, -, h3⟩ | ⟨h1, -, h3⟩)
  · have := trans_key A hA ht1 ht hsa hsb hra hrb h1; omega
  · have := trans_key A hA ht1 ht hsb hsa hrb hra h1; omega

/-- **Lemma 7.10.** Transition arcs of layers `t` and `t' ≥ t + 2` do not cross: all of the
first lies before all of the second. -/
theorem trans_far (hA : A.Valid) {t t' s r u : ℕ} (ht1 : 1 ≤ t) (hs : s < A.k)
    (hr : r = 0 ∨ r = 4) (htt : t + 2 ≤ t') (ht' : t' ≤ A.d + 1) :
    blockStart A.k t s + r < A.out (t' - 1) u := by
  have h1 := blockStart_lt A hA.1 hs ht1
  have h2 := layerBase_mono A.k (show t + 1 ≤ t' - 1 by omega)
  have h3 := out_ge A (t := t' - 1) (u := u) (by omega)
  omega

/-- **Theorem 7.11 (pages).** The explicit assignment `A.page` is a two-page assignment of
`Φ`. -/
theorem serp_pageAssignment (hA : A.Valid) (hs : sout < A.k) :
    IsPageAssignment A.len (A.serp sout) 2 A.page := by
  have hpar : ∀ i, 1 ≤ i → i ≤ A.len → A.ParentPos (A.serp sout i) :=
    serp_parentPos A sout hA hs
  intro i i' h1 hn h1' hn' hpage
  rcases classify A sout hA i h1 hn with ⟨-, hsh⟩ | hti | hti
  · exact short_noncross A.ParentPos (A.serp sout) rfl hsh rfl (hpar i' h1' hn')
  rcases classify A sout hA i' h1' hn' with ⟨-, hsh⟩ | hti' | hti'
  · exact fun h => short_noncross A.ParentPos (A.serp sout) rfl hsh rfl (hpar i h1 hn)
      (cross_symm h)
  · obtain ⟨t, s, r, ht1, htd, hs1, hr, rfl, hj, hp⟩ := hti
    obtain ⟨t', s', r', ht1', htd', hs1', hr', rfl, hj', hp'⟩ := hti'
    rw [hj, hj']
    rw [hp, hp'] at hpage
    have hpar' : t % 2 = t' % 2 := by
      split_ifs at hpage <;> first | omega | exact absurd hpage (by decide)
    rcases lt_trichotomy t t' with h | rfl | h
    · exact noncross_of_lt (trans_far A hA ht1 hs1 hr (by omega) (by omega))
    · exact trans_same_layer A hA ht1 htd hs1 hs1' hr hr'
    · exact fun hc => noncross_of_lt (trans_far A hA ht1' hs1' hr' (by omega) (by omega))
        (cross_symm hc)
  · obtain ⟨t, s, r, ht1, htd, hs1, hr, rfl, hj, hp⟩ := hti
    obtain ⟨rfl, hj', hp'⟩ := hti'
    rw [hj, hj']
    rw [hp, hp'] at hpage
    have htd' : t + 1 ≤ A.d := by
      split_ifs at hpage <;> first | omega | exact absurd hpage (by decide)
    exact noncross_of_lt (by
      have := trans_far A hA (u := sout) ht1 hs1 hr (show t + 2 ≤ A.d + 1 by omega) le_rfl
      simpa using this)
  · obtain ⟨rfl, hj, hp⟩ := hti
    rcases classify A sout hA i' h1' hn' with ⟨-, hsh⟩ | hti' | hti'
    · exact fun h => short_noncross A.ParentPos (A.serp sout) rfl hsh rfl (hpar _ h1 hn)
        (cross_symm h)
    · obtain ⟨t, s, r, ht1, htd, hs1, hr, rfl, hj', hp'⟩ := hti'
      rw [hj, hj']
      rw [hp, hp'] at hpage
      have htd' : t + 1 ≤ A.d := by
        split_ifs at hpage <;> first | omega | exact absurd hpage (by decide)
      exact fun hc => noncross_of_lt (by
        have := trans_far A hA (u := sout) ht1 hs1 hr (show t + 2 ≤ A.d + 1 by omega) le_rfl
        simpa using this) (cross_symm hc)
    · obtain ⟨rfl, -, -⟩ := hti'
      unfold Cross; omega

end Pages

/-- **Theorem 7.11 of 006a (serpentine compilation).** For every well-formed
alternating-direction NOR/OR array `A` and output column `s_out < k`, the instance
`Φ = A.serp s_out` of length `n = 2 + 2k + 8kd + 3` is a parent array, its trace satisfies
`x_{o(t,s)} = v(t,s)` for every cell and `x_n = v(d, s_out)`, and `A.page` (transition arcs of
odd layers and all short arcs on one page, transition arcs of even layers on the other, the
tail arc according to the parity of `d`) is a two-page assignment; in particular
`pg(Φ) ≤ 2`. -/
theorem serpentine_two_pages (A : NorOrArray) (hA : A.Valid) (sout : ℕ) (hs : sout < A.k) :
    IsParentArray A.len (A.serp sout) ∧
    (∀ t s, t ≤ A.d → s < A.k → trace (A.serp sout) (A.out t s) = A.val t s) ∧
    trace (A.serp sout) A.len = A.val A.d sout ∧
    IsPageAssignment A.len (A.serp sout) 2 A.page ∧
    PageNumberLE A.len (A.serp sout) 2 :=
  ⟨serp_isParentArray A sout hA hs, fun t s ht hs' => trace_out A sout hA t ht s hs',
    trace_len A sout hA hs, serp_pageAssignment A sout hA hs,
    ⟨A.page, serp_pageAssignment A sout hA hs⟩⟩

end GC.SeqNORNormalForms
