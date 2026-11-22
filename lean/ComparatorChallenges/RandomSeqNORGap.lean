import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Ring.Pow

/-! Comparator challenge for manuscript 001b (A Gap Theorem for P versus BPNC). Definitions are copied verbatim from
the solution files; theorems are stated with `sorry`. -/

namespace GC.RandomSeqNOR

/-- A Sequential NOR instance (infinite pointer sequence): gate `i ≥ 1` reads `i - 1` and `j i`,
with `j i < i`. The value `j 0` is irrelevant. -/
structure Inst where
  /-- The pointer of gate `i`. -/
  j : ℕ → ℕ
  /-- Pointers go strictly backwards. -/
  j_lt : ∀ i, 0 < i → j i < i

/-- The trace `x*` of an instance: `x*₀ = 1`, `x*ᵢ = (1 + x*ᵢ₋₁)(1 + x*_{jᵢ})`. -/
def trace (P : Inst) : ℕ → ZMod 2
  | 0 => 1
  | i + 1 => (1 + trace P i) * (1 + trace P (P.j (i + 1)))
termination_by i => i
decreasing_by
  · omega
  · exact P.j_lt (i + 1) (Nat.succ_pos i)

/-- `NOR` over `GF(2)`: `NOR(a, b) = (1 + a)(1 + b)`. -/
def nor (a b : ZMod 2) : ZMod 2 := (1 + a) * (1 + b)

/-- Majority over `GF(2)`: `MAJ(a, b, c) = ab + bc + ca`. -/
def maj (a b c : ZMod 2) : ZMod 2 := a * b + b * c + c * a

open Finset

/-- The law of one coordinate of the `ε`-smoothing: the pointer of gate `i` (with values in
`{0, …, i-1}`) is kept (`= j`) with probability `1 - ε` and resampled uniformly with probability
`ε`. `smoothKernel ε i j w` is the probability that the new pointer is `w`. -/
noncomputable def smoothKernel (ε : ℝ) (i j w : ℕ) : ℝ :=
  (1 - ε) * (if w = j then 1 else 0) + ε / i

/-- The law of the `ε`-smoothing of a base `j` of length `n`, as a function on parent arrays
`w` (with `w i ∈ {0, …, i}` the pointer of gate `i + 1`): the product of the one-coordinate laws
(the coordinates are independent). -/
noncomputable def smoothLaw (n : ℕ) (ε : ℝ) (j w : (i : Fin n) → Fin (i.1 + 1)) : ℝ :=
  ∏ i, smoothKernel ε (i.1 + 1) (j i) (w i)

/-- Gates `k, …, k+3` carry the pointers `(0, a, 1, b)` of the gadget `N(a, b)`. -/
def CarriesN (P : Inst) (k a b : ℕ) : Prop :=
  P.j k = 0 ∧ P.j (k + 1) = a ∧ P.j (k + 2) = 1 ∧ P.j (k + 3) = b

/-- Gates `k, …, k+7` carry the pointers `(0, a, 1, b, b, k+1, c, k+3)` of the gadget
`M(a, b, c)`. -/
def CarriesM (P : Inst) (k a b c : ℕ) : Prop :=
  P.j k = 0 ∧ P.j (k + 1) = a ∧ P.j (k + 2) = 1 ∧ P.j (k + 3) = b ∧ P.j (k + 4) = b ∧
    P.j (k + 5) = k + 1 ∧ P.j (k + 6) = c ∧ P.j (k + 7) = k + 3

/-- Gates `k, …, k+5` carry the pointers `(a, a, c, k+1, b, k)` of the gadget `M'(a, b, c)`. -/
def CarriesM' (P : Inst) (k a b c : ℕ) : Prop :=
  P.j k = a ∧ P.j (k + 1) = a ∧ P.j (k + 2) = c ∧ P.j (k + 3) = k + 1 ∧ P.j (k + 4) = b ∧
    P.j (k + 5) = k

/-- Number of gates of a cell of depth `h`: `4` for a leaf, and `3 S + 8` for an internal node. -/
def cellSize : ℕ → ℕ
  | 0 => 4
  | h + 1 => 3 * cellSize h + 8

/-- The listed pointer of gate `k + o` of a cell of depth `h` starting at position `k` whose
leaf `λ` is `N(leafIn λ)`. Children are laid out first (post-order), then the `M` gadget
`M(a, b, c)` with `a, b, c` the last gates of the three children. -/
def cellPtr : ℕ → ℕ → (ℕ → ℕ × ℕ) → ℕ → ℕ
  | 0, _, leafIn, o =>
    if o = 0 then 0 else if o = 1 then (leafIn 0).1 else if o = 2 then 1 else (leafIn 0).2
  | h + 1, k, leafIn, o =>
    if o < cellSize h then cellPtr h k leafIn o
    else if o < 2 * cellSize h then
      cellPtr h (k + cellSize h) (fun l => leafIn (3 ^ h + l)) (o - cellSize h)
    else if o < 3 * cellSize h then
      cellPtr h (k + 2 * cellSize h) (fun l => leafIn (2 * 3 ^ h + l)) (o - 2 * cellSize h)
    else if o - 3 * cellSize h = 0 then 0
    else if o - 3 * cellSize h = 1 then k + cellSize h - 1
    else if o - 3 * cellSize h = 2 then 1
    else if o - 3 * cellSize h = 3 then k + 2 * cellSize h - 1
    else if o - 3 * cellSize h = 4 then k + 2 * cellSize h - 1
    else if o - 3 * cellSize h = 5 then k + 3 * cellSize h + 1
    else if o - 3 * cellSize h = 6 then k + 3 * cellSize h - 1
    else k + 3 * cellSize h + 3

/-- The event `D(ν)` of Step 1 for the root of a cell of depth `h` at `k`, when the leaves should
compute `NOR(va, vb)`: for a leaf, the gadget does not carry its listed pointers or one of its
inputs is wrong; for an internal node, the `M` gadget does not carry its listed pointers or `D`
holds for at least two children. (Not carrying the listed pointers is implied by being hit.) -/
def cellBad (P : Inst) (va vb : ZMod 2) : ℕ → ℕ → (ℕ → ℕ × ℕ) → Prop
  | 0, k, leafIn =>
    ¬ CarriesN P k (leafIn 0).1 (leafIn 0).2 ∨ trace P (leafIn 0).1 ≠ va ∨
      trace P (leafIn 0).2 ≠ vb
  | h + 1, k, leafIn =>
    ¬ CarriesM P (k + 3 * cellSize h) (k + cellSize h - 1) (k + 2 * cellSize h - 1)
        (k + 3 * cellSize h - 1) ∨
      (cellBad P va vb h k leafIn ∧
          cellBad P va vb h (k + cellSize h) (fun l => leafIn (3 ^ h + l))) ∨
      (cellBad P va vb h (k + cellSize h) (fun l => leafIn (3 ^ h + l)) ∧
          cellBad P va vb h (k + 2 * cellSize h) (fun l => leafIn (2 * 3 ^ h + l))) ∨
      (cellBad P va vb h k leafIn ∧
          cellBad P va vb h (k + 2 * cellSize h) (fun l => leafIn (2 * 3 ^ h + l)))

/-- A wire of a NOR circuit: a constant `c_b` or an earlier gate. -/
inductive Wire
  | const (b : ZMod 2)
  | gate (t : ℕ)

/-- A NOR circuit: gate `t` computes `NOR(u t, v t)`, whose gate inputs are earlier gates. -/
structure NORCircuit where
  /-- First input of gate `t`. -/
  u : ℕ → Wire
  /-- Second input of gate `t`. -/
  v : ℕ → Wire
  u_lt : ∀ t t', u t = Wire.gate t' → t' < t
  v_lt : ∀ t t', v t = Wire.gate t' → t' < t

/-- The value of gate `t` of a NOR circuit. -/
def NORCircuit.val (C : NORCircuit) (t : ℕ) : ZMod 2 :=
  nor
    (match hu : C.u t with
      | Wire.const b => b
      | Wire.gate t' => C.val t')
    (match hv : C.v t with
      | Wire.const b => b
      | Wire.gate t' => C.val t')
termination_by t
decreasing_by
  · exact C.u_lt t t' hu
  · exact C.v_lt t t' hv

/-- The value carried by a wire. -/
def NORCircuit.wireVal (C : NORCircuit) : Wire → ZMod 2
  | Wire.const b => b
  | Wire.gate t' => C.val t'

/-- First position of the cell `𝒞(t, ℓ)` (gate `0` and gate `1` come first). -/
def cellStart (h m t ℓ : ℕ) : ℕ := 2 + (t * m + ℓ) * cellSize h

/-- The output position `o(t, ℓ)` of the cell `𝒞(t, ℓ)`. -/
def compOut (h m t ℓ : ℕ) : ℕ := cellStart h m t ℓ + cellSize h - 1

/-- The position read for a wire from copy `r`: `o(c₁, r) = 0`, `o(c₀, r) = 1`, and
`o(g_{t'}, r)` for a gate. -/
def wirePos (h m : ℕ) : Wire → ℕ → ℕ
  | Wire.const b, _ => if b = 1 then 0 else 1
  | Wire.gate t', r => compOut h m t' r

/-- The leaf inputs of `𝒞(t, ℓ)`: leaf `λ` is `N(o(u_t, r), o(v_t, r'))` with
`(r, r') = coin t ℓ λ`. -/
def leafInputs (C : NORCircuit) (h m : ℕ) (coin : ℕ → ℕ → ℕ → Fin m × Fin m) (t ℓ : ℕ) :
    ℕ → ℕ × ℕ :=
  fun l => (wirePos h m (C.u t) (coin t ℓ l).1, wirePos h m (C.v t) (coin t ℓ l).2)

/-- The compiled pointer array `Comp(C)` for a circuit with `s` gates, cells of depth `h`, bundles
of size `m`, and coins `coin` (positions beyond the last cell are filled with NOT gates). -/
def compPtr (C : NORCircuit) (h m s : ℕ) (coin : ℕ → ℕ → ℕ → Fin m × Fin m) (p : ℕ) : ℕ :=
  if p < 2 then 0
  else if (p - 2) / cellSize h < s * m then
    cellPtr h (2 + (p - 2) / cellSize h * cellSize h)
      (leafInputs C h m coin ((p - 2) / cellSize h / m) ((p - 2) / cellSize h % m))
      ((p - 2) % cellSize h)
  else p - 1

/-- The compiled pointers point backwards. -/
theorem compPtr_lt (C : NORCircuit) (h m s : ℕ) (coin : ℕ → ℕ → ℕ → Fin m × Fin m) :
    ∀ p, 0 < p → compPtr C h m s coin p < p := by
  sorry

/-- The compiled instance `Comp(C)`, a valid parent array. -/
def compInst (C : NORCircuit) (h m s : ℕ) (coin : ℕ → ℕ → ℕ → Fin m × Fin m) : Inst :=
  ⟨compPtr C h m s coin, compPtr_lt C h m s coin⟩

/-- `φ(q) = 3q² - 2q³`, the probability that at least two of three independent events of
probability `q` occur. -/
def phi (q : ℝ) : ℝ := 3 * q ^ 2 - 2 * q ^ 3

/-- The conditional probabilities `q_l` of Step 2 of Theorem 3.5. -/
def qSeq (ε βu βv : ℝ) : ℕ → ℝ
  | 0 => 1 - (1 - ε) ^ 4 * (1 - βu) * (1 - βv)
  | l + 1 => 1 - (1 - ε) ^ 8 * (1 - phi (qSeq ε βu βv l))

/-- **Lemma 3.3 (one coordinate).** Applying `S_{ε'}` and then `S_ε` gives the law of
`S_{ε''}` with `1 - ε'' = (1 - ε)(1 - ε')`. -/
theorem smoothKernel_comp (ε ε' : ℝ) {i j v : ℕ} (hi : 0 < i) (hj : j < i) (hv : v < i) :
    ∑ w ∈ range i, smoothKernel ε' i j w * smoothKernel ε i w v =
      smoothKernel (1 - (1 - ε) * (1 - ε')) i j v := by
  sorry

/-- **Lemma 3.3.** `S_ε(S_{ε'}(j))` has the law of `S_{ε''}(j)`, where
`1 - ε'' = (1 - ε)(1 - ε')`: for every base `j` and array `v`,
`∑_w Pr[S_{ε'}(j) = w] Pr[S_ε(w) = v] = Pr[S_{ε''}(j) = v]`. -/
theorem smoothLaw_comp (n : ℕ) (ε ε' : ℝ) (j v : (i : Fin n) → Fin (i.1 + 1)) :
    ∑ w, smoothLaw n ε' j w * smoothLaw n ε w v = smoothLaw n (1 - (1 - ε) * (1 - ε')) j v := by
  sorry

/-- **Lemma 3.3, second claim (the noise levels form an up-set).** For `ε ≤ ε'' ≤ 1` there is
`ε' ∈ [0, 1]` with `1 - ε'' = (1 - ε)(1 - ε')`; so `S_{ε''} = S_ε ∘ S_{ε'}`. -/
theorem smoothing_upset {ε ε'' : ℝ} (h1 : ε ≤ ε'') (h2 : ε'' ≤ 1) :
    ∃ ε' : ℝ, 0 ≤ ε' ∧ ε' ≤ 1 ∧ ε'' = 1 - (1 - ε) * (1 - ε') := by
  sorry

/-- **Lemma 3.4 (gadget `N`).** If gates `k, …, k+3` carry `N(a, b)`, then
`x*_{k+3} = NOR(x*_a, x*_b)`, whatever `x*_{k-1}`. -/
theorem gadget_N (P : Inst) {k a b : ℕ} (hk : 1 ≤ k) (h : CarriesN P k a b) :
    trace P (k + 3) = nor (trace P a) (trace P b) := by
  sorry

/-- **Lemma 3.4 (gadget `M`).** If gates `k, …, k+7` carry `M(a, b, c)`, then
`x*_{k+7} = MAJ(x*_a, x*_b, x*_c)`, whatever `x*_{k-1}`. -/
theorem gadget_M (P : Inst) {k a b c : ℕ} (hk : 1 ≤ k) (h : CarriesM P k a b c) :
    trace P (k + 7) = maj (trace P a) (trace P b) (trace P c) := by
  sorry

/-- **The 6-gate majority gadget `M'`.** If gates `k, …, k+5` carry `M'(a, b, c)` and
`c = k - 1`, then `x*_{k+5} = MAJ(x*_a, x*_b, x*_c)`, whatever the other values. -/
theorem gadget_M' (P : Inst) {k a b : ℕ} (hk : 1 ≤ k) (h : CarriesM' P k a b (k - 1)) :
    trace P (k + 5) = maj (trace P a) (trace P b) (trace P (k - 1)) := by
  sorry

/-- Density fact of Lemma 3.6 for `N`: a gadget `N` that carries its pointers has a one among its
four positions. -/
theorem gadget_N_has_one (P : Inst) {k a b : ℕ} (hk : 1 ≤ k) (h : CarriesN P k a b) :
    trace P (k + 1) = 1 ∨ trace P (k + 2) = 1 := by
  sorry

/-- Density fact of Lemma 3.6 for `M'`: a gadget `M'` (with `c = k - 1`) that carries its
pointers has at least two ones among its six positions, whatever `a, b, c`. -/
theorem gadget_M'_has_two_ones (P : Inst) {k a b : ℕ} (hk : 1 ≤ k)
    (h : CarriesM' P k a b (k - 1)) :
    2 ≤ ((range 6).filter (fun o => trace P (k + o) = 1)).card := by
  sorry

/-- **Step 1 of Theorem 3.5 (dominating events).** For every instance and every cell of depth `h`
starting at `k ≥ 1`: if `D(root)` fails, the output `x*_{k + S - 1}` equals `NOR(va, vb)`. -/
theorem cell_step1 (P : Inst) (va vb : ZMod 2) :
    ∀ h k (leafIn : ℕ → ℕ × ℕ), 1 ≤ k → ¬ cellBad P va vb h k leafIn →
      trace P (k + cellSize h - 1) = nor va vb := by
  sorry

/-- **Exactness of the unsmoothed embedding (Section 3.2).** For `ε = 0`, induction along the
layout gives `x*_{o(t,ℓ)} = val(g_t)` for all `t < s` and `ℓ < m`, whatever the coins. -/
theorem comp_exact (C : NORCircuit) (h m s : ℕ) (coin : ℕ → ℕ → ℕ → Fin m × Fin m) :
    ∀ t < s, ∀ ℓ < m, trace (compInst C h m s coin) (compOut h m t ℓ) = C.val t := by
  sorry

/-- **Step 1 of Theorem 3.5 for the compiled layout.** For every instance `P` (for instance every
outcome of the smoothing of `Comp(C)`), if the output of `𝒞(t, ℓ)` is bad, i.e.
`x*_{o(t,ℓ)} ≠ val(g_t)`, then the event `D(root 𝒞(t, ℓ))` holds; at the leaves, a wrong input is
exactly a bad input cell (constants are never bad). -/
theorem comp_step1 (C : NORCircuit) (h m : ℕ) (coin : ℕ → ℕ → ℕ → Fin m × Fin m) (P : Inst)
    (t ℓ : ℕ) (hbad : trace P (compOut h m t ℓ) ≠ C.val t) :
    cellBad P (C.wireVal (C.u t)) (C.wireVal (C.v t)) h (cellStart h m t ℓ)
      (leafInputs C h m coin t ℓ) := by
  sorry

/-- **Theorem 3.5, Step 3.** For `ε ≤ 1/1000` and `β_u, β_v ≤ 1/10`:
`q₀ ≤ 0.204`, `q₁ ≤ 0.11587`, `q₂ ≤ 0.04517`, `q₃ ≤ 0.01394 = q̄`. -/
theorem embed_step3 {ε βu βv : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 1000) (hu0 : 0 ≤ βu)
    (hu : βu ≤ 1 / 10) (hv0 : 0 ≤ βv) (hv : βv ≤ 1 / 10) :
    qSeq ε βu βv 0 ≤ 0.204 ∧ qSeq ε βu βv 1 ≤ 0.11587 ∧ qSeq ε βu βv 2 ≤ 0.04517 ∧
      qSeq ε βu βv 3 ≤ 0.01394 := by
  sorry

/-- **Theorem 3.7, the ten iterations.** Let `ε ≤ 1/64` and let `q₀, …, q₁₀ ≥ 0` satisfy
`q₀ ≤ 1 - (1 - 2.931ε)(5/6)²` and `q_{l+1} ≤ 1 - (1 - 4.86ε)(1 - φ(q_l))`.
Then `q₁₀ ≤ q̄ = 0.1161`. -/
theorem embed64_ten_iterations {ε : ℝ} (hε : ε ≤ 1 / 64) (q : ℕ → ℝ)
    (hq0 : ∀ l, 0 ≤ q l)
    (h0 : q 0 ≤ 1 - (1 - 2.931 * ε) * (5 / 6) ^ 2)
    (hs : ∀ l, q (l + 1) ≤ 1 - (1 - 4.86 * ε) * (1 - phi (q l))) :
    q 10 ≤ 0.1161 := by
  sorry

end GC.RandomSeqNOR
