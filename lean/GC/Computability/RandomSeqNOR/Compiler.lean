import GC.Computability.RandomSeqNOR.Smoothing

/-!
# The noise-tolerant compiler (manuscript 001b, Section 3.2): deterministic core

A *cell* of depth `h` is a complete ternary tree of depth `h` laid out in post-order: its `3^h`
leaves are `N` gadgets and its internal nodes are `M` gadgets (Theorem 3.5 uses `h = 3`).
The compiler `Comp` appends gate `1` and then, for every gate `t` of a NOR circuit and every copy
`ℓ < m`, a cell `𝒞(t, ℓ)` whose leaves read random copies of the cells of the inputs of `t`.

* `cell_step1`: Step 1 of the proof of Theorem 3.5 (dominating events), pathwise and for every
  instance: if the output of a cell is wrong, the event `D(root)` holds.
* `compInst`: the compiled parent array `Comp(C)` (a valid instance).
* `comp_exact`: for `ε = 0`, `x*_{o(t,ℓ)} = val(g_t)` for all `t, ℓ`, whatever the coins.
* `comp_step1`: Step 1 for every cell of the compiled layout, for every instance (in particular
  for every outcome of the smoothing).
-/

namespace GC.RandomSeqNOR

/-- Number of gates of a cell of depth `h`: `4` for a leaf, and `3 S + 8` for an internal node. -/
def cellSize : ℕ → ℕ
  | 0 => 4
  | h + 1 => 3 * cellSize h + 8

theorem four_le_cellSize (h : ℕ) : 4 ≤ cellSize h := by
  cases h with
  | zero => exact le_rfl
  | succ h => simp only [cellSize]; omega

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

theorem maj_of_two {x y z v : ZMod 2} (h : (x = v ∧ y = v) ∨ (y = v ∧ z = v) ∨ (x = v ∧ z = v)) :
    maj x y z = v := by
  revert h; revert x y z v; decide

/-- **Step 1 of Theorem 3.5 (dominating events).** For every instance and every cell of depth `h`
starting at `k ≥ 1`: if `D(root)` fails, the output `x*_{k + S - 1}` equals `NOR(va, vb)`. -/
theorem cell_step1 (P : Inst) (va vb : ZMod 2) :
    ∀ h k (leafIn : ℕ → ℕ × ℕ), 1 ≤ k → ¬ cellBad P va vb h k leafIn →
      trace P (k + cellSize h - 1) = nor va vb := by
  intro h
  induction h with
  | zero =>
    intro k leafIn hk hbad
    simp only [cellBad, not_or, not_not] at hbad
    obtain ⟨hN, ha, hb⟩ := hbad
    rw [show k + cellSize 0 - 1 = k + 3 by simp [cellSize], gadget_N P hk hN, ha, hb]
  | succ h ih =>
    intro k leafIn hk hbad
    simp only [cellBad, not_or, not_not] at hbad
    obtain ⟨hM, h01, h12, h02⟩ := hbad
    have S4 := four_le_cellSize h
    have e : k + cellSize (h + 1) - 1 = k + 3 * cellSize h + 7 := by simp only [cellSize]; omega
    rw [e, gadget_M P (by omega) hM]
    apply maj_of_two
    have c0 := ih k leafIn hk
    have c1 := ih (k + cellSize h) (fun l => leafIn (3 ^ h + l)) (by omega)
    have c2 := ih (k + 2 * cellSize h) (fun l => leafIn (2 * 3 ^ h + l)) (by omega)
    rw [show k + cellSize h + cellSize h - 1 = k + 2 * cellSize h - 1 by omega] at c1
    rw [show k + 2 * cellSize h + cellSize h - 1 = k + 3 * cellSize h - 1 by omega] at c2
    by_cases b0 : cellBad P va vb h k leafIn
    · have nb1 := fun h' => h01 ⟨b0, h'⟩
      have nb2 := fun h' => h02 ⟨b0, h'⟩
      exact Or.inr (Or.inl ⟨c1 nb1, c2 nb2⟩)
    · by_cases b1 : cellBad P va vb h (k + cellSize h) (fun l => leafIn (3 ^ h + l))
      · have nb2 := fun h' => h12 ⟨b1, h'⟩
        exact Or.inr (Or.inr ⟨c0 b0, c2 nb2⟩)
      · exact Or.inl ⟨c0 b0, c1 b1⟩

/-- If an instance carries all listed pointers of a cell and all leaf inputs hold the expected
values, then `D(root)` fails. -/
theorem cell_not_bad (P : Inst) (va vb : ZMod 2) :
    ∀ h k (leafIn : ℕ → ℕ × ℕ),
      (∀ o < cellSize h, P.j (k + o) = cellPtr h k leafIn o) →
      (∀ l < 3 ^ h, trace P (leafIn l).1 = va ∧ trace P (leafIn l).2 = vb) →
      ¬ cellBad P va vb h k leafIn := by
  intro h
  induction h with
  | zero =>
    intro k leafIn hp hl
    have p0 := hp 0 (by simp [cellSize]); have p1 := hp 1 (by simp [cellSize])
    have p2 := hp 2 (by simp [cellSize]); have p3 := hp 3 (by simp [cellSize])
    simp only [cellPtr, add_zero] at p0 p1 p2 p3
    simp only [cellBad, not_or, not_not]
    obtain ⟨l1, l2⟩ := hl 0 (by simp)
    exact ⟨⟨p0, p1, p2, p3⟩, l1, l2⟩
  | succ h ih =>
    intro k leafIn hp hl
    have S4 := four_le_cellSize h
    have hS : cellSize (h + 1) = 3 * cellSize h + 8 := rfl
    simp only [cellBad, not_or, not_not]
    -- pointers of the `M` gadget
    have pM : ∀ i < 8, P.j (k + 3 * cellSize h + i) =
        cellPtr (h + 1) k leafIn (3 * cellSize h + i) := by
      intro i hi; rw [← hp _ (by omega), add_assoc]
    have key : ∀ i, i < 8 → P.j (k + 3 * cellSize h + i) =
        if i = 0 then 0 else if i = 1 then k + cellSize h - 1 else if i = 2 then 1
        else if i = 3 then k + 2 * cellSize h - 1 else if i = 4 then k + 2 * cellSize h - 1
        else if i = 5 then k + 3 * cellSize h + 1 else if i = 6 then k + 3 * cellSize h - 1
        else k + 3 * cellSize h + 3 := by
      intro i hi
      rw [pM i hi]
      simp only [cellPtr]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
        show 3 * cellSize h + i - 3 * cellSize h = i by omega]
    have hM : CarriesM P (k + 3 * cellSize h) (k + cellSize h - 1) (k + 2 * cellSize h - 1)
        (k + 3 * cellSize h - 1) := by
      refine ⟨by simpa using key 0 (by omega), by simpa using key 1 (by omega),
        by simpa using key 2 (by omega), by simpa using key 3 (by omega),
        by simpa using key 4 (by omega), by simpa using key 5 (by omega),
        by simpa using key 6 (by omega), by simpa using key 7 (by omega)⟩
    -- the three children
    have n0 : ¬ cellBad P va vb h k leafIn := by
      apply ih k leafIn
      · intro o ho
        rw [hp o (by omega)]
        simp only [cellPtr, ho, ↓reduceIte]
      · intro l hl'; exact hl l (by rw [pow_succ]; omega)
    have n1 : ¬ cellBad P va vb h (k + cellSize h) (fun l => leafIn (3 ^ h + l)) := by
      apply ih
      · intro o ho
        rw [add_assoc, hp (cellSize h + o) (by omega)]
        simp only [cellPtr, show ¬ (cellSize h + o < cellSize h) by omega,
          show cellSize h + o < 2 * cellSize h by omega, ↓reduceIte,
          show cellSize h + o - cellSize h = o by omega]
      · intro l hl'; exact hl _ (by rw [pow_succ]; omega)
    have n2 : ¬ cellBad P va vb h (k + 2 * cellSize h) (fun l => leafIn (2 * 3 ^ h + l)) := by
      apply ih
      · intro o ho
        rw [add_assoc, hp (2 * cellSize h + o) (by omega)]
        simp only [cellPtr, show ¬ (2 * cellSize h + o < cellSize h) by omega,
          show ¬ (2 * cellSize h + o < 2 * cellSize h) by omega,
          show 2 * cellSize h + o < 3 * cellSize h by omega, ↓reduceIte,
          show 2 * cellSize h + o - 2 * cellSize h = o by omega]
      · intro l hl'; exact hl _ (by rw [pow_succ]; omega)
    exact ⟨hM, fun h' => n0 h'.1, fun h' => n1 h'.1, fun h' => n0 h'.1⟩

/-- Listed pointers of a cell point backwards, provided the leaf inputs lie before the cell. -/
theorem cellPtr_lt : ∀ h k (leafIn : ℕ → ℕ × ℕ), 1 ≤ k →
    (∀ l < 3 ^ h, (leafIn l).1 < k ∧ (leafIn l).2 < k) →
    ∀ o < cellSize h, cellPtr h k leafIn o < k + o := by
  intro h
  induction h with
  | zero =>
    intro k leafIn hk hl o ho
    obtain ⟨l1, l2⟩ := hl 0 (by simp)
    simp only [cellSize] at ho
    simp only [cellPtr]
    split_ifs <;> omega
  | succ h ih =>
    intro k leafIn hk hl o ho
    have S4 := four_le_cellSize h
    have hS : cellSize (h + 1) = 3 * cellSize h + 8 := rfl
    have hp : 3 ^ (h + 1) = 3 * 3 ^ h := by rw [pow_succ]; ring
    simp only [cellPtr]
    split_ifs with c1 c2 c3
    · exact ih k leafIn hk (fun l hl' => hl l (by omega)) o c1
    · have := ih (k + cellSize h) (fun l => leafIn (3 ^ h + l)) (by omega)
        (fun l hl' => by
          obtain ⟨a1, a2⟩ := hl (3 ^ h + l) (by omega); exact ⟨by omega, by omega⟩)
        (o - cellSize h) (by omega)
      omega
    · have := ih (k + 2 * cellSize h) (fun l => leafIn (2 * 3 ^ h + l)) (by omega)
        (fun l hl' => by
          obtain ⟨a1, a2⟩ := hl (2 * 3 ^ h + l) (by omega); exact ⟨by omega, by omega⟩)
        (o - 2 * cellSize h) (by omega)
      omega
    all_goals omega

/-! ### NOR circuits and the compiler -/

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

theorem NORCircuit.val_eq (C : NORCircuit) (t : ℕ) :
    C.val t = nor (C.wireVal (C.u t)) (C.wireVal (C.v t)) := by
  rw [NORCircuit.val]
  split <;> split <;> simp_all [NORCircuit.wireVal]

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

theorem wirePos_lt (h m : ℕ) {t ℓ : ℕ} (w : Wire) (hw : ∀ t', w = Wire.gate t' → t' < t) (r : Fin m) :
    wirePos h m w r < cellStart h m t ℓ := by
  have S4 := four_le_cellSize h
  cases w with
  | const b =>
    simp only [wirePos, cellStart]
    split_ifs <;> omega
  | gate t' =>
    have ht := hw t' rfl
    simp only [wirePos, compOut, cellStart]
    have h1 : t' * m + r.1 + 1 ≤ t * m + ℓ := by
      have : (t' + 1) * m ≤ t * m := Nat.mul_le_mul_right m ht
      have := r.2
      nlinarith
    have h2 : (t' * m + r.1 + 1) * cellSize h ≤ (t * m + ℓ) * cellSize h :=
      Nat.mul_le_mul_right _ h1
    have h3 : (t' * m + r.1 + 1) * cellSize h = (t' * m + r.1) * cellSize h + cellSize h := by
      ring
    omega

/-- The compiled pointers point backwards. -/
theorem compPtr_lt (C : NORCircuit) (h m s : ℕ) (coin : ℕ → ℕ → ℕ → Fin m × Fin m) :
    ∀ p, 0 < p → compPtr C h m s coin p < p := by
    intro p hp
    have S4 := four_le_cellSize h
    unfold compPtr
    split_ifs with h1 h2
    · omega
    · have hdiv := Nat.div_add_mod (p - 2) (cellSize h)
      have hmod := Nat.mod_lt (p - 2) (show 0 < cellSize h by omega)
      set q := (p - 2) / cellSize h with hq
      have hqm := Nat.div_add_mod q m
      have key := cellPtr_lt h (2 + q * cellSize h)
        (leafInputs C h m coin (q / m) (q % m)) (by omega)
        (fun l _ => by
          have e : 2 + q * cellSize h = cellStart h m (q / m) (q % m) := by
            simp only [cellStart]
            rw [show q / m * m + q % m = q by rw [mul_comm]; exact hqm]
          rw [e]
          exact ⟨wirePos_lt h m (C.u (q / m)) (C.u_lt _) _,
            wirePos_lt h m (C.v (q / m)) (C.v_lt _) _⟩)
        ((p - 2) % cellSize h) hmod
      have hc : q * cellSize h = cellSize h * q := mul_comm _ _
      omega
    · omega

/-- The compiled instance `Comp(C)`, a valid parent array. -/
def compInst (C : NORCircuit) (h m s : ℕ) (coin : ℕ → ℕ → ℕ → Fin m × Fin m) : Inst :=
  ⟨compPtr C h m s coin, compPtr_lt C h m s coin⟩

/-- `Comp(C)` carries the listed pointers of every cell `𝒞(t, ℓ)`, `t < s`, `ℓ < m`. -/
theorem compInst_carries (C : NORCircuit) (h m s : ℕ) (coin : ℕ → ℕ → ℕ → Fin m × Fin m)
    {t ℓ : ℕ} (ht : t < s) (hℓ : ℓ < m) :
    ∀ o < cellSize h, (compInst C h m s coin).j (cellStart h m t ℓ + o) =
      cellPtr h (cellStart h m t ℓ) (leafInputs C h m coin t ℓ) o := by
  intro o ho
  have S4 := four_le_cellSize h
  show compPtr C h m s coin _ = _
  have hq : (cellStart h m t ℓ + o - 2) / cellSize h = t * m + ℓ := by
    simp only [cellStart]
    rw [show 2 + (t * m + ℓ) * cellSize h + o - 2 = o + cellSize h * (t * m + ℓ) by ring_nf; omega,
      Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt ho, zero_add]
  have hr : (cellStart h m t ℓ + o - 2) % cellSize h = o := by
    simp only [cellStart]
    rw [show 2 + (t * m + ℓ) * cellSize h + o - 2 = o + cellSize h * (t * m + ℓ) by ring_nf; omega,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ho]
  have hlt : t * m + ℓ < s * m := by
    have : (t + 1) * m ≤ s * m := Nat.mul_le_mul_right m ht
    nlinarith
  have hdm : (t * m + ℓ) / m = t := by
    rw [show t * m + ℓ = ℓ + m * t by ring, Nat.add_mul_div_left _ _ (by omega),
      Nat.div_eq_of_lt hℓ, zero_add]
  have hmm : (t * m + ℓ) % m = ℓ := by
    rw [show t * m + ℓ = ℓ + m * t by ring, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hℓ]
  unfold compPtr
  rw [if_neg (by simp only [cellStart]; omega), hq, if_pos hlt, hr, hdm, hmm]
  rfl

theorem trace_wirePos (C : NORCircuit) (h m : ℕ) (P : Inst) {t : ℕ}
    (hgate : ∀ t' < t, ∀ r < m, trace P (compOut h m t' r) = C.val t')
    (w : Wire) (hw : ∀ t', w = Wire.gate t' → t' < t) (r : Fin m) :
    trace P (wirePos h m w r) = C.wireVal w := by
  cases w with
  | const b =>
    simp only [wirePos, NORCircuit.wireVal]
    rcases zmod2_cases b with rfl | rfl
    · simp only [show ¬ ((0 : ZMod 2) = 1) by decide, ↓reduceIte, trace_one]
    · simp only [↓reduceIte, trace_zero]
  | gate t' =>
    simp only [wirePos, NORCircuit.wireVal]
    exact hgate t' (hw t' rfl) r.1 r.2

/-- **Exactness of the unsmoothed embedding (Section 3.2).** For `ε = 0`, induction along the
layout gives `x*_{o(t,ℓ)} = val(g_t)` for all `t < s` and `ℓ < m`, whatever the coins. -/
theorem comp_exact (C : NORCircuit) (h m s : ℕ) (coin : ℕ → ℕ → ℕ → Fin m × Fin m) :
    ∀ t < s, ∀ ℓ < m, trace (compInst C h m s coin) (compOut h m t ℓ) = C.val t := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro ht ℓ hℓ
    have S4 := four_le_cellSize h
    unfold compOut
    rw [C.val_eq t]
    apply cell_step1 _ _ _ h _ _ (by simp only [cellStart]; omega)
    apply cell_not_bad _ _ _ h _ _ (compInst_carries C h m s coin ht hℓ)
    intro l _
    have hg : ∀ t' < t, ∀ r < m, trace (compInst C h m s coin) (compOut h m t' r) = C.val t' :=
      fun t' ht' r hr => ih t' ht' (by omega) r hr
    exact ⟨trace_wirePos C h m _ hg _ (C.u_lt t) _, trace_wirePos C h m _ hg _ (C.v_lt t) _⟩

/-- **Step 1 of Theorem 3.5 for the compiled layout.** For every instance `P` (for instance every
outcome of the smoothing of `Comp(C)`), if the output of `𝒞(t, ℓ)` is bad, i.e.
`x*_{o(t,ℓ)} ≠ val(g_t)`, then the event `D(root 𝒞(t, ℓ))` holds; at the leaves, a wrong input is
exactly a bad input cell (constants are never bad). -/
theorem comp_step1 (C : NORCircuit) (h m : ℕ) (coin : ℕ → ℕ → ℕ → Fin m × Fin m) (P : Inst)
    (t ℓ : ℕ) (hbad : trace P (compOut h m t ℓ) ≠ C.val t) :
    cellBad P (C.wireVal (C.u t)) (C.wireVal (C.v t)) h (cellStart h m t ℓ)
      (leafInputs C h m coin t ℓ) := by
  by_contra hD
  apply hbad
  rw [C.val_eq t]
  exact cell_step1 P _ _ h _ _ (by simp only [cellStart]; omega) hD

end GC.RandomSeqNOR
