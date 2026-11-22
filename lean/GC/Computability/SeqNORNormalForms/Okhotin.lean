import GC.Computability.SeqNORNormalForms.Basic

/-!
# 006a, Section 3: the five-cell reduction (Okhotin's theorem)

For a NOR circuit with `G ≥ 2` gates put `pos 0 = 0`, `pos 1 = 1`, `pos w = 5w - 5`, and
let `n = 5G - 1`. The parent array is `j_1 = 0`, the block
`j_{i₁} = pos a_w, j_{i₁+1} = 0, j_{i₁+2} = i₁, j_{i₁+3} = pos b_w, j_{i₁+4} = 0`
with `i₁ = 5w - 8` for every gate `w ≥ 2`, and the tail
`j_{5G-3} = pos G, j_{5G-2} = 0, j_{5G-1} = 5G - 3`.
-/

namespace GC.SeqNORNormalForms

/-- `pos(w)`: the position holding wire `w`. -/
def okPos (w : ℕ) : ℕ := if w ≤ 1 then w else 5 * w - 5

/-- The five-cell parent array of a NOR circuit (Section 3 of 006a). -/
def okhotin (C : NorCircuit) (i : ℕ) : ℕ :=
  if i ≤ 1 then 0
  else if i ≤ 5 * C.G - 4 then
    if (i + 8) % 5 = 0 then okPos (C.a ((i + 8) / 5))
    else if (i + 8) % 5 = 1 then 0
    else if (i + 8) % 5 = 2 then i - 2
    else if (i + 8) % 5 = 3 then okPos (C.b ((i + 8) / 5))
    else 0
  else if i = 5 * C.G - 3 then okPos C.G
  else if i = 5 * C.G - 2 then 0
  else 5 * C.G - 3

section

variable (C : NorCircuit)

theorem okPos_lt {u w : ℕ} (hw : 2 ≤ w) (hu : u < w) : okPos u < 5 * w - 8 := by
  unfold okPos; split <;> omega

theorem okhotin_block {w r : ℕ} (hw : 2 ≤ w) (hwG : w ≤ C.G) (hr : r < 5) :
    okhotin C (5 * w - 8 + r) =
      if r = 0 then okPos (C.a w) else if r = 1 then 0 else if r = 2 then 5 * w - 8
      else if r = 3 then okPos (C.b w) else 0 := by
  unfold okhotin
  rw [if_neg (by omega), if_pos (by omega)]
  have e1 : (5 * w - 8 + r + 8) % 5 = r := by omega
  have e2 : (5 * w - 8 + r + 8) / 5 = w := by omega
  rw [e1, e2]
  interval_cases r <;> simp

/-- **Lemma 3.2 of 006a (block invariant).** If `x_{i₁-1} = 0` then
`x_{i₁+3} = NOR(x_p, x_q)` and `x_{i₁+4} = 0`. -/
theorem okhotin_block_values (hC : C.Valid) {w : ℕ} (hw : 2 ≤ w) (hwG : w ≤ C.G)
    (hz : trace (okhotin C) (5 * w - 8 - 1) = false) :
    trace (okhotin C) (5 * w - 8 + 3) =
        nor (trace (okhotin C) (okPos (C.a w))) (trace (okhotin C) (okPos (C.b w))) ∧
      trace (okhotin C) (5 * w - 8 + 4) = false := by
  obtain ⟨ha, hb⟩ := hC.2 w hw hwG
  have hp := okPos_lt hw ha
  have hq := okPos_lt hw hb
  set i := 5 * w - 8 with hi
  have b0 := okhotin_block C hw hwG (r := 0) (by omega)
  have b1 := okhotin_block C hw hwG (r := 1) (by omega)
  have b2 := okhotin_block C hw hwG (r := 2) (by omega)
  have b3 := okhotin_block C hw hwG (r := 3) (by omega)
  have b4 := okhotin_block C hw hwG (r := 4) (by omega)
  simp only [Nat.add_zero, if_true, if_false, show (1 : ℕ) ≠ 0 by decide,
    show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide, show (3 : ℕ) ≠ 0 by decide,
    show (3 : ℕ) ≠ 1 by decide, show (3 : ℕ) ≠ 2 by decide, show (4 : ℕ) ≠ 0 by decide,
    show (4 : ℕ) ≠ 1 by decide, show (4 : ℕ) ≠ 2 by decide, show (4 : ℕ) ≠ 3 by decide]
    at b0 b1 b2 b3 b4
  rw [← hi] at b2
  have e0 := trace_step (okhotin C) i (okPos (C.a w)) (by omega) b0 hp
  have e1 := trace_step (okhotin C) (i + 1) 0 (by omega) b1 (by omega)
  have e2 := trace_step (okhotin C) (i + 2) i (by omega) b2 (by omega)
  have e3 := trace_step (okhotin C) (i + 3) (okPos (C.b w)) (by omega) b3 (by omega)
  have e4 := trace_step (okhotin C) (i + 4) 0 (by omega) b4 (by omega)
  simp only [Nat.add_sub_cancel, show i + 2 - 1 = i + 1 by omega,
    show i + 3 - 1 = i + 2 by omega, show i + 4 - 1 = i + 3 by omega, trace_zero] at e1 e2 e3 e4
  rw [hz] at e0
  constructor
  · rw [e3, e2, e1, e0]
    cases trace (okhotin C) (okPos (C.a w)) <;> simp [nor]
  · rw [e4]; simp [nor]

/-- **Theorem 3.3 of 006a (Okhotin).** The five-cell array of a NOR circuit is a parent
array of length `5G - 1`, every wire is held at `pos(w)`, and `x_n = w_G`. -/
theorem okhotin_correct (hC : C.Valid) :
    IsParentArray (5 * C.G - 1) (okhotin C) ∧
      (∀ w, w ≤ C.G → trace (okhotin C) (okPos w) = C.wire w) ∧
      trace (okhotin C) (5 * C.G - 1) = C.wire C.G := by
  have hG := hC.1
  -- invariant up to gate `w`
  have inv : ∀ w, 1 ≤ w → w ≤ C.G →
      trace (okhotin C) (5 * w - 4) = false ∧
        ∀ w', w' ≤ w → trace (okhotin C) (okPos w') = C.wire w' := by
    intro w hw1 hwG
    induction w with
    | zero => omega
    | succ w ih =>
      rcases Nat.eq_zero_or_pos w with rfl | hw0
      · have h1 : trace (okhotin C) 1 = false := by
          rw [trace_step (okhotin C) 1 0 le_rfl (by simp [okhotin]) (by omega)]
          simp [trace_zero, nor]
        refine ⟨h1, ?_⟩
        intro w' hw'
        interval_cases w'
        · simp [okPos, trace_zero, NorCircuit.wire_zero]
        · simp [okPos, h1, NorCircuit.wire_one]
      · obtain ⟨hz, hv⟩ := ih (by omega) (by omega)
        obtain ⟨ha, hb⟩ := hC.2 (w + 1) (by omega) hwG
        have hz' : trace (okhotin C) (5 * (w + 1) - 8 - 1) = false := by
          rw [show 5 * (w + 1) - 8 - 1 = 5 * w - 4 by omega]; exact hz
        obtain ⟨h3, h4⟩ := okhotin_block_values C hC (w := w + 1) (by omega) hwG hz'
        refine ⟨by rw [show 5 * (w + 1) - 4 = 5 * (w + 1) - 8 + 4 by omega]; exact h4, ?_⟩
        intro w' hw'
        rcases Nat.lt_or_ge w' (w + 1) with h | h
        · exact hv w' (by omega)
        · obtain rfl : w' = w + 1 := by omega
          rw [show okPos (w + 1) = 5 * (w + 1) - 8 + 3 by unfold okPos; split <;> omega, h3,
            hv _ (by omega), hv _ (by omega), NorCircuit.wire_gate C (w + 1) (by omega) ha hb]
  obtain ⟨hz, hv⟩ := inv C.G (by omega) le_rfl
  refine ⟨?_, hv, ?_⟩
  · intro i h1 hn
    unfold okhotin
    split_ifs <;> (try omega) <;> first
    | (unfold okPos; split_ifs <;> omega)
    | (have hw2 : 2 ≤ (i + 8) / 5 := by omega
       have hwG : (i + 8) / 5 ≤ C.G := by omega
       have := hC.2 _ hw2 hwG
       unfold okPos; split_ifs <;> omega)
  · have hpG := hv C.G le_rfl
    have hposG : okPos C.G = 5 * C.G - 5 := by unfold okPos; split <;> omega
    have j3 : okhotin C (5 * C.G - 3) = okPos C.G := by
      unfold okhotin; rw [if_neg (by omega), if_neg (by omega), if_pos rfl]
    have j2 : okhotin C (5 * C.G - 2) = 0 := by
      unfold okhotin; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]
    have j1 : okhotin C (5 * C.G - 1) = 5 * C.G - 3 := by
      unfold okhotin
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    have e3 := trace_step (okhotin C) (5 * C.G - 3) _ (by omega) j3 (by omega)
    have e2 := trace_step (okhotin C) (5 * C.G - 2) 0 (by omega) j2 (by omega)
    have e1 := trace_step (okhotin C) (5 * C.G - 1) _ (by omega) j1 (by omega)
    rw [show 5 * C.G - 3 - 1 = 5 * C.G - 4 by omega, hz, hpG] at e3
    rw [show 5 * C.G - 1 - 1 = 5 * C.G - 2 by omega, e2, e3] at e1
    rw [e1]
    cases C.wire C.G <;> simp [nor, trace_zero]

/-- **Corollary 3.4 of 006a (key step).** If gate `2` is the dummy gate `NOR(w_0, w_0)`
(`a_2 = 0`), then in the five-cell array `j_i ≠ i - 1` for every `2 ≤ i ≤ n`, so `i - 1` and
`j_i` are two distinct smaller neighbours of `i` in the graph `G_j`. -/
theorem okhotin_no_spine (hC : C.Valid) (ha2 : C.a 2 = 0) :
    ∀ i, 2 ≤ i → i ≤ 5 * C.G - 1 → okhotin C i ≠ i - 1 := by
  have hG := hC.1
  intro i h2 hn
  unfold okhotin
  split_ifs with h1 h3 h4 <;> (try omega) <;> first
  | (unfold okPos; split_ifs <;> omega)
  | (have hw2 : 2 ≤ (i + 8) / 5 := by omega
     have hwG : (i + 8) / 5 ≤ C.G := by omega
     have := hC.2 _ hw2 hwG
     rcases em ((i + 8) / 5 = 2) with hw | hw
     · rw [hw] at this ⊢; rw [ha2]; simp [okPos]; omega
     · unfold okPos; split_ifs <;> omega)

end

end GC.SeqNORNormalForms
