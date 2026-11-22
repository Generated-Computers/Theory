import GC.Computability.SeqNORNormalForms.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.Ring.Basic

/-!
# 006d: Newton's method over GF(2) for Sequential NOR — the first-collision law

`F_i(x) = x_i + G_i(x)`, with `G_i = 1 + x_{i-1}` at a NOT gate (`j_i = i - 1`) and
`G_i = (1 + x_{i-1})(1 + x_{j_i})` otherwise. A Newton round is `x ↦ x + d` with
`J(x) d = F(x)`, where `J(x)` is the unit lower-triangular Jacobian with respect to
`x_1, …, x_n` (convention `d_0 = 0`). We define `d` by forward substitution and prove that it
solves `J(x) d = F(x)`.
-/

namespace GC.SeqNORNormalForms

/-- Embedding of `Bool` into `𝔽₂`. -/
def toF2 (b : Bool) : ZMod 2 := if b then 1 else 0

/-- `G_i(x)`. -/
def newtonG (j : ℕ → ℕ) (x : ℕ → ZMod 2) (i : ℕ) : ZMod 2 :=
  if j i = i - 1 then 1 + x (i - 1) else (1 + x (i - 1)) * (1 + x (j i))

/-- `F_i(x) = x_i + G_i(x)`. -/
def newtonF (j : ℕ → ℕ) (x : ℕ → ZMod 2) (i : ℕ) : ZMod 2 := x i + newtonG j x i

/-- Coordinates `1, …, n` of a vector, with the convention `z_0 = 0`. -/
def dropZero (z : ℕ → ZMod 2) (k : ℕ) : ZMod 2 := if k = 0 then 0 else z k

/-- Row `i` of `J(x) z`: `z_i + z_{i-1}` at a NOT gate and
`z_i + (1 + x_{j_i}) z_{i-1} + (1 + x_{i-1}) z_{j_i}` at a binary gate (with `z_0 = 0`). -/
def jacMul (j : ℕ → ℕ) (x z : ℕ → ZMod 2) (i : ℕ) : ZMod 2 :=
  z i + (if j i = i - 1 then dropZero z (i - 1)
    else (1 + x (j i)) * dropZero z (i - 1) + (1 + x (i - 1)) * dropZero z (j i))

/-- The Newton direction `d = J(x)^{-1} F(x)`, by forward substitution (`d_0 = 0`). -/
def newtonDir (j : ℕ → ℕ) (x : ℕ → ZMod 2) : ℕ → ZMod 2
  | 0 => 0
  | i + 1 => newtonF j x (i + 1) +
      (if j (i + 1) = i then (if i = 0 then 0 else newtonDir j x i)
        else (1 + x (j (i + 1))) * (if i = 0 then 0 else newtonDir j x i) +
          (1 + x i) * (if h : j (i + 1) < i + 1 then
            (if j (i + 1) = 0 then 0 else newtonDir j x (j (i + 1))) else 0))
termination_by i => i

/-- One Newton round `x⁺ = x + d`. -/
def newtonStep (j : ℕ → ℕ) (x : ℕ → ZMod 2) (i : ℕ) : ZMod 2 := x i + newtonDir j x i

/-- The trace as a vector over `𝔽₂`. -/
def traceF2 (j : ℕ → ℕ) (i : ℕ) : ZMod 2 := toF2 (trace j i)

/-- The collision vector `q_i(e) = e_{i-1} e_{j_i}` at binary gates, `0` at NOT gates. -/
def collision (j : ℕ → ℕ) (e : ℕ → ZMod 2) (i : ℕ) : ZMod 2 :=
  if j i = i - 1 then 0 else e (i - 1) * e (j i)

section

variable (j : ℕ → ℕ)

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a; decide

theorem newtonDir_zero (x : ℕ → ZMod 2) : newtonDir j x 0 = 0 := by rw [newtonDir]

theorem dropZero_newtonDir (x : ℕ → ZMod 2) : dropZero (newtonDir j x) = newtonDir j x := by
  funext k; unfold dropZero; split
  · next h => subst h; rw [newtonDir_zero]
  · rfl

/-- `d` solves the triangular system `J(x) d = F(x)`, so `newtonStep` is a Newton round. -/
theorem jacMul_newtonDir (x : ℕ → ZMod 2) (i : ℕ) (hi : 1 ≤ i) (hj : j i < i) :
    jacMul j x (newtonDir j x) i = newtonF j x i := by
  obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  unfold jacMul
  rw [dropZero_newtonDir]
  conv_lhs => rw [newtonDir]
  simp only [Nat.add_sub_cancel, hj, dite_true]
  have h0 : ∀ k, (if k = 0 then (0 : ZMod 2) else newtonDir j x k) = newtonDir j x k := by
    intro k; split
    · next h => subst h; rw [newtonDir_zero]
    · rfl
  simp only [h0]
  split <;> (generalize newtonF j x (i + 1) = A; ring_nf; rw [show (2 : ZMod 2) = 0 from rfl]; ring)

theorem jacMul_add (x a b : ℕ → ZMod 2) (i : ℕ) :
    jacMul j x (a + b) i = jacMul j x a i + jacMul j x b i := by
  unfold jacMul dropZero
  simp only [Pi.add_apply]
  split_ifs <;> ring

theorem traceF2_F (n : ℕ) (hj : IsParentArray n j) (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
    newtonF j (traceF2 j) i = 0 := by
  have h := trace_at j i hi (hj i hi hin)
  unfold newtonF newtonG traceF2
  rw [h]
  split
  · next he => rw [he]; cases trace j (i - 1) <;> decide
  · cases trace j (i - 1) <;> cases trace j (j i) <;> decide

theorem traceF2_zero : traceF2 j 0 = 1 := by simp [traceF2, trace_zero, toF2]

/-- **Lemma 2.1 of 006d (exact error identity).** For `x_0 = 1`, with `e = x + y` and
`e⁺ = x⁺ + y`, `J(x) e⁺ = q(e)` on the rows `1, …, n`. -/
theorem error_identity (n : ℕ) (hj : IsParentArray n j) (x : ℕ → ZMod 2) (hx0 : x 0 = 1)
    (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
    jacMul j x (newtonStep j x + traceF2 j) i = collision j (x + traceF2 j) i := by
  have hji := hj i hi hin
  have hsplit : newtonStep j x + traceF2 j = (x + traceF2 j) + newtonDir j x := by
    funext k; simp only [newtonStep, Pi.add_apply]; ring
  rw [hsplit, jacMul_add, jacMul_newtonDir j x i hi hji]
  have hF := traceF2_F j n hj i hi hin
  have he0 : (x + traceF2 j) 0 = 0 := by
    simp only [Pi.add_apply, hx0, traceF2_zero]; rfl
  have hd : dropZero (x + traceF2 j) = x + traceF2 j := by
    funext k; unfold dropZero; split
    · next h => subst h; rw [he0]
    · rfl
  unfold jacMul collision newtonF newtonG at *
  rw [hd]
  simp only [Pi.add_apply] at *
  generalize traceF2 j = y at *
  split
  · next hne =>
    simp only [hne, if_true] at hF ⊢
    generalize x (i - 1) = a at *
    generalize y (i - 1) = b at *
    generalize x i = c at *
    generalize y i = d at *
    rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
      rcases zmod2_cases c with rfl | rfl <;> rcases zmod2_cases d with rfl | rfl <;>
      revert hF <;> decide
  · next hne =>
    simp only [hne, if_false] at hF ⊢
    generalize x (i - 1) = a at *
    generalize y (i - 1) = b at *
    generalize x i = c at *
    generalize y i = d at *
    generalize x (j i) = f at *
    generalize y (j i) = g at *
    rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
      rcases zmod2_cases c with rfl | rfl <;> rcases zmod2_cases d with rfl | rfl <;>
      rcases zmod2_cases f with rfl | rfl <;> rcases zmod2_cases g with rfl | rfl <;>
      revert hF <;> decide

/-- Forward substitution: if `J(x) z = w` on rows `1, …, m`, `z_0 = 0`, and `w` vanishes on
rows `1, …, m-1`, then `z` vanishes on `0, …, m-1` and `z_m = w_m`. -/
theorem forward_subst (n : ℕ) (hj : IsParentArray n j) (x z w : ℕ → ZMod 2) (hz0 : z 0 = 0)
    (m : ℕ) (hm : m ≤ n) (hJ : ∀ i, 1 ≤ i → i ≤ m → jacMul j x z i = w i)
    (hw : ∀ i, 1 ≤ i → i < m → w i = 0) :
    (∀ i, i < m → z i = 0) ∧ (1 ≤ m → z m = w m) := by
  have hd : ∀ k, (∀ i, i < k → z i = 0) → ∀ i, i < k → dropZero z i = 0 := by
    intro k hk i hi; unfold dropZero; split
    · rfl
    · exact hk i hi
  have key : ∀ i, 1 ≤ i → i ≤ m → (∀ k, k < i → z k = 0) → z i = w i := by
    intro i hi him hk
    have := hJ i hi him
    unfold jacMul at this
    have hji := hj i hi (by omega)
    rw [hd i hk (i - 1) (by omega), hd i hk (j i) hji] at this
    simp at this
    exact this
  have low : ∀ i, i < m → z i = 0 := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro him
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · exact hz0
      · rw [key i hi (by omega) (fun k hk => ih k hk (by omega)), hw i hi him]
  exact ⟨low, fun h1 => key m h1 le_rfl low⟩

/-- If `q_i(e) ≠ 0` then `i` is a binary gate with `e_{i-1} = e_{j_i} = 1`; so if `e`
vanishes below `m`, the collision vector vanishes below `m + 2`. -/
theorem collision_vanish (n : ℕ) (hj : IsParentArray n j) (e : ℕ → ZMod 2) (m : ℕ)
    (he : ∀ i, i < m → e i = 0) : ∀ i, 1 ≤ i → i ≤ n → i < m + 2 → collision j e i = 0 := by
  intro i hi hin him
  have hji := hj i hi hin
  unfold collision
  split
  · rfl
  · next hne =>
    by_cases h1 : i - 1 < m
    · rw [he _ h1]; ring
    · rw [he (j i) (by omega)]; ring

/-- **Theorem 2.2 of 006d (first-collision law).** Let `x_0 = 1`, `e = x + y`,
`e⁺ = x⁺ + y`. If `e` vanishes on `0, …, m-1` then `q(e)` vanishes on `1, …, m+1`, and the
new error vanishes up to the first collision `s(q(e))` and equals `q` there. In particular the
first error advances by at least two positions per round:
`e` vanishes below `m` ⟹ `e⁺` vanishes below `m + 2` (on `0, …, n`). -/
theorem first_collision_law (n : ℕ) (hj : IsParentArray n j) (x : ℕ → ZMod 2)
    (hx0 : x 0 = 1) :
    (∀ m, m ≤ n → (∀ i, 1 ≤ i → i < m → collision j (x + traceF2 j) i = 0) →
      (∀ i, i < m → (newtonStep j x + traceF2 j) i = 0) ∧
      (1 ≤ m → (newtonStep j x + traceF2 j) m = collision j (x + traceF2 j) m)) ∧
    (∀ m, (∀ i, i < m → (x + traceF2 j) i = 0) →
      ∀ i, i ≤ n → i < m + 2 → (newtonStep j x + traceF2 j) i = 0) := by
  have hz0 : (newtonStep j x + traceF2 j) 0 = 0 := by
    simp only [Pi.add_apply, newtonStep, newtonDir_zero, hx0, traceF2_zero]; rfl
  have part1 : ∀ m, m ≤ n → (∀ i, 1 ≤ i → i < m → collision j (x + traceF2 j) i = 0) →
      (∀ i, i < m → (newtonStep j x + traceF2 j) i = 0) ∧
      (1 ≤ m → (newtonStep j x + traceF2 j) m = collision j (x + traceF2 j) m) := by
    intro m hm hq
    exact forward_subst j n hj x _ _ hz0 m hm
      (fun i hi him => error_identity j n hj x hx0 i hi (by omega)) hq
  refine ⟨part1, ?_⟩
  intro m he i hin him
  have hq := collision_vanish j n hj _ m he
  rcases Nat.lt_or_ge (m + 1) n with h | h
  · exact (part1 (m + 2) (by omega) (fun k hk hkm => hq k hk (by omega) hkm)).1 i him
  · rcases Nat.eq_zero_or_pos i with rfl | hi
    · exact hz0
    · have := part1 i hin (fun k hk hki => hq k hk (by omega) (by omega))
      rw [this.2 hi]
      exact hq i hi hin him

theorem newtonStep_zero (x : ℕ → ZMod 2) : newtonStep j x 0 = x 0 := by
  simp [newtonStep, newtonDir_zero]

/-- **Corollary 2.3 of 006d.** From every start `x⁽⁰⁾` with `x⁽⁰⁾_0 = 1`, after `t` Newton
rounds the iterate agrees with the trace on `0, …, 2t`; hence Newton's method reaches the
trace (on `0, …, n`) within `⌈n/2⌉` rounds. -/
theorem newton_rounds (n : ℕ) (hj : IsParentArray n j) (x₀ : ℕ → ZMod 2) (hx0 : x₀ 0 = 1) :
    ∀ t i, i ≤ n → i ≤ 2 * t → ((newtonStep j)^[t] x₀) i = traceF2 j i := by
  have hiter0 : ∀ t, ((newtonStep j)^[t] x₀) 0 = 1 := by
    intro t
    induction t with
    | zero => exact hx0
    | succ t ih => rw [Function.iterate_succ_apply', newtonStep_zero, ih]
  have herr : ∀ t i, i ≤ n → i < 2 * t + 1 → ((newtonStep j)^[t] x₀ + traceF2 j) i = 0 := by
    intro t
    induction t with
    | zero =>
      intro i _ hi
      obtain rfl : i = 0 := by omega
      simp only [Function.iterate_zero, id, Pi.add_apply, hx0, traceF2_zero]; rfl
    | succ t ih =>
      intro i hin hi
      rw [Function.iterate_succ_apply']
      have key := (first_collision_law j n hj _ (hiter0 t)).2 (min (2 * t + 1) (n + 1))
        (fun k hk => ih k (by omega) (by omega)) i hin (by omega)
      exact key
  intro t i hin hit
  have := herr t i hin (by omega)
  simp only [Pi.add_apply] at this
  generalize ((newtonStep j)^[t] x₀) i = a at *
  generalize traceF2 j i = b at *
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
    revert this <;> decide

/-- **Corollary 2.3 of 006d (round count).** Newton's method is exact on `0, …, n` after
`⌈n/2⌉ = (n+1)/2` rounds, from every start with `x_0 = 1`. -/
theorem newton_converges (n : ℕ) (hj : IsParentArray n j) (x₀ : ℕ → ZMod 2) (hx0 : x₀ 0 = 1)
    (t : ℕ) (ht : (n + 1) / 2 ≤ t) : ∀ i, i ≤ n → ((newtonStep j)^[t] x₀) i = traceF2 j i :=
  fun i hi => newton_rounds j n hj x₀ hx0 t i hi (by omega)

/-- **Corollary 2.3 of 006d (standard start).** From `(1, 0, …, 0)` Newton's method is exact after
`⌈(n-1)/2⌉ = n/2` rounds. -/
theorem newton_converges_std (n : ℕ) (hj : IsParentArray n j) (t : ℕ) (ht : n / 2 ≤ t) :
    ∀ i, i ≤ n → ((newtonStep j)^[t] (fun k => if k = 0 then 1 else 0)) i = traceF2 j i := by
  -- after `t` rounds the error vanishes below `2t + 2`
  have hiter0 : ∀ t, ((newtonStep j)^[t] (fun k => if k = 0 then (1 : ZMod 2) else 0)) 0 = 1 := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih => rw [Function.iterate_succ_apply', newtonStep_zero, ih]
  have hy1 : 1 ≤ n → traceF2 j 1 = 0 := by
    intro h1
    have := trace_at j 1 le_rfl (hj 1 le_rfl h1)
    rw [show j 1 = 0 by have := hj 1 le_rfl h1; omega] at this
    simp [traceF2, this, trace_zero, nor, toF2]
  have herr : ∀ t i, i ≤ n → i < 2 * t + 2 →
      ((newtonStep j)^[t] (fun k => if k = 0 then (1 : ZMod 2) else 0) + traceF2 j) i = 0 := by
    intro t
    induction t with
    | zero =>
      intro i hin hi
      simp only [Function.iterate_zero, id, Pi.add_apply]
      interval_cases i
      · simp [traceF2_zero]; rfl
      · simp [hy1 hin]
    | succ t ih =>
      intro i hin hi
      rw [Function.iterate_succ_apply']
      exact (first_collision_law j n hj _ (hiter0 t)).2 (min (2 * t + 2) (n + 1))
        (fun k hk => ih k (by omega) (by omega)) i hin (by omega)
  intro i hin
  have := herr t i hin (by omega)
  simp only [Pi.add_apply] at this
  generalize ((newtonStep j)^[t] fun k => if k = 0 then (1 : ZMod 2) else 0) i = a at *
  generalize traceF2 j i = b at *
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
    revert this <;> decide

end

/-- **Proposition 2.5 of 006d.** For `j = (0, 0, 1)` the trace is `y = (1,0,0,1)`; for
`x = (1,1,1,0)` the error is `e = (0,1,1,1)`, position `3` has no active transport parent
(`x_1 = x_2 = 1`), but `q_3(e) = e_2 e_1 = 1`. -/
theorem collision_without_active_parent :
    let j : ℕ → ℕ := fun i => if i = 3 then 1 else 0
    let x : ℕ → ZMod 2 := fun i => if i = 0 then 1 else if i = 1 then 1 else if i = 2 then 1
      else 0
    (traceF2 j 0 = 1 ∧ traceF2 j 1 = 0 ∧ traceF2 j 2 = 0 ∧ traceF2 j 3 = 1) ∧
    ((x + traceF2 j) 1 = 1 ∧ (x + traceF2 j) 2 = 1 ∧ (x + traceF2 j) 3 = 1) ∧
    x 1 = 1 ∧ x 2 = 1 ∧ collision j (x + traceF2 j) 3 = 1 := by
  intro j x
  have h1 : trace j 1 = false := by
    rw [trace_step j 1 0 le_rfl (by simp [j]) (by omega)]; simp [trace_zero, nor]
  have h2 : trace j 2 = false := by
    rw [trace_step j 2 0 (by omega) (by simp [j]) (by omega)]; simp [trace_zero, nor]
  have h3 : trace j 3 = true := by
    rw [trace_step j 3 1 (by omega) (by simp [j]) (by omega)]; simp [h1, h2, nor]
  simp [traceF2, toF2, trace_zero, h1, h2, h3, x, collision, j] <;> decide

end GC.SeqNORNormalForms
