import GC.Computability.SeqNORNormalForms.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat

/-!
# 006c, Theorem 5.1: fan-out normalization

The construction of the proof of Theorem 5.1, written with explicit indices. Positions `0`
and `1` (`j_1 = 0`, a rail) come first; round `i = 1, …, n` starts at `S_i`
(`S_1 = 2`, `S_{i+1} = S_i + 3i + 2`) and consists of
* for `k = 0, …, i-1` the positions `a = S_i + 3k` (parent `B_k`, the bus of the previous
  round) and `b = S_i + 3k + 1` (parent the current rail `S_i + 3k - 1`), and for
  `k ≤ i - 2` the position `c = S_i + 3k + 2` (parent `a`), the new rail;
* `y = S_i + 3i - 1` with parent `B'_{j_i} = S_i + 3 j_i + 1`;
* `g₁ = S_i + 3i` with parent the rail before step 2 (`S_i + 3i - 4`) and
  `g₂ = S_i + 3i + 1` with parent `y` (the new rail).
The bus before round `i ≥ 2` is `B_k = S_{i-1} + 3k + 1` (`k ≤ i - 2`) and
`B_{i-1} = y` of round `i - 1`; before round `1` it is `(0)`. The output is `y` of round `n`,
at position `S_n + 3n - 1`.
-/

namespace GC.SeqNORNormalForms

/-- `S_i`, the first position of round `i ≥ 1`. -/
def fanStart : ℕ → ℕ
  | 0 => 2
  | 1 => 2
  | i + 2 => fanStart (i + 1) + 3 * (i + 1) + 2

/-- The bus position `B_k` before round `i`. -/
def busPrev (i k : ℕ) : ℕ :=
  if i ≤ 1 then 0
  else if k + 2 ≤ i then fanStart (i - 1) + 3 * k + 1
  else fanStart (i - 1) + 3 * (i - 1) - 1

/-- The parent of the position `S_i + m` of round `i`. -/
def fanParent (j : ℕ → ℕ) (i m : ℕ) : ℕ :=
  if m = 3 * i - 1 then fanStart i + 3 * j i + 1
  else if m = 3 * i then fanStart i + 3 * i - 4
  else if m = 3 * i + 1 then fanStart i + 3 * i - 1
  else if m % 3 = 0 then busPrev i (m / 3)
  else fanStart i + m - 2

theorem exists_round (p : ℕ) : ∃ i, p < fanStart (i + 1) := by
  have h : ∀ i, i + 2 ≤ fanStart (i + 1) := by
    intro i
    induction i with
    | zero => simp [fanStart]
    | succ i ih => simp only [fanStart]; omega
  exact ⟨p, by have := h p; omega⟩

/-- The round containing position `p ≥ 2`. -/
def roundOf (p : ℕ) : ℕ := Nat.find (exists_round p)

/-- **Theorem 5.1 of 006c (the instance).** The fan-out normalized parent array. -/
def fanout (j : ℕ → ℕ) (p : ℕ) : ℕ :=
  if p ≤ 1 then 0 else fanParent j (roundOf p) (p - fanStart (roundOf p))

/-- Its length `S_n + 3n - 1`. -/
def fanLen (n : ℕ) : ℕ := fanStart n + 3 * n - 1

/-- The lengths for `n = 1, …, 7` are `4, 12, 23, 37, 54, 74, 97`, as reported in 006c. -/
theorem fanLen_values :
    fanLen 1 = 4 ∧ fanLen 2 = 12 ∧ fanLen 3 = 23 ∧ fanLen 4 = 37 ∧ fanLen 5 = 54 ∧
      fanLen 6 = 74 ∧ fanLen 7 = 97 := by
  decide

section

variable (j : ℕ → ℕ)

theorem fanStart_succ {i : ℕ} (hi : 1 ≤ i) : fanStart (i + 1) = fanStart i + 3 * i + 2 := by
  obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  rfl

theorem fanStart_ge (i : ℕ) : 2 ≤ fanStart i := by
  induction i with
  | zero => simp [fanStart]
  | succ i ih =>
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [fanStart]
    · rw [fanStart_succ hi]; omega

theorem fanStart_mono {i i' : ℕ} (hi : 1 ≤ i) (h : i < i') :
    fanStart i + 3 * i + 2 ≤ fanStart i' := by
  induction i' with
  | zero => omega
  | succ i' ih =>
    rcases Nat.lt_or_ge i i' with h' | h'
    · have := ih h'; rw [fanStart_succ (by omega)]; omega
    · obtain rfl : i = i' := by omega
      rw [fanStart_succ hi]

theorem fanStart_le {a b : ℕ} (h : a ≤ b) : fanStart a ≤ fanStart b := by
  induction b with
  | zero => obtain rfl : a = 0 := by omega
            exact le_rfl
  | succ b ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | hlt
    · exact le_rfl
    · have := ih (by omega)
      rcases Nat.eq_zero_or_pos b with rfl | hb
      · simp [fanStart] at this ⊢; omega
      · rw [fanStart_succ hb]; omega

theorem roundOf_eq {p i : ℕ} (hi : 1 ≤ i) (h1 : fanStart i ≤ p) (h2 : p < fanStart (i + 1)) :
    roundOf p = i := by
  unfold roundOf
  rw [Nat.find_eq_iff]
  refine ⟨h2, fun i' hi' => ?_⟩
  have := fanStart_le (show i' + 1 ≤ i by omega)
  omega

theorem fanout_at {i m : ℕ} (hi : 1 ≤ i) (hm : m < 3 * i + 2) :
    fanout j (fanStart i + m) = fanParent j i m := by
  have hS := fanStart_ge i
  unfold fanout
  rw [if_neg (by omega), roundOf_eq hi (by omega) (by rw [fanStart_succ hi]; omega),
    Nat.add_sub_cancel_left]

theorem fanout_one : fanout j 1 = 0 := by simp [fanout]

/-- Every position `2 ≤ p` lies in a round. -/
theorem fan_pos_cases (p : ℕ) (hp : 2 ≤ p) :
    ∃ i m, 1 ≤ i ∧ m < 3 * i + 2 ∧ p = fanStart i + m := by
  have hspec := Nat.find_spec (exists_round p)
  have hmin := fun k (hk : k < Nat.find (exists_round p)) => Nat.find_min (exists_round p) hk
  set i := Nat.find (exists_round p)
  have hi : 1 ≤ i := by
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · rw [h0] at hspec; simp [fanStart] at hspec; omega
    · exact h0
  have hlow : fanStart i ≤ p := by
    have := hmin (i - 1) (by omega)
    rw [show i - 1 + 1 = i by omega] at this; omega
  rw [fanStart_succ hi] at hspec
  exact ⟨i, p - fanStart i, hi, by omega, by omega⟩

/-- The new array is a parent array. -/
theorem fanout_isParentArray (n : ℕ) (hj : IsParentArray n j) :
    IsParentArray (fanLen n) (fanout j) := by
  intro p h1 hp
  rcases Nat.lt_or_ge p 2 with h | h
  · obtain rfl : p = 1 := by omega
    rw [fanout_one]; omega
  obtain ⟨i, m, hi, hm, rfl⟩ := fan_pos_cases p h
  rw [fanout_at j hi hm]
  have hS := fanStart_ge i
  have hin : i ≤ n := by
    by_contra hni
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; unfold fanLen at hp; simp [fanStart] at hp; omega
    · have := fanStart_mono hpos (show n < i by omega); unfold fanLen at hp; omega
  unfold fanParent busPrev
  split_ifs <;> try omega
  · have := hj i hi hin; omega
  · rcases Nat.eq_or_lt_of_le (show 2 ≤ i by omega) with rfl | hlt
    · simp [fanStart]; omega
    · have := fanStart_succ (show 1 ≤ i - 1 by omega)
      rw [show i - 1 + 1 = i by omega] at this; omega
  · have := fanStart_succ (show 1 ≤ i - 1 by omega)
    rw [show i - 1 + 1 = i by omega] at this; omega

theorem fanParent_a {i k : ℕ} (hi : 1 ≤ i) (hk : k ≤ i - 1) :
    fanParent j i (3 * k) = busPrev i k := by
  unfold fanParent
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  congr 1; omega

theorem fanParent_b {i k : ℕ} (hi : 1 ≤ i) (hk : k ≤ i - 1) :
    fanParent j i (3 * k + 1) = fanStart i + 3 * k - 1 := by
  unfold fanParent
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  omega

theorem fanParent_c {i k : ℕ} (hi : 1 ≤ i) (hk : k + 2 ≤ i) :
    fanParent j i (3 * k + 2) = fanStart i + 3 * k := by
  unfold fanParent
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  omega

theorem fanParent_y (i : ℕ) : fanParent j i (3 * i - 1) = fanStart i + 3 * j i + 1 := by
  unfold fanParent; rw [if_pos rfl]

theorem fanParent_g1 {i : ℕ} (hi : 1 ≤ i) : fanParent j i (3 * i) = fanStart i + 3 * i - 4 := by
  unfold fanParent; rw [if_neg (by omega), if_pos rfl]

theorem fanParent_g2 {i : ℕ} (hi : 1 ≤ i) :
    fanParent j i (3 * i + 1) = fanStart i + 3 * i - 1 := by
  unfold fanParent; rw [if_neg (by omega), if_neg (by omega), if_pos rfl]

theorem busPrev_lt {i k : ℕ} (hi : 1 ≤ i) : busPrev i k < fanStart i := by
  have hS := fanStart_ge i
  unfold busPrev
  split_ifs with h1 h2
  · omega
  · have := fanStart_succ (show 1 ≤ i - 1 by omega)
    rw [show i - 1 + 1 = i by omega] at this; omega
  · have := fanStart_succ (show 1 ≤ i - 1 by omega)
    rw [show i - 1 + 1 = i by omega] at this; omega

/-- The values of one round. -/
theorem round_values (n : ℕ) (hj : IsParentArray n j) (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n)
    (hrail : trace (fanout j) (fanStart i - 1) = false)
    (hbus : ∀ k, k ≤ i - 1 → trace (fanout j) (busPrev i k) = trace j k) :
    (∀ k, k ≤ i - 1 → trace (fanout j) (fanStart i + 3 * k + 1) = trace j k) ∧
    trace (fanout j) (fanStart i + 3 * i - 1) = trace j i ∧
    trace (fanout j) (fanStart i + 3 * i + 1) = false := by
  have hS := fanStart_ge i
  have hstep : ∀ m p, m < 3 * i + 2 → fanParent j i m = p → p < fanStart i + m →
      trace (fanout j) (fanStart i + m) =
        nor (trace (fanout j) (fanStart i + m - 1)) (trace (fanout j) p) := by
    intro m p hm hp hlt
    exact trace_step _ _ p (by omega) (by rw [fanout_at j hi hm, hp]) hlt
  -- the blocks `k = 0, …, i-1`
  have blocks : ∀ k, k ≤ i - 1 →
      trace (fanout j) (fanStart i + 3 * k) = !trace j k ∧
      trace (fanout j) (fanStart i + (3 * k + 1)) = trace j k ∧
      (k + 2 ≤ i → trace (fanout j) (fanStart i + (3 * k + 2)) = false) := by
    intro k
    induction k with
    | zero =>
      intro _
      have ea : trace (fanout j) (fanStart i + 3 * 0) = !trace j 0 := by
        rw [hstep (3 * 0) _ (by omega) (fanParent_a j hi (by omega)) (by
            have := busPrev_lt (k := 0) hi; omega),
          show fanStart i + 3 * 0 - 1 = fanStart i - 1 by omega, hrail, hbus 0 (by omega)]
        cases trace j 0 <;> rfl
      have eb : trace (fanout j) (fanStart i + (3 * 0 + 1)) = trace j 0 := by
        rw [hstep _ _ (by omega) (fanParent_b j hi (by omega)) (by omega),
          show fanStart i + (3 * 0 + 1) - 1 = fanStart i + 3 * 0 by omega, ea,
          show fanStart i + 3 * 0 - 1 = fanStart i - 1 by omega, hrail]
        cases trace j 0 <;> rfl
      refine ⟨ea, eb, fun hk => ?_⟩
      rw [hstep _ _ (by omega) (fanParent_c j hi hk) (by omega),
        show fanStart i + (3 * 0 + 2) - 1 = fanStart i + (3 * 0 + 1) by omega, eb, ea]
      cases trace j 0 <;> rfl
    | succ k ih =>
      intro hk
      have hc' := (ih (by omega)).2.2 (by omega)
      have ea : trace (fanout j) (fanStart i + 3 * (k + 1)) = !trace j (k + 1) := by
        rw [hstep (3 * (k + 1)) _ (by omega) (fanParent_a j hi (by omega)) (by
            have := busPrev_lt (k := k + 1) hi; omega),
          show fanStart i + 3 * (k + 1) - 1 = fanStart i + (3 * k + 2) by omega, hc',
          hbus (k + 1) (by omega)]
        cases trace j (k + 1) <;> rfl
      have eb : trace (fanout j) (fanStart i + (3 * (k + 1) + 1)) = trace j (k + 1) := by
        rw [hstep _ _ (by omega) (fanParent_b j hi (by omega)) (by omega),
          show fanStart i + (3 * (k + 1) + 1) - 1 = fanStart i + 3 * (k + 1) by omega, ea,
          show fanStart i + 3 * (k + 1) - 1 = fanStart i + (3 * k + 2) by omega, hc']
        cases trace j (k + 1) <;> rfl
      refine ⟨ea, eb, fun hk2 => ?_⟩
      rw [hstep _ _ (by omega) (fanParent_c j hi hk2) (by omega),
        show fanStart i + (3 * (k + 1) + 2) - 1 = fanStart i + (3 * (k + 1) + 1) by omega, eb, ea]
      cases trace j (k + 1) <;> rfl
  have hji := hj i hi hin
  have eb_last := (blocks (i - 1) le_rfl).2.1
  have ey : trace (fanout j) (fanStart i + (3 * i - 1)) = trace j i := by
    rw [hstep _ _ (by omega) (fanParent_y j i) (by omega),
      show fanStart i + (3 * i - 1) - 1 = fanStart i + (3 * (i - 1) + 1) by omega, eb_last,
      show fanStart i + 3 * j i + 1 = fanStart i + (3 * j i + 1) by omega,
      (blocks (j i) (by omega)).2.1, trace_at j i hi hji]
  -- the rail before step 2
  have hrail2 : trace (fanout j) (fanStart i + 3 * i - 4) = false := by
    rcases Nat.eq_or_lt_of_le hi with rfl | hlt
    · rw [show fanStart 1 + 3 * 1 - 4 = fanStart 1 - 1 by omega]; exact hrail
    · have := (blocks (i - 2) (by omega)).2.2 (by omega)
      rwa [show fanStart i + (3 * (i - 2) + 2) = fanStart i + 3 * i - 4 by omega] at this
  have eg1 : trace (fanout j) (fanStart i + 3 * i) = !trace j i := by
    rw [hstep _ _ (by omega) (fanParent_g1 j hi) (by omega),
      show fanStart i + 3 * i - 1 = fanStart i + (3 * i - 1) by omega, ey, hrail2]
    cases trace j i <;> rfl
  have eg2 : trace (fanout j) (fanStart i + (3 * i + 1)) = false := by
    rw [hstep _ _ (by omega) (fanParent_g2 j hi) (by omega),
      show fanStart i + (3 * i + 1) - 1 = fanStart i + 3 * i by omega, eg1,
      show fanStart i + 3 * i - 1 = fanStart i + (3 * i - 1) by omega, ey]
    cases trace j i <;> rfl
  refine ⟨fun k hk => ?_, ?_, ?_⟩
  · rw [show fanStart i + 3 * k + 1 = fanStart i + (3 * k + 1) by omega]
    exact (blocks k hk).2.1
  · rw [show fanStart i + 3 * i - 1 = fanStart i + (3 * i - 1) by omega]; exact ey
  · rw [show fanStart i + 3 * i + 1 = fanStart i + (3 * i + 1) by omega]; exact eg2

/-- **Theorem 5.1 of 006c (value).** The last position of the normalized instance holds
`x_n`. -/
theorem fanout_value (n : ℕ) (hn : 1 ≤ n) (hj : IsParentArray n j) :
    trace (fanout j) (fanLen n) = trace j n := by
  have inv : ∀ i, 1 ≤ i → i ≤ n →
      trace (fanout j) (fanStart i - 1) = false ∧
      ∀ k, k ≤ i - 1 → trace (fanout j) (busPrev i k) = trace j k := by
    intro i hi hin
    induction i with
    | zero => omega
    | succ i ih =>
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · refine ⟨?_, fun k hk => ?_⟩
        · have : fanStart (0 + 1) - 1 = 1 := rfl
          rw [this, trace_step _ 1 0 le_rfl (fanout_one j) (by omega)]
          simp [trace_zero, nor]
        · obtain rfl : k = 0 := by omega
          simp [busPrev, trace_zero]
      · obtain ⟨hr, hb⟩ := ih hpos (by omega)
        obtain ⟨h1, h2, h3⟩ := round_values j n hj i hpos (by omega) hr hb
        refine ⟨?_, fun k hk => ?_⟩
        · rw [fanStart_succ hpos, show fanStart i + 3 * i + 2 - 1 = fanStart i + 3 * i + 1 by omega]
          exact h3
        · unfold busPrev
          rw [if_neg (by omega), Nat.add_sub_cancel]
          split_ifs with hk2
          · exact h1 k (by omega)
          · rw [show k = i by omega]; exact h2
  obtain ⟨hr, hb⟩ := inv n hn le_rfl
  exact (round_values j n hj n hn le_rfl hr hb).2.1

/-- Candidate children of a position: every position `q` with `fanout j q = p` lies in this
set of at most two elements. -/
def fanChildren (p : ℕ) : Finset ℕ :=
  if p = 0 then {1, fanStart 1}
  else if p = 1 then {fanStart 1 + 1, fanStart 1 + 3}
  else
    let i := roundOf p
    let m := p - fanStart i
    if m = 3 * i - 1 then {fanStart i + 3 * i + 1, fanStart (i + 1) + 3 * i}
    else if m = 3 * i + 1 then {fanStart (i + 1) + 1}
    else if m % 3 = 1 then {fanStart (i + 1) + (m - 1), fanStart i + 3 * i - 1}
    else if m % 3 = 2 then {fanStart i + m + 2, fanStart i + 3 * i}
    else {fanStart i + m + 2}

theorem fanChildren_card (p : ℕ) : (fanChildren p).card ≤ 2 := by
  unfold fanChildren
  split_ifs
  · exact Finset.card_le_two
  · exact Finset.card_le_two
  · dsimp only
    split_ifs <;> first | exact Finset.card_le_two | simp

theorem fanChildren_at {i m : ℕ} (hi : 1 ≤ i) (hm : m < 3 * i + 2) :
    fanChildren (fanStart i + m) =
      if m = 3 * i - 1 then {fanStart i + 3 * i + 1, fanStart (i + 1) + 3 * i}
      else if m = 3 * i + 1 then {fanStart (i + 1) + 1}
      else if m % 3 = 1 then {fanStart (i + 1) + (m - 1), fanStart i + 3 * i - 1}
      else if m % 3 = 2 then {fanStart i + m + 2, fanStart i + 3 * i}
      else {fanStart i + m + 2} := by
  have hS := fanStart_ge i
  unfold fanChildren
  rw [if_neg (by omega), if_neg (by omega)]
  simp only []
  rw [roundOf_eq hi (by omega) (by rw [fanStart_succ hi]; omega), Nat.add_sub_cancel_left]

/-- Every child of `p` is a candidate child. -/
theorem mem_fanChildren (n : ℕ) (hj : IsParentArray n j) (q : ℕ) (hq : 1 ≤ q)
    (hqn : q ≤ fanLen n) : q ∈ fanChildren (fanout j q) := by
  rcases Nat.lt_or_ge q 2 with h | h
  · obtain rfl : q = 1 := by omega
    rw [fanout_one]; simp [fanChildren]
  obtain ⟨i, m, hi, hm, rfl⟩ := fan_pos_cases q h
  have hS := fanStart_ge i
  have hin : i ≤ n := by
    by_contra hni
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; unfold fanLen at hqn; simp [fanStart] at hqn; omega
    · have := fanStart_mono hpos (show n < i by omega)
      unfold fanLen at hqn; omega
  have hsucc := fanStart_succ hi
  rw [fanout_at j hi hm]
  unfold fanParent
  by_cases hy : m = 3 * i - 1
  · -- `y`: parent is the `b` of block `j_i`
    have hji := hj i hi hin
    rw [if_pos hy, show fanStart i + 3 * j i + 1 = fanStart i + (3 * j i + 1) by omega,
      fanChildren_at (m := 3 * j i + 1) hi (by omega)]
    rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    simp; omega
  rw [if_neg hy]
  by_cases hg1 : m = 3 * i
  · -- `g₁`: parent is the rail before step 2
    rw [if_pos hg1]
    rcases Nat.eq_or_lt_of_le hi with rfl | hlt
    · have : fanStart 1 + 3 * 1 - 4 = 1 := rfl
      rw [this]; simp [fanChildren]; omega
    · rw [show fanStart i + 3 * i - 4 = fanStart i + (3 * (i - 2) + 2) by omega,
        fanChildren_at hi (by omega)]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
      simp; omega
  rw [if_neg hg1]
  by_cases hg2 : m = 3 * i + 1
  · -- `g₂`: parent is `y`
    rw [if_pos hg2, show fanStart i + 3 * i - 1 = fanStart i + (3 * i - 1) by omega,
      fanChildren_at hi (by omega), if_pos rfl]
    simp; omega
  rw [if_neg hg2]
  by_cases ha : m % 3 = 0
  · -- `a`: parent is the bus position `B_{m/3}`
    rw [if_pos ha]
    unfold busPrev
    split_ifs with h1 h2
    · obtain rfl : i = 1 := by omega
      obtain rfl : m = 0 := by omega
      simp [fanChildren]
    · -- `b` of the previous round
      have hprev := fanStart_succ (show 1 ≤ i - 1 by omega)
      rw [show i - 1 + 1 = i by omega] at hprev
      rw [show fanStart (i - 1) + 3 * (m / 3) + 1 = fanStart (i - 1) + (3 * (m / 3) + 1) by omega,
        fanChildren_at (show 1 ≤ i - 1 by omega) (by omega)]
      rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
      rw [show i - 1 + 1 = i by omega]
      simp; omega
    · -- `y` of the previous round
      have hprev := fanStart_succ (show 1 ≤ i - 1 by omega)
      rw [show i - 1 + 1 = i by omega] at hprev
      rw [show fanStart (i - 1) + 3 * (i - 1) - 1 = fanStart (i - 1) + (3 * (i - 1) - 1) by omega,
        fanChildren_at (show 1 ≤ i - 1 by omega) (by omega), if_pos rfl,
        show i - 1 + 1 = i by omega]
      simp; omega
  rw [if_neg ha]
  by_cases hb : m % 3 = 1
  · -- `b`: parent is the current rail
    rcases Nat.eq_or_lt_of_le (show 1 ≤ m by omega) with hm1 | hm1
    · subst hm1
      rcases Nat.eq_or_lt_of_le hi with rfl | hlt
      · have : fanStart 1 + 1 - 2 = 1 := rfl
        rw [this]; simp [fanChildren]
      · have hprev := fanStart_succ (show 1 ≤ i - 1 by omega)
        rw [show i - 1 + 1 = i by omega] at hprev
        rw [show fanStart i + 1 - 2 = fanStart (i - 1) + (3 * (i - 1) + 1) by omega,
          fanChildren_at (show 1 ≤ i - 1 by omega) (by omega), if_neg (by omega), if_pos rfl,
          show i - 1 + 1 = i by omega]
        simp
    · rw [show fanStart i + m - 2 = fanStart i + (m - 2) by omega, fanChildren_at hi (by omega)]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
      simp; omega
  · -- `c`: parent is the `a` of the same block
    rw [show fanStart i + m - 2 = fanStart i + (m - 2) by omega, fanChildren_at hi (by omega)]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    simp; omega

/-- **Theorem 5.1 of 006c (fan-out normalization).** For every parent array `j` of length
`n ≥ 1`, `fanout j` is a parent array of length `S_n + 3n - 1 = O(n²)` with the same output
bit, in which every position is the parent of at most two positions. -/
theorem fanout_normalization (n : ℕ) (hn : 1 ≤ n) (hj : IsParentArray n j) :
    IsParentArray (fanLen n) (fanout j) ∧
    trace (fanout j) (fanLen n) = trace j n ∧
    (∀ p, ((Finset.Icc 1 (fanLen n)).filter (fun q => fanout j q = p)).card ≤ 2) ∧
    fanLen n ≤ 3 * n * n + 2 * n + 1 := by
  refine ⟨fanout_isParentArray j n hj, fanout_value j n hn hj, ?_, ?_⟩
  · intro p
    refine le_trans (Finset.card_le_card ?_) (fanChildren_card p)
    intro q hq
    rw [Finset.mem_filter, Finset.mem_Icc] at hq
    obtain ⟨⟨h1, h2⟩, hp⟩ := hq
    rw [← hp]
    exact mem_fanChildren j n hj q h1 h2
  · have : ∀ i, 1 ≤ i → fanStart i + 3 * i ≤ 3 * i * i + 2 * i + 2 := by
      intro i hi
      induction i with
      | zero => omega
      | succ i ih =>
        rcases Nat.eq_zero_or_pos i with rfl | hpos
        · simp [fanStart]
        · rw [fanStart_succ hpos]; have := ih hpos; nlinarith
    have := this n hn
    unfold fanLen; omega

end

end GC.SeqNORNormalForms
