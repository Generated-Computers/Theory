import GC.Computability.SeqNORNormalForms.Basic
import Mathlib.Data.Fintype.Pi

/-!
# 006e: blockwise causal recovery of the bad-shield values

Bad shields `H(j) = {h ∈ [1, n-1] : j_h ≠ 0, 1 ≤ j_{h+1} ≤ h - 1}` with ranks
`1, …, b`. For an assignment `γ` (indexed by rank) the candidate `Y(γ)` sets `y_0 = 1`,
`y_{h_k} = γ_k` and `y_q = NOR(y_{q-1}, y_{j_q})` elsewhere. Stage `s` (with `a = s g`)
tries all `2^g` branches `α` for the ranks `a+1, …, a+g`, keeps the valid ones (padding bits
`0`, deferred equations satisfied) and outputs `β_{a+t} = ⋁_α (V_α ∧ α_t)`.

The circuit size/depth bounds are not formalized; we formalize the correctness of this
explicitly defined schedule, including its number of stages `⌈r/g⌉`.
-/

namespace GC.SeqNORNormalForms

/-- `h` is a bad shield of the parent array `j` of length `n`. -/
def IsBad (n : ℕ) (j : ℕ → ℕ) (h : ℕ) : Prop :=
  1 ≤ h ∧ h + 1 ≤ n ∧ j h ≠ 0 ∧ 1 ≤ j (h + 1) ∧ j (h + 1) + 1 ≤ h

instance (n : ℕ) (j : ℕ → ℕ) (h : ℕ) : Decidable (IsBad n j h) := by
  unfold IsBad; infer_instance

/-- `badRank q = |H(j) ∩ [1, q]|`; the rank of a bad shield `h` is `badRank h`. -/
def badRank (n : ℕ) (j : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | q + 1 => badRank n j q + if IsBad n j (q + 1) then 1 else 0

/-- `b = |H(j)|`. -/
def numBad (n : ℕ) (j : ℕ → ℕ) : ℕ := badRank n j n

/-- The candidate `Y(γ)` for an assignment `γ` indexed by rank (Section 3 of 006e). -/
def cand (n : ℕ) (j : ℕ → ℕ) (γ : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | q + 1 =>
      if IsBad n j (q + 1) then γ (badRank n j (q + 1))
      else nor (cand n j γ q) (if h : j (q + 1) < q + 1 then cand n j γ (j (q + 1)) else true)
termination_by q => q

/-- The assignment `γ^{s,α}` of stage `s` (Section 5 of 006e), with `a = s g`. -/
def branchAssign (β : ℕ → Bool) (a g : ℕ) (α : Fin g → Bool) (k : ℕ) : Bool :=
  if h1 : k ≤ a then β k
  else if h2 : k ≤ a + g then α ⟨k - a - 1, by omega⟩
  else false

/-- The validity bit `V_{s,α}`: padding bits are `0` and the deferred equations of the
ranks `a+1, …, min(a+g, b)` hold (Section 5 of 006e). -/
def BranchValid (n : ℕ) (j : ℕ → ℕ) (β : ℕ → Bool) (a g : ℕ) (α : Fin g → Bool) : Prop :=
  (∀ t : Fin g, numBad n j < a + t.val + 1 → α t = false) ∧
  (∀ h, IsBad n j h → a < badRank n j h → badRank n j h ≤ a + g →
    branchAssign β a g α (badRank n j h) =
      nor (cand n j (branchAssign β a g α) (h - 1)) (cand n j (branchAssign β a g α) (j h)))

open Classical in
/-- Stage `s` of the blockwise compiler: `β_{a+t} = ⋁_α (V_{s,α} ∧ α_t)`. -/
noncomputable def stage (n : ℕ) (j : ℕ → ℕ) (g s : ℕ) (β : ℕ → Bool) : ℕ → Bool := fun k =>
  if h1 : k ≤ s * g then β k
  else if h : k ≤ s * g + g then
    decide (∃ α : Fin g → Bool, BranchValid n j β (s * g) g α ∧ α ⟨k - s * g - 1, by omega⟩ = true)
  else false

/-- The bits after `s` stages, starting from all zeros. -/
noncomputable def recover (n : ℕ) (j : ℕ → ℕ) (g : ℕ) : ℕ → ℕ → Bool
  | 0 => fun _ => false
  | s + 1 => stage n j g s (recover n j g s)

section

variable (n : ℕ) (j : ℕ → ℕ)

theorem cand_zero (γ : ℕ → Bool) : cand n j γ 0 = true := by rw [cand]

theorem cand_at (γ : ℕ → Bool) (q : ℕ) (hq : 1 ≤ q) (hjq : j q < q) :
    cand n j γ q = if IsBad n j q then γ (badRank n j q)
      else nor (cand n j γ (q - 1)) (cand n j γ (j q)) := by
  obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  rw [cand]; simp [hjq]

theorem badRank_succ (q : ℕ) :
    badRank n j (q + 1) = badRank n j q + if IsBad n j (q + 1) then 1 else 0 := rfl

theorem badRank_mono {q q' : ℕ} (h : q ≤ q') : badRank n j q ≤ badRank n j q' := by
  induction q' with
  | zero => obtain rfl : q = 0 := by omega
            exact le_rfl
  | succ q' ih =>
    rcases Nat.lt_or_ge q (q' + 1) with h' | h'
    · rw [badRank_succ]; have := ih (by omega); omega
    · obtain rfl : q = q' + 1 := by omega
      exact le_rfl

theorem badRank_bad {h : ℕ} (hb : IsBad n j h) : badRank n j h = badRank n j (h - 1) + 1 := by
  obtain ⟨h, rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by have := hb.1; omega⟩
  rw [badRank_succ, if_pos hb]; simp

theorem badRank_lt {h h' : ℕ} (hb : IsBad n j h) (hh : h' < h) :
    badRank n j h' < badRank n j h := by
  rw [badRank_bad n j hb]; have := badRank_mono n j (show h' ≤ h - 1 by omega); omega

theorem badRank_inj {h h' : ℕ} (hb : IsBad n j h) (hb' : IsBad n j h')
    (he : badRank n j h = badRank n j h') : h = h' := by
  rcases lt_trichotomy h h' with hl | rfl | hl
  · have := badRank_lt n j hb' hl; omega
  · rfl
  · have := badRank_lt n j hb hl; omega

theorem badRank_le_num {h : ℕ} (hb : IsBad n j h) : badRank n j h ≤ numBad n j :=
  badRank_mono n j (by have := hb.2.1; omega)

theorem badRank_surj : ∀ N k, 1 ≤ k → k ≤ badRank n j N → ∃ h, IsBad n j h ∧ h ≤ N ∧ badRank n j h = k := by
  intro N
  induction N with
  | zero => intro k hk hk'; simp [badRank] at hk'; omega
  | succ N ih =>
    intro k hk hk'
    rw [badRank_succ] at hk'
    by_cases hkN : k ≤ badRank n j N
    · obtain ⟨h, h1, h2, h3⟩ := ih k hk hkN; exact ⟨h, h1, by omega, h3⟩
    · by_cases hb : IsBad n j (N + 1)
      · rw [if_pos hb] at hk'
        refine ⟨N + 1, hb, le_rfl, ?_⟩
        rw [badRank_succ, if_pos hb]; omega
      · rw [if_neg hb] at hk'; omega

/-- **Corollary 4.2 of 006e (true-prefix recovery).** If `γ` gives the true value to every bad
shield `h ≤ t`, then `Y(γ)` agrees with the trace on `0, …, t`. -/
theorem cand_true_prefix (hj : IsParentArray n j) (γ : ℕ → Bool) (t : ℕ)
    (hγ : ∀ h, IsBad n j h → h ≤ t → γ (badRank n j h) = trace j h) :
    ∀ q, q ≤ t → q ≤ n → cand n j γ q = trace j q := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro hqt hqn
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · rw [cand_zero, trace_zero]
    have hjq := hj q hq hqn
    rw [cand_at n j γ q hq hjq]
    split
    · next hb => exact hγ q hb hqt
    · rw [ih (q - 1) (by omega) (by omega) (by omega), ih (j q) hjq (by omega) (by omega),
        trace_at j q hq hjq]

/-- **Lemma 4.1 of 006e (prefix locality).** If `γ` and `γ'` agree on the ranks of the bad
shields `≤ t`, then `Y(γ)` and `Y(γ')` agree on `0, …, t`. -/
theorem cand_prefix_locality (hj : IsParentArray n j) (γ γ' : ℕ → Bool) (t : ℕ)
    (hγ : ∀ h, IsBad n j h → h ≤ t → γ (badRank n j h) = γ' (badRank n j h)) :
    ∀ q, q ≤ t → q ≤ n → cand n j γ q = cand n j γ' q := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro hqt hqn
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · rw [cand_zero, cand_zero]
    have hjq := hj q hq hqn
    rw [cand_at n j γ q hq hjq, cand_at n j γ' q hq hjq]
    split
    · next hb => exact hγ q hb hqt
    · rw [ih (q - 1) (by omega) (by omega) (by omega), ih (j q) hjq (by omega) (by omega)]

/-- The invariant before a stage with `a = s g`: `β` is correct on the ranks `≤ a` and `0`
on the padding ranks `b < k ≤ a`. -/
def StageInv (β : ℕ → Bool) (a : ℕ) : Prop :=
  (∀ h, IsBad n j h → badRank n j h ≤ a → β (badRank n j h) = trace j h) ∧
  (∀ k, numBad n j < k → k ≤ a → β k = false)

open Classical in
/-- The true branch: `α⋆_t = x_{h_{a+t+1}}` if that rank exists, `0` otherwise. -/
noncomputable def trueBranch (a g : ℕ) (t : Fin g) : Bool :=
  decide (∃ h, IsBad n j h ∧ badRank n j h = a + t.val + 1 ∧ trace j h = true)

open Classical in
theorem trueBranch_eq (a g : ℕ) (h : ℕ) (hb : IsBad n j h) (t : Fin g)
    (ht : badRank n j h = a + t.val + 1) : trueBranch n j a g t = trace j h := by
  unfold trueBranch
  by_cases hx : trace j h = true
  · rw [hx]; exact decide_eq_true ⟨h, hb, ht, hx⟩
  · rw [Bool.not_eq_true] at hx
    rw [hx]
    apply decide_eq_false
    rintro ⟨h', hb', ht', hx'⟩
    rw [badRank_inj n j hb hb' (by omega)] at hx
    rw [hx] at hx'; exact absurd hx' (by decide)

open Classical in
theorem trueBranch_pad (a g : ℕ) (t : Fin g) (ht : numBad n j < a + t.val + 1) :
    trueBranch n j a g t = false := by
  unfold trueBranch
  apply decide_eq_false
  rintro ⟨h, hb, hr, -⟩
  have := badRank_le_num n j hb; omega

/-- Under the invariant, a branch assignment that is correct up to (but excluding) the bad
shield `h` gives the correct value to the deferred equation of `h`. -/
theorem deferred_true (hj : IsParentArray n j) (γ : ℕ → Bool) (h : ℕ) (hb : IsBad n j h)
    (hγ : ∀ h', IsBad n j h' → h' < h → γ (badRank n j h') = trace j h') :
    nor (cand n j γ (h - 1)) (cand n j γ (j h)) = trace j h := by
  have h1 := hb.1
  have hn : h ≤ n := by have := hb.2.1; omega
  have hjh := hj h h1 hn
  rw [cand_true_prefix n j hj γ (h - 1) (fun h' hb' hh' => hγ h' hb' (by omega)) (h - 1) le_rfl
      (by omega),
    cand_true_prefix n j hj γ (h - 1) (fun h' hb' hh' => hγ h' hb' (by omega)) (j h) (by omega)
      (by omega), trace_at j h h1 hjh]

/-- **Lemma 5.1 of 006e (unique valid branch).** Under the invariant, the valid branches of
stage `s` are exactly the true branch. -/
theorem unique_valid_branch (hj : IsParentArray n j) (β : ℕ → Bool) (a g : ℕ)
    (hinv : StageInv n j β a) (α : Fin g → Bool) :
    BranchValid n j β a g α ↔ α = trueBranch n j a g := by
  -- correctness of the assignment on ranks `≤ a`
  have base : ∀ (α : Fin g → Bool) h, IsBad n j h → badRank n j h ≤ a →
      branchAssign β a g α (badRank n j h) = trace j h := by
    intro α h hb hr
    unfold branchAssign; rw [dif_pos hr]; exact hinv.1 h hb hr
  -- the true branch gives true values on the block
  have tb : ∀ h, IsBad n j h → badRank n j h ≤ a + g →
      branchAssign β a g (trueBranch n j a g) (badRank n j h) = trace j h := by
    intro h hb hr
    by_cases hra : badRank n j h ≤ a
    · exact base _ h hb hra
    · unfold branchAssign
      rw [dif_neg hra, dif_pos hr]
      exact trueBranch_eq n j a g h hb _ (by simp; omega)
  constructor
  · rintro ⟨hpad, hcheck⟩
    -- by induction over the bad shields of the block, the branch is correct
    have hcorr : ∀ h, IsBad n j h → badRank n j h ≤ a + g →
        branchAssign β a g α (badRank n j h) = trace j h := by
      intro h
      induction h using Nat.strong_induction_on with
      | _ h ih =>
        intro hb hr
        by_cases hra : badRank n j h ≤ a
        · exact base α h hb hra
        · rw [hcheck h hb (by omega) hr]
          apply deferred_true n j hj _ h hb
          intro h' hb' hh'
          exact ih h' hh' hb' (by have := badRank_lt n j hb hh'; omega)
    funext t
    by_cases hex : ∃ h, IsBad n j h ∧ badRank n j h = a + t.val + 1
    · obtain ⟨h, hb, hr⟩ := hex
      rw [trueBranch_eq n j a g h hb t hr]
      have := hcorr h hb (by omega)
      unfold branchAssign at this
      rw [dif_neg (by omega), dif_pos (by omega)] at this
      rw [← this]; congr 1; ext; simp; omega
    · have hpad' : numBad n j < a + t.val + 1 := by
        by_contra hle
        obtain ⟨h, hb, -, hr⟩ := badRank_surj n j n (a + t.val + 1) (by omega) (by
          unfold numBad at hle; omega)
        exact hex ⟨h, hb, hr⟩
      rw [hpad t hpad', trueBranch_pad n j a g t hpad']
  · rintro rfl
    refine ⟨fun t ht => trueBranch_pad n j a g t ht, ?_⟩
    intro h hb hra hr
    rw [tb h hb hr]
    symm
    apply deferred_true n j hj _ h hb
    intro h' hb' hh'
    exact tb h' hb' (by have := badRank_lt n j hb hh'; omega)

open Classical in
/-- One stage preserves the invariant, with `a` replaced by `a + g`. -/
theorem stage_inv (hj : IsParentArray n j) (g s : ℕ) (β : ℕ → Bool)
    (hinv : StageInv n j β (s * g)) : StageInv n j (stage n j g s β) (s * g + g) := by
  have key : ∀ k (h1 : ¬ k ≤ s * g) (h2 : k ≤ s * g + g),
      stage n j g s β k = trueBranch n j (s * g) g ⟨k - s * g - 1, by omega⟩ := by
    intro k h1 h2
    unfold stage
    rw [dif_neg h1, dif_pos h2]
    have hval := unique_valid_branch n j hj β (s * g) g hinv
    by_cases ht : trueBranch n j (s * g) g ⟨k - s * g - 1, by omega⟩ = true
    · rw [ht]
      exact decide_eq_true ⟨_, (hval _).2 rfl, ht⟩
    · rw [Bool.not_eq_true] at ht
      rw [ht]
      apply decide_eq_false
      rintro ⟨α, hv, hα⟩
      rw [(hval α).1 hv] at hα
      rw [hα] at ht; exact absurd ht (by decide)
  constructor
  · intro h hb hr
    by_cases hra : badRank n j h ≤ s * g
    · unfold stage; rw [dif_pos hra]; exact hinv.1 h hb hra
    · rw [key _ hra hr]
      exact trueBranch_eq n j _ g h hb _ (by simp; omega)
  · intro k hk hka
    by_cases hra : k ≤ s * g
    · unfold stage; rw [dif_pos hra]; exact hinv.2 k hk hra
    · rw [key _ hra hka]
      exact trueBranch_pad n j _ g _ (by simp; omega)

/-- **Theorem 5.2 of 006e (blockwise causal compiler), correctness.** On the promise
`|H(j)| ≤ r`, with block width `g ≥ 1`, after `T = ⌈r/g⌉` stages the recovered bits are the
true values of all bad shields, and the candidate `Y(β)` is the trace of `j`. -/
theorem blockwise_correct (hj : IsParentArray n j) (g r : ℕ) (hg : 1 ≤ g)
    (hr : numBad n j ≤ r) :
    let β := recover n j g ((r + g - 1) / g)
    (∀ h, IsBad n j h → β (badRank n j h) = trace j h) ∧
    ∀ q, q ≤ n → cand n j β q = trace j q := by
  intro β
  have hinv : ∀ s, StageInv n j (recover n j g s) (s * g) := by
    intro s
    induction s with
    | zero =>
      refine ⟨fun h hb hr0 => ?_, fun k hk hk0 => ?_⟩
      · have := badRank_bad n j hb; simp at hr0; omega
      · rfl
    | succ s ih =>
      have := stage_inv n j hj g s _ ih
      rwa [show (s + 1) * g = s * g + g by ring]
  have hT : r ≤ (r + g - 1) / g * g := by
    have := Nat.div_add_mod (r + g - 1) g
    have := Nat.mod_lt (r + g - 1) (show 0 < g by omega)
    rw [Nat.mul_comm]
    omega
  have h1 : ∀ h, IsBad n j h → β (badRank n j h) = trace j h := by
    intro h hb
    exact (hinv _).1 h hb (by have := badRank_le_num n j hb; omega)
  exact ⟨h1, fun q hq => cand_true_prefix n j hj β n (fun h hb _ => h1 h hb) q hq hq⟩

end

end GC.SeqNORNormalForms
