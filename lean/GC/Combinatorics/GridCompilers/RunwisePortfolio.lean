import GC.Combinatorics.GridCompilers.RowPartitions
import GC.Combinatorics.GridCompilers.ThreeCompilers

/-!
# A runwise portfolio of NC grid compilers (manuscript 009c): exact lemmas

The portfolio theorem (Theorem 3.2), which is an `FNC^k` statement, is *not* formalized. We
formalize its combinatorial ingredients:

* `portfolio_sound`, `portfolio_isSome_iff` (Lemma 3.1, finite portfolios): choosing the first
  passing compiler is sound, its pass bit is the OR of the pass bits, and the choice depends only
  on the block, not on the north word.
* `gamma_ge_min_segments` (Lemma 4.1, proved in `RowPartitions.lean`).
* `gamma_two_bands` (second run of Proposition 4.2): two homogeneous bands give `Γ ≤ 2`.
* `gamma_common_core` (Proposition 5.1): a common core of width `m` and `s` free columns gives
  `Γ ≤ min(H, 1 + s)`.
* The two row facts of Proposition 2.4 are `rowI_eq`, `rowQ_involutive` and `payload_const`
  (in `ThreeCompilers.lean`).
-/

namespace GC.GridCompilers

/-! ### Lemma 3.1: finite portfolios -/

section Portfolio

variable {B N Y : Type*}

/-- A compiler for active blocks: on a block `b` it either fails (`none`) or passes and returns
the trace as a function of the north word. Its pass bit `(c b).isSome` depends only on `b`. -/
abbrev BlockCompiler (B N Y : Type*) := B → Option (N → Y)

/-- A compiler is sound for the semantics `truth` if every output it returns is the true trace. -/
def Sound (truth : B → N → Y) (c : BlockCompiler B N Y) : Prop :=
  ∀ b f, c b = some f → ∀ n, f n = truth b n

/-- The portfolio of a finite list of compilers: run all of them and keep the output of the first
passing one. -/
def portfolio : List (BlockCompiler B N Y) → BlockCompiler B N Y
  | [], _ => none
  | c :: cs, b => match c b with
    | some f => some f
    | none => portfolio cs b

/-- **Finite portfolios** (009c, Lemma 3.1), pass bit: the portfolio passes on a block iff some
compiler of the list passes on it. -/
theorem portfolio_isSome_iff (cs : List (BlockCompiler B N Y)) (b : B) :
    (portfolio cs b).isSome ↔ ∃ c ∈ cs, (c b).isSome := by
  induction cs with
  | nil => simp [portfolio]
  | cons c cs ih =>
    simp only [portfolio, List.mem_cons, exists_eq_or_imp]
    cases hc : c b with
    | some f => simp
    | none => simp [ih]

/-- **Finite portfolios** (009c, Lemma 3.1), soundness: if every compiler of the list is sound,
so is the portfolio. -/
theorem portfolio_sound (truth : B → N → Y) (cs : List (BlockCompiler B N Y))
    (hcs : ∀ c ∈ cs, Sound truth c) : Sound truth (portfolio cs) := by
  induction cs with
  | nil => intro b f h; simp [portfolio] at h
  | cons c cs ih =>
    intro b f h n
    simp only [portfolio] at h
    cases hc : c b with
    | some g =>
      rw [hc] at h
      cases h
      exact hcs c (by simp) b _ hc n
    | none =>
      rw [hc] at h
      exact ih (fun c' hc' => hcs c' (by simp [hc'])) b f h n

end Portfolio

/-! ### `Γ` facts used in Proposition 4.2 and Proposition 5.1 -/

theorem varCols_eq_empty_of_const {W : ℕ} {β : ℕ → ℕ → Bool} {a b : ℕ}
    (h : ∀ i, a < i → i < b → ∀ j, 1 ≤ j → j ≤ W → β i j = β a j) :
    varCols W β a b = ∅ := by
  ext j
  simp only [varCols, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioo, Finset.notMem_empty,
    iff_false, not_and, not_exists]
  intro hj i hi
  exact fun hne => hne (h i hi.1 hi.2 j hj.1 hj.2)

/-- **Second run of Proposition 4.2** (009c): if rows `1, …, L` carry one cell word and rows
`L + 1, …, L + L'` carry another (e.g. `L` rows `I` followed by `L'` rows `Q`), then `Γ ≤ 2`. -/
theorem gamma_two_bands (W L L' : ℕ) (hL : 1 ≤ L) (hL' : 1 ≤ L') (β : ℕ → ℕ → Bool)
    (h1 : ∀ i, 1 ≤ i → i ≤ L → ∀ j, 1 ≤ j → j ≤ W → β i j = β 1 j)
    (h2 : ∀ i, L + 1 ≤ i → i ≤ L + L' → ∀ j, 1 ≤ j → j ≤ W → β i j = β (L + 1) j) :
    Gamma W β (L + L') ≤ 2 := by
  have hpart : IsRowPartition (L + L') [L, L'] :=
    ⟨by simp; omega, by simp⟩
  refine (Gamma_le hpart).trans (le_of_eq ?_)
  simp only [partitionCost, blockWeight]
  rw [varCols_eq_empty_of_const (fun i hi1 hi2 j hj1 hj2 => h1 i (by omega) (by omega) j hj1 hj2),
    varCols_eq_empty_of_const (a := 1 + L) (b := 1 + L + L') (fun i hi1 hi2 j hj1 hj2 => by
      rw [show 1 + L = L + 1 by omega]; exact h2 i (by omega) (by omega) j hj1 hj2)]
  simp

/-- The cell words of the second run of Proposition 4.2: `L` rows `I = 0^W` followed by `L` rows
`Q = 0^{W-1} 1`. -/
def twoBandCells (W L : ℕ) : ℕ → ℕ → Bool := fun i j => decide (L < i ∧ j = W)

/-- **Proposition 4.2, second run** (009c): `L` rows `I` followed by `L` rows `Q` have `Γ ≤ 2`. -/
theorem gamma_twoBandCells (W L : ℕ) (hL : 1 ≤ L) : Gamma W (twoBandCells W L) (L + L) ≤ 2 := by
  apply gamma_two_bands W L L hL hL
  · intro i _ hi j _ _
    have h1 : ¬ L < i := by omega
    have h2 : ¬ L < 1 := by omega
    simp [twoBandCells, h1, h2]
  · intro i hi _ j _ _
    have h1 : L < i := by omega
    have h2 : L < L + 1 := by omega
    simp [twoBandCells, h1, h2]

/-- **Common cores** (009c, Proposition 5.1): if all rows `1, …, H` share their first `m` cells
and have `s` further cells (so `W = m + s`), then `Γ ≤ min(H, 1 + s)`. -/
theorem gamma_common_core (H m s : ℕ) (β : ℕ → ℕ → Bool)
    (hcore : ∀ i i', 1 ≤ i → i ≤ H → 1 ≤ i' → i' ≤ H → ∀ j, 1 ≤ j → j ≤ m → β i j = β i' j) :
    Gamma (m + s) β H ≤ min H (1 + s) := by
  rcases Nat.eq_zero_or_pos H with rfl | hH
  · have : Gamma (m + s) β 0 ≤ partitionCost (m + s) β 1 [] := Gamma_le ⟨by simp, by simp⟩
    simp [partitionCost] at this
    simp [this]
  refine le_min ((gamma_bounds H hH).2.trans (min_le_left _ _)) ?_
  calc Gamma (m + s) β H ≤ partitionCost (m + s) β 1 [H] :=
        Gamma_le ⟨fun h hh => by simp at hh; omega, by simp⟩
    _ ≤ 1 + s := by
        simp only [partitionCost, blockWeight, add_zero]
        have hsub : varCols (m + s) β 1 (1 + H) ⊆ Finset.Icc (m + 1) (m + s) := by
          intro j hj
          simp only [varCols, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioo] at hj
          obtain ⟨⟨hj1, hj2⟩, i, ⟨hi1, hi2⟩, hne⟩ := hj
          rw [Finset.mem_Icc]
          refine ⟨?_, hj2⟩
          by_contra hcon
          exact hne (hcore i 1 (by omega) (by omega) le_rfl hH j hj1 (by omega))
        have := Finset.card_le_card hsub
        simp at this
        omega

end GC.GridCompilers
