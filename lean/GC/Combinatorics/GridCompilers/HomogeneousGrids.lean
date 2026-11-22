import GC.Combinatorics.GridCompilers.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Option
import Mathlib.Order.Nat

/-!
# Homogeneous Sequential NOR grids (manuscript 009a): the per-template lemmas

The NC¹ compiler of 009a (Theorem 4.6) and its uniformity are *not* formalized. We formalize
the exact grid facts on which it rests, for the grid normal form `grid` of `Basic.lean`:

* `active_row_formula`, `active_row_noAdj` (Lemma 3.1): active rows output Fibonacci words.
* `reset_row_iff`, `reset_row_threshold` (Lemma 3.2): a reset row outputs a threshold word.
* `orientation_example` (Remark 3.3).
* For homogeneous templates (`α ≡ 1`, `β_{i,·} = b`):
  `zero_column_iff` (Lemma 4.1), `diagonal_collapse`, `diagonal_collapse_iterate`,
  `slab_cell_copy` (Lemma 4.2), `no_vertical_000` (Lemma 4.3), and the transfer-type closure
  `transferClass_comp`, `card_transferClass_le` (Lemma 4.5).
-/

namespace GC.GridCompilers

variable (T L α : ℕ → Bool) (β : ℕ → ℕ → Bool)

theorem grid_zero (j : ℕ) : grid T L α β 0 j = T j := rfl

theorem grid_succ_zero (i : ℕ) : grid T L α β (i + 1) 0 = L (i + 1) := rfl

theorem grid_succ_succ (i j : ℕ) :
    grid T L α β (i + 1) (j + 1) =
      (Bool.xor (grid T L α β (i + 1) j) (α (i + 1)) &&
        Bool.xor (grid T L α β i (j + 1)) (β (i + 1) (j + 1))) := rfl

/-! ### Rows of the grid -/

/-- **Active rows** (009a, Lemma 3.1, formula). -/
theorem active_row_formula {i : ℕ} (hα : α (i + 1) = true) (j : ℕ) :
    grid T L α β (i + 1) (j + 1) =
      (!grid T L α β (i + 1) j && Bool.xor (grid T L α β i (j + 1)) (β (i + 1) (j + 1))) := by
  rw [grid_succ_succ, hα, Bool.xor_true]

/-- **Active rows** (009a, Lemma 3.1): no two adjacent ones in an active row (this includes the
west bit `X_{i,0} = L_i`, so in particular the output lies in `𝓕_W` for every `W`). -/
theorem active_row_noAdj {i : ℕ} (hα : α (i + 1) = true) (j : ℕ) :
    ¬ (grid T L α β (i + 1) j = true ∧ grid T L α β (i + 1) (j + 1) = true) := by
  rintro ⟨h1, h2⟩
  rw [active_row_formula T L α β hα, h1] at h2
  simp at h2

theorem active_row_isFibOn {i : ℕ} (hα : α (i + 1) = true) (W : ℕ) :
    IsFibOn W (grid T L α β (i + 1)) :=
  fun j _ _ => active_row_noAdj T L α β hα j

/-- **Reset rows** (009a, Lemma 3.2, formula): on a reset row,
`X_{i,j} = L_i ∧ ⋀_{1 ≤ t ≤ j} (N_t ⊕ β_{i,t})`. -/
theorem reset_row_iff {i : ℕ} (hα : α (i + 1) = false) (j : ℕ) :
    grid T L α β (i + 1) j = true ↔
      L (i + 1) = true ∧ ∀ t, 1 ≤ t → t ≤ j → Bool.xor (grid T L α β i t) (β (i + 1) t) = true := by
  induction j with
  | zero =>
    rw [grid_succ_zero]
    exact ⟨fun h => ⟨h, fun t h1 h2 => absurd h2 (by omega)⟩, fun h => h.1⟩
  | succ j ih =>
    rw [grid_succ_succ, hα, Bool.xor_false, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨⟨hL, hall⟩, hj⟩
      refine ⟨hL, fun t h1 h2 => ?_⟩
      rcases Nat.lt_or_ge t (j + 1) with h | h
      · exact hall t h1 (by omega)
      · obtain rfl : t = j + 1 := by omega
        exact hj
    · rintro ⟨hL, hall⟩
      exact ⟨⟨hL, fun t h1 h2 => hall t h1 (by omega)⟩, hall (j + 1) (by omega) le_rfl⟩

/-- A Boolean word that is non-increasing on `[1, W]` is a threshold word `1^q 0^{W-q}`. -/
theorem exists_threshold (f : ℕ → Bool) (W : ℕ)
    (hmono : ∀ j, 1 ≤ j → f (j + 1) = true → f j = true) :
    ∃ q ≤ W, ∀ j, 1 ≤ j → j ≤ W → (f j = true ↔ j ≤ q) := by
  classical
  let P : ℕ → Prop := fun q => ∀ t, 1 ≤ t → t ≤ q → f t = true
  have hdown : ∀ j, 1 ≤ j → f j = true → P j := by
    intro j hj hf
    induction j with
    | zero => omega
    | succ j ih =>
      intro t h1 h2
      rcases Nat.lt_or_ge t (j + 1) with h | h
      · exact ih (by omega) (hmono j (by omega) hf) t h1 (by omega)
      · obtain rfl : t = j + 1 := by omega
        exact hf
  refine ⟨Nat.findGreatest P W, Nat.findGreatest_le W, fun j h1 h2 => ⟨fun hf => ?_, fun hq => ?_⟩⟩
  · exact Nat.le_findGreatest h2 (hdown j h1 hf)
  · have h0 : P 0 := fun t h1 h2 => absurd h2 (by omega)
    exact Nat.findGreatest_spec (P := P) (Nat.zero_le W) h0 j h1 hq

/-- **Reset rows** (009a, Lemma 3.2, threshold form): the output of a reset row on columns
`1, …, W` is a threshold word `1^q 0^{W-q}`. -/
theorem reset_row_threshold {i : ℕ} (hα : α (i + 1) = false) (W : ℕ) :
    ∃ q ≤ W, ∀ j, 1 ≤ j → j ≤ W → (grid T L α β (i + 1) j = true ↔ j ≤ q) := by
  apply exists_threshold
  intro j _ h
  rw [grid_succ_succ, hα, Bool.xor_false, Bool.and_eq_true] at h
  exact h.1

/-- **Remark 3.3** (orientation). With `W = 2`, `T = 00`, `L = (0,0)`, `α = (0,1)`,
`β = (00, 01)`, the reset row is `00` and the following active row is `01`. -/
theorem orientation_example :
    let T : ℕ → Bool := fun _ => false
    let L : ℕ → Bool := fun _ => false
    let α : ℕ → Bool := fun i => decide (i = 2)
    let β : ℕ → ℕ → Bool := fun i j => decide (i = 2 ∧ j = 2)
    (grid T L α β 1 1, grid T L α β 1 2) = (false, false) ∧
      (grid T L α β 2 1, grid T L α β 2 2) = (false, true) := by
  decide

/-! ### Homogeneous templates -/

section Homogeneous

variable (b : ℕ → Bool)

/-- The homogeneous grid: every row active, every row carrying the cell word `b`. -/
abbrev homGrid : ℕ → ℕ → Bool := grid T L (fun _ => true) (fun _ => b)

theorem homGrid_succ_succ (i j : ℕ) :
    homGrid T L b (i + 1) (j + 1) =
      (!homGrid T L b (i + 1) j && Bool.xor (homGrid T L b i (j + 1)) (b (j + 1))) := by
  show (Bool.xor (homGrid T L b (i + 1) j) true &&
    Bool.xor (homGrid T L b i (j + 1)) (b (j + 1))) = _
  rw [Bool.xor_true]

theorem homGrid_dense {j : ℕ} (hb : b (j + 1) = true) (i : ℕ) :
    homGrid T L b (i + 1) (j + 1) = nor (homGrid T L b (i + 1) j) (homGrid T L b i (j + 1)) := by
  rw [homGrid_succ_succ, hb, Bool.xor_true]
  simp [nor]

/-- **Zero columns reset** (009a, Lemma 4.1): if `b_j = 0` then
`X_{i,j} = T_j ∧ ⋀_{r=1}^{i} ¬X_{r,j-1}`. -/
theorem zero_column_iff {j : ℕ} (hb : b (j + 1) = false) (i : ℕ) :
    homGrid T L b i (j + 1) = true ↔
      T (j + 1) = true ∧ ∀ r, 1 ≤ r → r ≤ i → homGrid T L b r j = false := by
  induction i with
  | zero => exact ⟨fun h => ⟨h, fun r h1 h2 => absurd h2 (by omega)⟩, fun h => h.1⟩
  | succ i ih =>
    rw [homGrid_succ_succ, hb, Bool.xor_false, Bool.and_eq_true, ih, Bool.not_eq_true']
    constructor
    · rintro ⟨hr, hT, hall⟩
      refine ⟨hT, fun r h1 h2 => ?_⟩
      rcases Nat.lt_or_ge r (i + 1) with h | h
      · exact hall r h1 (by omega)
      · obtain rfl : r = i + 1 := by omega
        exact hr
    · rintro ⟨hT, hall⟩
      exact ⟨hall (i + 1) (by omega) le_rfl, hT, fun r h1 h2 => hall r h1 (by omega)⟩

/-- A zero column is a vertical threshold word `1^s 0^{H-s}`. -/
theorem zero_column_threshold {j : ℕ} (hb : b (j + 1) = false) (H : ℕ) :
    ∃ s ≤ H, ∀ i, 1 ≤ i → i ≤ H → (homGrid T L b i (j + 1) = true ↔ i ≤ s) := by
  apply exists_threshold
  intro i hi h
  rw [zero_column_iff T L b hb] at h ⊢
  exact ⟨h.1, fun r h1 h2 => h.2 r h1 (by omega)⟩

private theorem diag_aux (p u v w : Bool) :
    nor (nor (nor p u) (nor u v)) (nor (nor u v) (nor v w)) = nor u v := by
  cases p <;> cases u <;> cases v <;> cases w <;> rfl

/-- **Diagonal collapse** (009a, Lemma 4.2). Let `c ≤ d` be a dense slab (`b_t = 1` for
`c ≤ t ≤ d`, with `c ≥ 1`). For `i ≥ 3` and `c + 2 ≤ j ≤ d`, `X_{i,j} = X_{i-1,j-1}`. -/
theorem diagonal_collapse {c d : ℕ} (hc : 1 ≤ c) (hslab : ∀ t, c ≤ t → t ≤ d → b t = true)
    {i j : ℕ} (hi : 3 ≤ i) (hj : c + 2 ≤ j) (hjd : j ≤ d) :
    homGrid T L b i j = homGrid T L b (i - 1) (j - 1) := by
  obtain ⟨i, rfl⟩ : ∃ i', i = i' + 3 := ⟨i - 3, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 3 := ⟨j - 3, by omega⟩
  have e1 := homGrid_dense T L b (j := j + 2) (hslab _ (by omega) hjd) (i + 2)
  have e2 := homGrid_dense T L b (j := j + 1) (hslab _ (by omega) (by omega)) (i + 2)
  have e3 := homGrid_dense T L b (j := j) (hslab _ (by omega) (by omega)) (i + 2)
  have e4 := homGrid_dense T L b (j := j + 1) (hslab _ (by omega) (by omega)) (i + 1)
  have e5 := homGrid_dense T L b (j := j + 2) (hslab _ (by omega) hjd) (i + 1)
  have e6 := homGrid_dense T L b (j := j + 2) (hslab _ (by omega) hjd) i
  simp only [show i + 3 - 1 = i + 2 by omega, show j + 3 - 1 = j + 2 by omega]
  rw [e1, e2, e5, e6, e3, e4]
  exact diag_aux _ _ _ _

/-- Iterated diagonal collapse: `X_{i,j} = X_{i-t,j-t}` for `t ≤ min(i-2, j-c-1)`. -/
theorem diagonal_collapse_iterate {c d : ℕ} (hc : 1 ≤ c)
    (hslab : ∀ t, c ≤ t → t ≤ d → b t = true) {i j : ℕ} (hjd : j ≤ d) :
    ∀ t, t + 2 ≤ i → t + c + 1 ≤ j → homGrid T L b i j = homGrid T L b (i - t) (j - t) := by
  intro t
  induction t with
  | zero => intro _ _; rfl
  | succ t ih =>
    intro h1 h2
    rw [ih (by omega) (by omega), diagonal_collapse T L b hc hslab (by omega) (by omega)
      (by omega)]
    congr 1

/-- **Diagonal collapse, consequence** (009a, Lemma 4.2): every cell of a dense slab (rows
`≥ 1`, columns `c ≤ j ≤ d`) is a copy of a slab cell in rows `1, 2` or columns `c, c + 1`. -/
theorem slab_cell_copy {c d : ℕ} (hc : 1 ≤ c) (hslab : ∀ t, c ≤ t → t ≤ d → b t = true)
    {i j : ℕ} (hi : 1 ≤ i) (hcj : c ≤ j) (hjd : j ≤ d) :
    ∃ i' j', 1 ≤ i' ∧ c ≤ j' ∧ (i' ≤ 2 ∨ j' ≤ c + 1) ∧
      homGrid T L b i j = homGrid T L b i' j' := by
  by_cases h : i ≤ 2 ∨ j ≤ c + 1
  · exact ⟨i, j, hi, hcj, h, rfl⟩
  · push Not at h
    let t := min (i - 2) (j - c - 1)
    refine ⟨i - t, j - t, by omega, by omega, by omega, ?_⟩
    exact diagonal_collapse_iterate T L b hc hslab hjd t (by omega) (by omega)

private theorem no000_aux (s a p : Bool) :
    ¬ (s = false ∧ nor a s = false ∧ nor (nor p a) (nor a s) = false) := by
  cases s <;> cases a <;> cases p <;> decide

/-- **No vertical 000** (009a, Lemma 4.3). In a dense slab `c ≤ d` (`c ≥ 1`), for
`c + 1 ≤ j ≤ d` there is no `i` with `X_{i-2,j} = X_{i-1,j} = X_{i,j} = 0`. The paper states
this for `3 ≤ i ≤ H`; it also holds for `i = 2`. -/
theorem no_vertical_000 {c d : ℕ} (hc : 1 ≤ c) (hslab : ∀ t, c ≤ t → t ≤ d → b t = true)
    {i j : ℕ} (hi : 2 ≤ i) (hj : c + 1 ≤ j) (hjd : j ≤ d) :
    ¬ (homGrid T L b (i - 2) j = false ∧ homGrid T L b (i - 1) j = false ∧
      homGrid T L b i j = false) := by
  obtain ⟨i, rfl⟩ : ∃ i', i = i' + 2 := ⟨i - 2, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 2 := ⟨j - 2, by omega⟩
  have e1 := homGrid_dense T L b (j := j + 1) (hslab _ (by omega) hjd) i
  have e2 := homGrid_dense T L b (j := j) (hslab _ (by omega) (by omega)) (i + 1)
  have e3 := homGrid_dense T L b (j := j + 1) (hslab _ (by omega) hjd) (i + 1)
  simp only [show i + 2 - 2 = i by omega, show i + 2 - 1 = i + 1 by omega]
  rw [e3, e2, e1]
  exact no000_aux _ _ _

end Homogeneous

/-! ### The transfer class `𝒢_H` and its closure (Lemma 4.5) -/

/-- `A_H = {0, 1, 2, H}` as a subset of `{0, …, H}`. -/
def rankSet (H : ℕ) : Finset (Fin (H + 1)) := {0, 1, 2, Fin.last H}

/-- `f ∈ 𝒢_H`: `f(0), f(1) ∈ A_H`, and on `{2, …, H}` the map is the identity or a constant in
`A_H`. -/
def InTransferClass (H : ℕ) (f : Fin (H + 1) → Fin (H + 1)) : Prop :=
  f 0 ∈ rankSet H ∧ f 1 ∈ rankSet H ∧
    ((∀ s : Fin (H + 1), 2 ≤ s.val → f s = s) ∨
      ∃ c ∈ rankSet H, ∀ s : Fin (H + 1), 2 ≤ s.val → f s = c)

instance (H : ℕ) : DecidablePred (InTransferClass H) := by
  intro f; unfold InTransferClass; infer_instance

/-- The finite set `𝒢_H`. -/
def transferClass (H : ℕ) : Finset (Fin (H + 1) → Fin (H + 1)) :=
  Finset.univ.filter (InTransferClass H)

theorem two_val {H : ℕ} (hH : 3 ≤ H) : (2 : Fin (H + 1)).val = 2 := by
  show 2 % (H + 1) = 2
  exact Nat.mod_eq_of_lt (by omega)

theorem mapsTo_rankSet {H : ℕ} (hH : 3 ≤ H) {f : Fin (H + 1) → Fin (H + 1)}
    (hf : InTransferClass H f) {a : Fin (H + 1)} (ha : a ∈ rankSet H) : f a ∈ rankSet H := by
  obtain ⟨h0, h1, htail⟩ := hf
  have hcases : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = Fin.last H := by
    simpa [rankSet] using ha
  have h2 : 2 ≤ (2 : Fin (H + 1)).val := by rw [two_val hH]
  have hl : 2 ≤ (Fin.last H).val := by simp; omega
  rcases hcases with rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · rcases htail with ht | ⟨c, hc, ht⟩
    · rw [ht _ h2]; simp [rankSet]
    · rw [ht _ h2]; exact hc
  · rcases htail with ht | ⟨c, hc, ht⟩
    · rw [ht _ hl]; simp [rankSet]
    · rw [ht _ hl]; exact hc

/-- **Closure** (009a, Lemma 4.5): for `H ≥ 3`, `𝒢_H` is closed under composition. -/
theorem transferClass_comp {H : ℕ} (hH : 3 ≤ H) {f g : Fin (H + 1) → Fin (H + 1)}
    (hf : InTransferClass H f) (hg : InTransferClass H g) : InTransferClass H (f ∘ g) := by
  obtain ⟨g0, g1, gtail⟩ := hg
  refine ⟨mapsTo_rankSet hH hf g0, mapsTo_rankSet hH hf g1, ?_⟩
  rcases gtail with ht | ⟨c, hc, ht⟩
  · rcases hf.2.2 with ft | ⟨c, hc, ft⟩
    · left; intro s hs; simp [ht s hs, ft s hs]
    · right; exact ⟨c, hc, fun s hs => by simp [ht s hs, ft s hs]⟩
  · right
    exact ⟨f c, mapsTo_rankSet hH hf hc, fun s hs => by simp [ht s hs]⟩

/-- **Lemma 4.4/4.5, count**: for `H ≥ 3`, `|𝒢_H| ≤ 80`. -/
theorem card_transferClass_le {H : ℕ} (hH : 3 ≤ H) : (transferClass H).card ≤ 80 := by
  classical
  let A := rankSet H
  let code : (Fin (H + 1) → Fin (H + 1)) → Fin (H + 1) × Fin (H + 1) × Option (Fin (H + 1)) :=
    fun f => (f 0, f 1, if ∀ s : Fin (H + 1), 2 ≤ s.val → f s = s then none else some (f 2))
  have h2 : 2 ≤ (2 : Fin (H + 1)).val := by rw [two_val hH]
  have hmaps : ∀ f ∈ transferClass H, code f ∈ A ×ˢ A ×ˢ A.insertNone := by
    intro f hf
    simp only [transferClass, Finset.mem_filter, Finset.mem_univ, true_and] at hf
    obtain ⟨h0, h1, htail⟩ := hf
    simp only [code, Finset.mem_product]
    refine ⟨h0, h1, ?_⟩
    split_ifs with hid
    · exact Finset.mem_insertNone.2 (by simp)
    · rcases htail with ht | ⟨c, hc, ht⟩
      · exact absurd ht hid
      · rw [Finset.mem_insertNone]
        intro a ha
        simp only [Option.mem_def, Option.some.injEq] at ha
        rw [← ha, ht _ h2]; exact hc
  have hinj : Set.InjOn code (transferClass H) := by
    intro f hf g hg hfg
    simp only [Finset.coe_filter, transferClass, Finset.mem_univ, true_and,
      Set.mem_ofPred_eq] at hf hg
    simp only [code, Prod.mk.injEq] at hfg
    obtain ⟨e0, e1, e2⟩ := hfg
    funext s
    by_cases hs0 : s.val = 0
    · rw [show s = 0 from Fin.ext (by simp [hs0])]; exact e0
    by_cases hs1 : s.val = 1
    · have h1v : (1 : Fin (H + 1)).val = 1 := by
        show 1 % (H + 1) = 1
        exact Nat.mod_eq_of_lt (by omega)
      rw [show s = 1 from Fin.ext (by rw [hs1, h1v])]; exact e1
    have hs : 2 ≤ s.val := by omega
    by_cases hfid : ∀ t : Fin (H + 1), 2 ≤ t.val → f t = t
    · by_cases hgid : ∀ t : Fin (H + 1), 2 ≤ t.val → g t = t
      · rw [hfid s hs, hgid s hs]
      · rw [if_pos hfid, if_neg hgid] at e2; exact absurd e2 (by simp)
    · by_cases hgid : ∀ t : Fin (H + 1), 2 ≤ t.val → g t = t
      · rw [if_neg hfid, if_pos hgid] at e2; exact absurd e2 (by simp)
      · rw [if_neg hfid, if_neg hgid, Option.some.injEq] at e2
        obtain ⟨cf, -, hcf⟩ := hf.2.2.resolve_left hfid
        obtain ⟨cg, -, hcg⟩ := hg.2.2.resolve_left hgid
        rw [hcf s hs, hcg s hs, ← hcf 2 h2, ← hcg 2 h2, e2]
  have hcard := Finset.card_le_card_of_injOn code hmaps hinj
  have hA : A.card ≤ 4 := Finset.card_le_four
  rw [Finset.card_product, Finset.card_product, Finset.card_insertNone] at hcard
  calc (transferClass H).card ≤ A.card * (A.card * (A.card + 1)) := hcard
    _ ≤ 4 * (4 * (4 + 1)) := by gcongr
    _ = 80 := by norm_num

end GC.GridCompilers
