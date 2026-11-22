import GC.Computability.Tabulation.Basic
import GC.Computability.Tabulation.TilingRotation

/-!
# Homogeneous rules and polarity gauges (manuscript 010b, Sections 4–5: sixteen rules, polarity gauges)
-/

namespace GC.Tabulation

/-- The complement conjugate `Ḡ(u, v) = ¬G(¬u, ¬v)`. -/
def conjGate (G : Bool → Bool → Bool) : Bool → Bool → Bool := fun u v => !(G (!u) (!v))

/-- `𝖢_D`: complement all bits of a row. -/
def cmpRow {D : ℕ} (x : Fin D → Bool) : Fin D → Bool := fun s => !(x s)

/-- **Lemma 4.1 (complement conjugation).** `F_{Ḡ,D} = 𝖢_D ∘ F_{G,D} ∘ 𝖢_D`. -/
theorem sweep_conjGate (G : Bool → Bool → Bool) {D : ℕ} (x : Fin D → Bool) :
    sweep (conjGate G) x = cmpRow (sweep G (cmpRow x)) := by
  rcases Nat.eq_zero_or_pos D with hD | hD
  · subst hD; funext s; exact s.elim0
  have key : ∀ s, s ≤ D → sweepVal (conjGate G) x s = !(sweepVal G (cmpRow x) s) := by
    intro s
    induction s with
    | zero =>
      intro _
      simp only [sweepVal, rowGet, cmpRow]
      rw [dif_pos (by omega), dif_pos (by omega), Bool.not_not]
    | succ s ih =>
      intro hs
      simp only [sweepVal, conjGate]
      rw [ih (by omega), Bool.not_not]
      simp only [rowGet, cmpRow]
      rw [dif_pos (by omega), dif_pos (by omega)]
  funext s
  simp only [sweep, cmpRow]
  rw [key _ (by omega)]

lemma sweep_conjGate_iterate (G : Bool → Bool → Bool) {D : ℕ} (k : ℕ) (x : Fin D → Bool) :
    (sweep (conjGate G))^[k] x = cmpRow ((sweep G)^[k] (cmpRow x)) := by
  induction k generalizing x with
  | zero => funext s; simp [cmpRow]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, sweep_conjGate, Function.iterate_succ_apply']
    congr 2
    funext s; simp [cmpRow]

/-- `P(u, v) = v ∧ ¬u`. -/
def gateP (u v : Bool) : Bool := v && !u
/-- `Q(u, v) = u ∧ ¬v`. -/
def gateQ (u v : Bool) : Bool := u && !v
/-- `A(u, v) = u ∧ v`. -/
def gateA (u v : Bool) : Bool := u && v

section Collapse

variable {D : ℕ}

lemma rowGet_sweep (G : Bool → Bool → Bool) (x : Fin D → Bool) (s : ℕ) (hs : s < D) :
    rowGet (sweep G x) s = sweepVal G x (s + 1) := by
  simp [rowGet, sweep, hs]

/-- **Lemma 4.2, rule `P`.** `F_P² = F_P`. -/
theorem sweep_P_idem (x : Fin D → Bool) : sweep gateP (sweep gateP x) = sweep gateP x := by
  rcases Nat.eq_zero_or_pos D with hD | hD
  · subst hD; funext s; exact s.elim0
  obtain ⟨n, rfl⟩ : ∃ n, D = n + 1 := ⟨D - 1, by omega⟩
  have hvs : ∀ s, sweepVal gateP x (s + 1) = (rowGet x s && !sweepVal gateP x s) :=
    fun s => rfl
  have hv0 : sweepVal gateP x 0 = rowGet x n := rfl
  have key : ∀ s, s ≤ n + 1 → sweepVal gateP (sweep gateP x) s =
      if s = 0 then sweepVal gateP x (n + 1) else sweepVal gateP x s := by
    intro s
    induction s with
    | zero =>
      intro _
      simp only [sweepVal, if_true]
      rw [rowGet_sweep _ _ _ (by omega), show n + 1 - 1 + 1 = n + 1 by omega]
      rfl
    | succ s ih =>
      intro hs
      simp only [sweepVal]
      rw [ih (by omega), rowGet_sweep _ _ _ (by omega)]
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, gateP]
      rcases s with _ | s
      · simp only [if_true]
        rw [hvs n, hvs 0, hv0]
        cases rowGet x n <;> cases rowGet x 0 <;> cases sweepVal gateP x n <;> simp
      · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false]
        rw [hvs (s + 1)]
        cases rowGet x (s + 1) <;> cases sweepVal gateP x (s + 1) <;> simp
  funext s
  simp only [sweep]
  rw [key _ (by omega)]
  simp

/-- **Lemma 4.2, rule `Q`.** `F_Q²(x) = 0^D`. -/
theorem sweep_Q_two (x : Fin D → Bool) :
    sweep gateQ (sweep gateQ x) = fun _ => false := by
  rcases Nat.eq_zero_or_pos D with hD | hD
  · subst hD; funext s; exact s.elim0
  obtain ⟨n, rfl⟩ : ∃ n, D = n + 1 := ⟨D - 1, by omega⟩
  set v := sweepVal gateQ x with hv
  have hdec : ∀ s, v s = true → v 0 = true := by
    intro s
    induction s with
    | zero => exact id
    | succ s ih =>
      intro h
      simp only [hv, sweepVal, gateQ, Bool.and_eq_true] at h
      exact ih h.1
  have hvD : v (n + 1) = false := by
    have e : v (n + 1) = (v n && !rowGet x n) := by simp [hv, sweepVal, gateQ]
    have h0 : v 0 = rowGet x n := by simp [hv, sweepVal]
    cases hvn : v n
    · simp [e, hvn]
    · have := hdec n hvn
      rw [h0] at this
      simp [e, hvn, this]
  have key : ∀ s, sweepVal gateQ (sweep gateQ x) s = false := by
    intro s
    induction s with
    | zero =>
      simp only [sweepVal]
      rw [rowGet_sweep _ _ _ (by omega)]
      exact hvD
    | succ s ih => simp [sweepVal, ih, gateQ]
  funext s
  exact key _

lemma sweepVal_A_ones (hD : 1 ≤ D) : ∀ s, s ≤ D → sweepVal gateA (fun _ : Fin D => true) s = true := by
  intro s
  induction s with
  | zero => intro _; simp [sweepVal, rowGet, show D - 1 < D by omega]
  | succ s ih =>
    intro hs
    simp only [sweepVal, gateA, ih (by omega), Bool.true_and, rowGet, dif_pos (show s < D by omega)]

lemma sweep_A_ones : sweep gateA (fun _ : Fin D => true) = fun _ => true := by
  funext s
  exact sweepVal_A_ones (by have := s.isLt; omega) _ (by have := s.isLt; omega)

lemma sweep_zero_start (G : Bool → Bool → Bool) (hG : ∀ v, G false v = false) (y : Fin D → Bool)
    (h0 : sweepVal G y 0 = false) : sweep G y = fun _ => false := by
  have : ∀ s, sweepVal G y s = false := by
    intro s
    induction s with
    | zero => exact h0
    | succ s ih => simp [sweepVal, ih, hG]
  funext s; exact this _

lemma sweep_A_zero : sweep gateA (fun _ : Fin D => false) = fun _ => false := by
  rcases Nat.eq_zero_or_pos D with hD | hD
  · subst hD; funext s; exact s.elim0
  exact sweep_zero_start gateA (fun v => by simp [gateA]) _ (by simp [sweepVal, rowGet])

/-- **Lemma 4.2, rule `A`.** `F_A²(x) = 1^D` if `x = 1^D` and `0^D` otherwise. -/
theorem sweep_A_two (x : Fin D → Bool) :
    sweep gateA (sweep gateA x) =
      if x = (fun _ => true) then (fun _ => true) else (fun _ => false) := by
  rcases Nat.eq_zero_or_pos D with hD | hD
  · subst hD; funext s; exact s.elim0
  split_ifs with hx
  · subst hx; rw [sweep_A_ones, sweep_A_ones]
  · obtain ⟨j, hj⟩ : ∃ j : Fin D, x j = false := by
      by_contra h
      push_neg at h
      exact hx (funext fun s => by simpa using h s)
    have hv : ∀ s, j.val < s → sweepVal gateA x s = false := by
      intro s hs
      induction s with
      | zero => omega
      | succ s ih =>
        rcases Nat.lt_succ_iff_lt_or_eq.mp hs with h | h
        · simp [sweepVal, gateA, ih h]
        · subst h
          simp [sweepVal, gateA, rowGet, hj]
    apply sweep_zero_start gateA (fun v => by simp [gateA])
    simp only [sweepVal]
    rw [rowGet_sweep _ _ _ (by omega), show D - 1 + 1 = D by omega]
    exact hv D j.isLt

lemma sweep_Q_zero : sweep gateQ (fun _ : Fin D => false) = fun _ => false := by
  rcases Nat.eq_zero_or_pos D with hD | hD
  · subst hD; funext s; exact s.elim0
  exact sweep_zero_start gateQ (fun v => by simp [gateQ]) _ (by simp [sweepVal, rowGet])

/-- **Lemma 4.2, last claim.** For the six collapsing non-affine rules `P, Q, A` and their
complement conjugates, `F³ = F²`: every row from the second one on equals the second row. -/
theorem collapse_six (G : Bool → Bool → Bool)
    (hG : G = gateP ∨ G = gateQ ∨ G = gateA ∨
      G = conjGate gateP ∨ G = conjGate gateQ ∨ G = conjGate gateA) (x : Fin D → Bool) :
    (sweep G)^[3] x = (sweep G)^[2] x := by
  have base : ∀ G', (G' = gateP ∨ G' = gateQ ∨ G' = gateA) →
      ∀ y : Fin D → Bool, (sweep G')^[3] y = (sweep G')^[2] y := by
    rintro G' (rfl | rfl | rfl) y
    · show sweep gateP (sweep gateP (sweep gateP y)) = sweep gateP (sweep gateP y)
      rw [sweep_P_idem (sweep gateP y)]
    · show sweep gateQ (sweep gateQ (sweep gateQ y)) = sweep gateQ (sweep gateQ y)
      rw [sweep_Q_two y, sweep_Q_zero]
    · show sweep gateA (sweep gateA (sweep gateA y)) = sweep gateA (sweep gateA y)
      rw [sweep_A_two y]
      split_ifs
      · exact sweep_A_ones
      · exact sweep_A_zero
  rcases hG with h | h | h | h | h | h
  · exact base G (Or.inl h) x
  · exact base G (Or.inr (Or.inl h)) x
  · exact base G (Or.inr (Or.inr h)) x
  · subst h; rw [sweep_conjGate_iterate, sweep_conjGate_iterate, base gateP (Or.inl rfl)]
  · subst h
    rw [sweep_conjGate_iterate, sweep_conjGate_iterate, base gateQ (Or.inr (Or.inl rfl))]
  · subst h
    rw [sweep_conjGate_iterate, sweep_conjGate_iterate, base gateA (Or.inr (Or.inr rfl))]

end Collapse

/-! ### Section 5: polarity gauges -/

/-- Affine binary gates `αu ⊕ βv ⊕ γ`. -/
def IsAffineGate (G : Bool → Bool → Bool) : Prop :=
  ∃ α β γ : Bool, ∀ u v : Bool, G u v = xor (xor (α && u) (β && v)) γ

/-- The gate `NOR(u ⊕ a, v ⊕ b) ⊕ c` with polarity triple `(a, b, c)`. -/
def norPol (a b c : Bool) : Bool → Bool → Bool := fun u v => xor (nor (xor u a) (xor v b)) c

/-- **Lemma 5.1 (unique NOR polarity), existence part.** A binary gate is non-affine iff it is
`NOR(u ⊕ a, v ⊕ b) ⊕ c` for some triple `(a, b, c)`. -/
theorem nonaffine_iff_norPol (G : Bool → Bool → Bool) :
    ¬ IsAffineGate G ↔ ∃ a b c : Bool, G = norPol a b c := by
  have key : ∀ g00 g01 g10 g11 : Bool,
      (¬ ∃ α β γ : Bool, ∀ u v : Bool,
        cond u (cond v g11 g10) (cond v g01 g00) = xor (xor (α && u) (β && v)) γ) ↔
      ∃ a b c : Bool, ∀ u v : Bool, cond u (cond v g11 g10) (cond v g01 g00) = norPol a b c u v := by
    unfold norPol nor; decide
  have hG : G = fun u v => cond u (cond v (G true true) (G true false))
      (cond v (G false true) (G false false)) := by
    funext u v; cases u <;> cases v <;> rfl
  rw [hG]
  simp only [IsAffineGate, funext_iff]
  exact key _ _ _ _

/-- **Lemma 5.1, uniqueness part.** The polarity triple is unique. -/
theorem norPol_injective {a b c a' b' c' : Bool} (h : norPol a b c = norPol a' b' c') :
    a = a' ∧ b = b' ∧ c = c' := by
  have h1 := congrFun (congrFun h true) true
  have h2 := congrFun (congrFun h true) false
  have h3 := congrFun (congrFun h false) true
  have h4 := congrFun (congrFun h false) false
  revert h1 h2 h3 h4
  unfold norPol nor
  revert a b c a' b' c'; decide

/-- **Theorem 5.3 (polarity-gauge conjugacy), one cell.** If `G = NOR(u ⊕ a, v ⊕ b) ⊕ c` with
`a = η_W ⊕ A`, `b = η_N ⊕ B`, `c = η ⊕ C`, then the gauged values `z = x ⊕ η` satisfy
`z = H(z_W, z_N)` for `H = NOR(u ⊕ A, v ⊕ B) ⊕ C`. -/
theorem gauge_cell (A B C ηW ηN η xW xN : Bool) :
    xor (norPol (xor ηW A) (xor ηN B) (xor η C) xW xN) η =
      norPol A B C (xor xW ηW) (xor xN ηN) := by
  unfold norPol nor
  revert A B C ηW ηN η xW xN; decide

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
  intro q haq hqb
  apply rowOf_succ_eq_sweep _ hD
  intro i hi1 hi2
  have h1 : (a + 1) * D ≤ i := le_trans (Nat.mul_le_mul_right _ (by omega)) hi1
  have h2 : i < (b + 1) * D := lt_of_lt_of_le hi2 (Nat.mul_le_mul_right _ (by omega))
  show xor (x i) (η i) = norPol A B C (xor (x (i - 1)) (η (i - 1))) (xor (x (i - D)) (η (i - D)))
  rw [hx i h1 h2, hcons i h1 h2, gauge_cell]

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
  apply greedy_optimal _ R _ (fun a => Or.inl rfl) c k hc0 hck hc
  rintro a a' b (h | ⟨A, B, C, η, h⟩) haa' hab
  · left; omega
  · right
    refine ⟨A, B, C, η, fun i hi1 hi2 => h i (le_trans (Nat.mul_le_mul_right _ (by omega)) hi1) hi2⟩

end GC.Tabulation
