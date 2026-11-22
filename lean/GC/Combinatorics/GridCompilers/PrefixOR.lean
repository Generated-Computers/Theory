import GC.Combinatorics.GridCompilers.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.DeriveFintype
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Prefix OR defeats treewidth and curvature measures (manuscript 009e)

* Masking (Lemma 6.1): `unmask_maskedY`, `maskedY_unmask`, `maskedY_bijective`,
  `mixedDeriv_xor_const`.
* Masked prefix OR (Theorem 6.2): `maskedPrefixOr_prefix`, `maskedPrefixOr_formula`,
  `maskedPrefixOr_curvature_complete`.
* The reduction behind Theorem 6.3: `maskedY_zero_mask`.
* The reverse-prefix family (Theorem 4.1): `revPrefix_value` (`z_r = z_1 ∨ z_2` for `r ≥ 3`)
  and `revPrefix_minor_model` (an explicit `K_{k,k}` minor model in the moral graph).
* The grid of disjoint moral triangles (Theorem 4.2): `triGrid_vertexCover_card`,
  `triGrid_Krr`.

Treewidth is not available in Mathlib: for Theorem 4.1 we formalize the branch sets of the
`K_{k,k}` minor (disjoint, each connected by a path of moral edges, pairwise adjacent); the facts
`tw(K_{k,k}) = k` and minor-monotonicity of treewidth are not formalized. No NC upper bound and no
P-completeness is formalized.
-/

namespace GC.GridCompilers

/-! ### Masking -/

/-- `restrictLT y e` keeps the coordinates `i < e` of `y` and zeroes the others. -/
def restrictLT (y : ℕ → Bool) (e : ℕ) : ℕ → Bool := fun i => if i < e then y i else false

/-- The masked recurrence `y_e = x_e ⊕ g_e(y_{<e})`. -/
def maskedY (g : ℕ → (ℕ → Bool) → Bool) (x : ℕ → Bool) : ℕ → Bool
  | e => Bool.xor (x e) (g e (fun i => if _h : i < e then maskedY g x i else false))
termination_by e => e

theorem maskedY_eq (g : ℕ → (ℕ → Bool) → Bool) (x : ℕ → Bool) (e : ℕ) :
    maskedY g x e = Bool.xor (x e) (g e (restrictLT (maskedY g x) e)) := by
  rw [maskedY]; rfl

/-- The inverse map `x_e = y_e ⊕ g_e(y_{<e})`. -/
def unmask (g : ℕ → (ℕ → Bool) → Bool) (y : ℕ → Bool) : ℕ → Bool :=
  fun e => Bool.xor (y e) (g e (restrictLT y e))

/-- **Masking** (009e, Lemma 6.1), left inverse. -/
theorem unmask_maskedY (g : ℕ → (ℕ → Bool) → Bool) (x : ℕ → Bool) :
    unmask g (maskedY g x) = x := by
  funext e
  rw [unmask, maskedY_eq]
  cases x e <;> cases g e (restrictLT (maskedY g x) e) <;> rfl

/-- **Masking** (009e, Lemma 6.1), right inverse. -/
theorem maskedY_unmask (g : ℕ → (ℕ → Bool) → Bool) (y : ℕ → Bool) :
    maskedY g (unmask g y) = y := by
  have key : ∀ e, ∀ i < e, maskedY g (unmask g y) i = y i := by
    intro e
    induction e with
    | zero => intro i hi; omega
    | succ e ih =>
      intro i hi
      rcases Nat.lt_or_ge i e with h | h
      · exact ih i h
      · obtain rfl : i = e := by omega
        have hr : restrictLT (maskedY g (unmask g y)) i = restrictLT y i := by
          funext k; simp only [restrictLT]; split_ifs with hk
          · exact ih k hk
          · rfl
        rw [maskedY_eq, hr, unmask]
        cases y i <;> cases g i (restrictLT y i) <;> rfl
  funext e
  exact key (e + 1) e (by omega)

/-- **Masking** (009e, Lemma 6.1): for fixed `g`, `x ↦ y` is a bijection. -/
theorem maskedY_bijective (g : ℕ → (ℕ → Bool) → Bool) : Function.Bijective (maskedY g) :=
  ⟨Function.LeftInverse.injective (g := unmask g) (unmask_maskedY g),
    Function.RightInverse.surjective (g := unmask g) (maskedY_unmask g)⟩

/-- Toggle coordinate `u`. -/
def flipAt (u : ℕ) (y : ℕ → Bool) : ℕ → Bool := Function.update y u (!y u)

/-- The mixed derivative `Δ_{uv} g(y) = g(y) ⊕ g(y ⊕ e_u) ⊕ g(y ⊕ e_v) ⊕ g(y ⊕ e_u ⊕ e_v)`. -/
def mixedDeriv (u v : ℕ) (g : (ℕ → Bool) → Bool) (y : ℕ → Bool) : Bool :=
  Bool.xor (Bool.xor (Bool.xor (g y) (g (flipAt u y))) (g (flipAt v y)))
    (g (flipAt u (flipAt v y)))

/-- **Masking** (009e, Lemma 6.1): `Δ_{uv}(x_e ⊕ g_e) = Δ_{uv} g_e`, since `x_e` does not depend
on the earlier coordinates. -/
theorem mixedDeriv_xor_const (u v : ℕ) (c : Bool) (g : (ℕ → Bool) → Bool) :
    mixedDeriv u v (fun y => Bool.xor c (g y)) = mixedDeriv u v g := by
  funext y
  simp only [mixedDeriv]
  cases c <;> cases g y <;> cases g (flipAt u y) <;> cases g (flipAt v y) <;>
    cases g (flipAt u (flipAt v y)) <;> rfl

/-- The prefix-OR functions `g_e(y) = ⋁_{i<e} y_i`. -/
def prefixOrG : ℕ → (ℕ → Bool) → Bool := fun e y => decide (∃ i < e, y i = true)

/-- **Masked prefix OR** (009e, Theorem 6.2): `⋁_{i ≤ e} y_i = ⋁_{i ≤ e} x_i`. -/
theorem maskedPrefixOr_prefix (x : ℕ → Bool) (e : ℕ) :
    (∃ i ≤ e, maskedY prefixOrG x i = true) ↔ (∃ i ≤ e, x i = true) := by
  have hstep : ∀ e, maskedY prefixOrG x e =
      Bool.xor (x e) (decide (∃ i < e, maskedY prefixOrG x i = true)) := by
    intro e
    rw [maskedY_eq]
    congr 1
    simp only [prefixOrG, restrictLT]
    apply Bool.decide_congr
    constructor
    · rintro ⟨i, hi, h⟩; exact ⟨i, hi, by simpa [hi] using h⟩
    · rintro ⟨i, hi, h⟩; exact ⟨i, hi, by simpa [hi] using h⟩
  induction e with
  | zero =>
    have := hstep 0
    simp only [Nat.not_lt_zero, false_and, exists_false, decide_false, Bool.xor_false] at this
    simp [this]
  | succ e ih =>
    by_cases hp : ∃ i ≤ e, maskedY prefixOrG x i = true
    · obtain ⟨i, hi, h⟩ := hp
      obtain ⟨i', hi', h'⟩ := ih.1 ⟨i, hi, h⟩
      exact ⟨fun _ => ⟨i', by omega, h'⟩, fun _ => ⟨i, by omega, h⟩⟩
    · have hx : ¬ ∃ i ≤ e, x i = true := fun h => hp (ih.2 h)
      have hy : maskedY prefixOrG x (e + 1) = x (e + 1) := by
        rw [hstep]
        have : ¬ ∃ i < e + 1, maskedY prefixOrG x i = true :=
          fun ⟨i, hi, h⟩ => hp ⟨i, by omega, h⟩
        simp [this]
      constructor
      · rintro ⟨i, hi, h⟩
        rcases Nat.lt_or_ge i (e + 1) with h' | h'
        · exact absurd ⟨i, by omega, h⟩ hp
        · obtain rfl : i = e + 1 := by omega
          exact ⟨e + 1, le_rfl, hy ▸ h⟩
      · rintro ⟨i, hi, h⟩
        rcases Nat.lt_or_ge i (e + 1) with h' | h'
        · exact absurd ⟨i, by omega, h⟩ hx
        · obtain rfl : i = e + 1 := by omega
          exact ⟨e + 1, le_rfl, hy.symm ▸ h⟩

/-- **Masked prefix OR** (009e, Theorem 6.2): `y_e = x_e ⊕ ⋁_{i<e} x_i`. -/
theorem maskedPrefixOr_formula (x : ℕ → Bool) (e : ℕ) :
    maskedY prefixOrG x e = Bool.xor (x e) (decide (∃ i < e, x i = true)) := by
  rw [maskedY_eq]
  congr 1
  simp only [prefixOrG, restrictLT]
  apply Bool.decide_congr
  cases e with
  | zero => simp
  | succ e =>
    have := maskedPrefixOr_prefix x e
    constructor
    · rintro ⟨i, hi, h⟩
      obtain ⟨i', hi', h'⟩ := this.1 ⟨i, by omega, by simpa [hi] using h⟩
      exact ⟨i', by omega, h'⟩
    · rintro ⟨i, hi, h⟩
      obtain ⟨i', hi', h'⟩ := this.2 ⟨i, by omega, h⟩
      exact ⟨i', by omega, by simpa [show i' < e + 1 by omega] using h'⟩

/-- **Masked prefix OR** (009e, Theorem 6.2): the curvature hypergraph is complete: for all
`u < v < e`, `{u, v}` is a curvature pair of `g_e` (the mixed derivative is `1` at `y = 0`). -/
theorem maskedPrefixOr_curvature_complete (u v e : ℕ) (huv : u < v) (hve : v < e) :
    mixedDeriv u v (prefixOrG e) (fun _ => false) = true := by
  have h1 : prefixOrG e (fun _ => false) = false := by simp [prefixOrG]
  have h2 : prefixOrG e (flipAt u (fun _ => false)) = true := by
    simp only [prefixOrG, decide_eq_true_eq]
    exact ⟨u, by omega, by simp [flipAt]⟩
  have h3 : prefixOrG e (flipAt v (fun _ => false)) = true := by
    simp only [prefixOrG, decide_eq_true_eq]
    exact ⟨v, hve, by simp [flipAt]⟩
  have h4 : prefixOrG e (flipAt u (flipAt v (fun _ => false))) = true := by
    simp only [prefixOrG, decide_eq_true_eq]
    exact ⟨v, hve, by simp [flipAt, Function.update, show v ≠ u by omega]⟩
  simp only [mixedDeriv, h1, h2, h3, h4]
  rfl

/-- The reduction of Theorem 6.3 (009e): with the zero mask, the masked recurrence is the
chronological evaluation `y_e = g_e(y_{<e})`. -/
theorem maskedY_zero_mask (g : ℕ → (ℕ → Bool) → Bool) (e : ℕ) :
    maskedY g (fun _ => false) e = g e (restrictLT (maskedY g (fun _ => false)) e) := by
  rw [maskedY_eq]; simp

/-! ### Moral graphs -/

/-- The moral graph of a literal-binary program whose operator scopes are the triples
`(e, p, q)` satisfying `scope`: the scope of every operator is a clique. -/
def moralGraph {R : Type*} (scope : R → R → R → Prop) : SimpleGraph R :=
  SimpleGraph.fromRel fun u v => ∃ e p q, scope e p q ∧ (u = e ∨ u = p ∨ u = q) ∧
    (v = e ∨ v = p ∨ v = q)

theorem moralGraph_adj {R : Type*} {scope : R → R → R → Prop} {e p q u v : R}
    (h : scope e p q) (hu : u = e ∨ u = p ∨ u = q) (hv : v = e ∨ v = p ∨ v = q) (hne : u ≠ v) :
    (moralGraph scope).Adj u v :=
  ⟨hne, Or.inl ⟨e, p, q, h, hu, hv⟩⟩

/-! ### The reverse-prefix family (Theorem 4.1) -/

/-- Records of the reverse-prefix program: `z r` (raw for `r ≤ 2`), the record `a`, and the
helpers `O i r`. -/
inductive RPRec
  | z (r : ℕ)
  | a
  | O (i r : ℕ)
  deriving DecidableEq

/-- First component of the chronological key (used only for termination). -/
def RPRec.k1 : RPRec → ℕ
  | .z r => r
  | .a => 2
  | .O _ r => r

/-- Second component of the chronological key (used only for termination). -/
def RPRec.k2 : RPRec → ℕ
  | .z _ => 0
  | .a => 1
  | .O i r => r + 1 - i

/-- The values of the reverse-prefix program on the raw inputs `z₁, z₂`:
`a = z₁ ∧ z₂`, `O_{r-1,r} = z_{r-1} ∨ z_r`, `O_{i,r} = z_i ∨ O_{i+1,r}` (`i ≤ r - 2`) and
`z_{r+1} = O_{1,r} ∨ a` (`r ≥ 2`). Arguments outside the program evaluate to `false`. -/
def rpVal (z₁ z₂ : Bool) : RPRec → Bool
  | .z 0 => false
  | .z 1 => z₁
  | .z 2 => z₂
  | .z (r + 3) => rpVal z₁ z₂ (.O 1 (r + 2)) || rpVal z₁ z₂ .a
  | .a => z₁ && z₂
  | .O i r =>
    if _h : 1 ≤ i ∧ i + 1 < r then rpVal z₁ z₂ (.z i) || rpVal z₁ z₂ (.O (i + 1) r)
    else if _h' : 1 ≤ i ∧ i + 1 = r then rpVal z₁ z₂ (.z i) || rpVal z₁ z₂ (.z r)
    else false
termination_by x => (x.k1, x.k2)
decreasing_by
  all_goals simp_wf
  all_goals simp only [RPRec.k1, RPRec.k2, Prod.lex_def, true_and]
  all_goals omega

/-- The helper `O_{i,r}` is the OR `z_i ∨ ⋯ ∨ z_r`. -/
theorem rpVal_O (z₁ z₂ : Bool) :
    ∀ d i, 1 ≤ i → (rpVal z₁ z₂ (.O i (i + 1 + d)) = true ↔
      ∃ k, i ≤ k ∧ k ≤ i + 1 + d ∧ rpVal z₁ z₂ (.z k) = true) := by
  intro d
  induction d with
  | zero =>
    intro i hi
    rw [rpVal, dif_neg (by omega), dif_pos ⟨hi, by omega⟩, Bool.or_eq_true]
    constructor
    · rintro (h | h)
      · exact ⟨i, le_rfl, by omega, h⟩
      · exact ⟨i + 1, by omega, le_rfl, h⟩
    · rintro ⟨k, hk1, hk2, h⟩
      rcases Nat.eq_or_lt_of_le hk1 with rfl | hk
      · exact Or.inl h
      · obtain rfl : k = i + 1 := by omega
        exact Or.inr h
  | succ d ih =>
    intro i hi
    rw [rpVal, dif_pos ⟨hi, by omega⟩, Bool.or_eq_true,
      show i + 1 + (d + 1) = i + 1 + 1 + d by omega, ih (i + 1) (by omega)]
    constructor
    · rintro (h | ⟨k, hk1, hk2, h⟩)
      · exact ⟨i, le_rfl, by omega, h⟩
      · exact ⟨k, by omega, hk2, h⟩
    · rintro ⟨k, hk1, hk2, h⟩
      rcases Nat.eq_or_lt_of_le hk1 with rfl | hk
      · exact Or.inl h
      · exact Or.inr ⟨k, by omega, hk2, h⟩

/-- **Reverse prefix, value** (009e, Theorem 4.1): `z_r = z_1 ∨ z_2` for all `r ≥ 3`. -/
theorem revPrefix_value (z₁ z₂ : Bool) (r : ℕ) (hr : 3 ≤ r) :
    rpVal z₁ z₂ (.z r) = (z₁ || z₂) := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    obtain ⟨r, rfl⟩ : ∃ r', r = r' + 3 := ⟨r - 3, by omega⟩
    rw [rpVal]
    have ha : rpVal z₁ z₂ .a = (z₁ && z₂) := by rw [rpVal]
    rw [ha]
    have hO := rpVal_O z₁ z₂ r 1 le_rfl
    rw [show 1 + 1 + r = r + 2 by omega] at hO
    have hex : (∃ k, 1 ≤ k ∧ k ≤ r + 2 ∧ rpVal z₁ z₂ (.z k) = true) ↔
        (z₁ = true ∨ z₂ = true) := by
      constructor
      · rintro ⟨k, hk1, hk2, h⟩
        match k, hk1, h with
        | 1, _, h => left; rw [rpVal] at h; exact h
        | 2, _, h => right; rw [rpVal] at h; exact h
        | k + 3, _, h =>
          rw [ih (k + 3) (by omega) (by omega)] at h
          simpa using h
      · rintro (h | h)
        · exact ⟨1, le_rfl, by omega, by rw [rpVal]; exact h⟩
        · exact ⟨2, by omega, by omega, by rw [rpVal]; exact h⟩
    rw [hex] at hO
    by_cases hv : rpVal z₁ z₂ (.O 1 (r + 2)) = true
    · have := hO.1 hv
      rw [hv]
      cases z₁ <;> cases z₂ <;> simp_all
    · have : ¬ (z₁ = true ∨ z₂ = true) := fun h => hv (hO.2 h)
      simp only [Bool.not_eq_true] at hv
      rw [hv]
      cases z₁ <;> cases z₂ <;> simp_all

/-- The operator scopes `(e, p, q)` of the reverse-prefix program with parameter `h`. -/
def rpScope (h : ℕ) (e p q : RPRec) : Prop :=
  (e = .a ∧ p = .z 1 ∧ q = .z 2) ∨
    ∃ r, 2 ≤ r ∧ r ≤ h - 1 ∧
      ((e = .O (r - 1) r ∧ p = .z (r - 1) ∧ q = .z r) ∨
        (∃ i, 1 ≤ i ∧ i ≤ r - 2 ∧ e = .O i r ∧ p = .z i ∧ q = .O (i + 1) r) ∨
        (e = .z (r + 1) ∧ p = .O 1 r ∧ q = .a))

/-- The records of the reverse-prefix program with parameter `h`. -/
def rpIsRecord (h : ℕ) : RPRec → Prop
  | .z r => 1 ≤ r ∧ r ≤ h
  | .a => True
  | .O i r => 1 ≤ i ∧ i < r ∧ 2 ≤ r ∧ r ≤ h - 1

/-- **Reverse prefix, minor** (009e, Theorem 4.1). Let `h ≥ 3` and `k = ⌊(h-1)/2⌋`. In the moral
graph of the reverse-prefix program, the branch sets `A_i = {z_i}` (`1 ≤ i ≤ k`) and
`B_r = {O_{1,r}, …, O_{k,r}}` (`k + 1 ≤ r ≤ 2k`) consist of records of the program, are
pairwise disjoint, each `B_r` is connected by the moral edges `O_{i,r} O_{i+1,r}`, and every
`A_i` is adjacent to every `B_r` (through the edge `z_i O_{i,r}`). Contracting the `B_r` gives
a `K_{k,k}` minor. -/
theorem revPrefix_minor_model (h : ℕ) (hh : 3 ≤ h) :
    let k := (h - 1) / 2
    let G := moralGraph (rpScope h)
    1 ≤ k ∧
    (∀ i, 1 ≤ i → i ≤ k → rpIsRecord h (.z i)) ∧
    (∀ i r, 1 ≤ i → i ≤ k → k + 1 ≤ r → r ≤ 2 * k → rpIsRecord h (.O i r)) ∧
    (∀ i i' r, RPRec.z i' ≠ RPRec.O i r) ∧
    (∀ i i' r r', r ≠ r' → RPRec.O i r ≠ RPRec.O i' r') ∧
    (∀ i r, 1 ≤ i → i < k → k + 1 ≤ r → r ≤ 2 * k → G.Adj (.O i r) (.O (i + 1) r)) ∧
    (∀ i r, 1 ≤ i → i ≤ k → k + 1 ≤ r → r ≤ 2 * k → G.Adj (.z i) (.O i r)) := by
  intro k G
  refine ⟨by omega, fun i h1 h2 => ⟨h1, by omega⟩, fun i r h1 h2 h3 h4 => ⟨h1, by omega, by omega,
    by omega⟩, fun _ _ _ => RPRec.noConfusion, fun i i' r r' hne heq => hne (by cases heq; rfl),
    ?_, ?_⟩
  · intro i r h1 h2 h3 h4
    refine moralGraph_adj (e := .O i r) (p := .z i) (q := .O (i + 1) r) ?_ (Or.inl rfl)
      (Or.inr (Or.inr rfl)) (by simp)
    exact Or.inr ⟨r, by omega, by omega, Or.inr (Or.inl ⟨i, h1, by omega, rfl, rfl, rfl⟩)⟩
  · intro i r h1 h2 h3 h4
    by_cases hir : i + 1 = r
    · refine moralGraph_adj (e := .O (r - 1) r) (p := .z (r - 1)) (q := .z r) ?_
        (Or.inr (Or.inl (by rw [← hir]; rfl))) (Or.inl (by rw [← hir]; rfl)) (by simp)
      exact Or.inr ⟨r, by omega, by omega, Or.inl ⟨rfl, rfl, rfl⟩⟩
    · refine moralGraph_adj (e := .O i r) (p := .z i) (q := .O (i + 1) r) ?_
        (Or.inr (Or.inl rfl)) (Or.inl rfl) (by simp)
      exact Or.inr ⟨r, by omega, by omega, Or.inr (Or.inl ⟨i, h1, by omega, rfl, rfl, rfl⟩)⟩

/-! ### Disjoint moral triangles (Theorem 4.2) -/

/-- Records of the triangle grid: raw inputs `A_i, B_j, C_i, D_j` and the records
`u_{ij} = A_i ∧ B_j`, `v_{ij} = C_i ∧ D_j`, `t_{ij} = u_{ij} ∧ v_{ij}`. -/
inductive TriRec (r : ℕ)
  | A (i : Fin r)
  | B (j : Fin r)
  | C (i : Fin r)
  | D (j : Fin r)
  | u (i j : Fin r)
  | v (i j : Fin r)
  | t (i j : Fin r)
  deriving DecidableEq, Fintype

/-- The operator scopes of the triangle grid. -/
def triScope (r : ℕ) (e p q : TriRec r) : Prop :=
  ∃ i j, (e = .u i j ∧ p = .A i ∧ q = .B j) ∨ (e = .v i j ∧ p = .C i ∧ q = .D j) ∨
    (e = .t i j ∧ p = .u i j ∧ q = .v i j)

/-- The triangle grid has `3r² + 4r` records. -/
theorem triGrid_card (r : ℕ) : Fintype.card (TriRec r) = 3 * r ^ 2 + 4 * r := by
  let e : TriRec r ≃ (Fin r ⊕ Fin r ⊕ Fin r ⊕ Fin r) ⊕ (Fin r × Fin r ⊕ Fin r × Fin r ⊕
      Fin r × Fin r) :=
    { toFun := fun x => match x with
        | .A i => .inl (.inl i)
        | .B j => .inl (.inr (.inl j))
        | .C i => .inl (.inr (.inr (.inl i)))
        | .D j => .inl (.inr (.inr (.inr j)))
        | .u i j => .inr (.inl (i, j))
        | .v i j => .inr (.inr (.inl (i, j)))
        | .t i j => .inr (.inr (.inr (i, j)))
      invFun := fun y => match y with
        | .inl (.inl i) => .A i
        | .inl (.inr (.inl j)) => .B j
        | .inl (.inr (.inr (.inl i))) => .C i
        | .inl (.inr (.inr (.inr j))) => .D j
        | .inr (.inl (i, j)) => .u i j
        | .inr (.inr (.inl (i, j))) => .v i j
        | .inr (.inr (.inr (i, j))) => .t i j
      left_inv := fun x => by cases x <;> rfl
      right_inv := fun y => by
        rcases y with ((_ | _ | _ | _) | (⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩)) <;> rfl }
  rw [Fintype.card_congr e]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  ring

/-- **Disjoint moral triangles** (009e, Theorem 4.2): every vertex cover of the moral graph of
the triangle grid has at least `2r²` vertices. -/
theorem triGrid_vertexCover_card (r : ℕ) (S : Finset (TriRec r))
    (hS : ∀ x y, (moralGraph (triScope r)).Adj x y → x ∈ S ∨ y ∈ S) : 2 * r ^ 2 ≤ S.card := by
  classical
  let tri : Fin r × Fin r → Finset (TriRec r) := fun p =>
    {TriRec.u p.1 p.2, TriRec.v p.1 p.2, TriRec.t p.1 p.2}
  have hscope : ∀ i j, triScope r (.t i j) (.u i j) (.v i j) :=
    fun i j => ⟨i, j, Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)⟩
  have htwo : ∀ p, 2 ≤ (S.filter (· ∈ tri p)).card := by
    rintro ⟨i, j⟩
    have huv := hS _ _ (moralGraph_adj (hscope i j) (Or.inr (Or.inl rfl))
      (Or.inr (Or.inr rfl)) (by simp))
    have hut := hS _ _ (moralGraph_adj (hscope i j) (Or.inr (Or.inl rfl))
      (Or.inl rfl) (by simp))
    have hvt := hS _ _ (moralGraph_adj (hscope i j) (Or.inr (Or.inr rfl))
      (Or.inl rfl) (by simp))
    have pair : ∀ x y : TriRec r, x ≠ y → x ∈ S → y ∈ S → x ∈ tri (i, j) → y ∈ tri (i, j) →
        2 ≤ (S.filter (· ∈ tri (i, j))).card := by
      intro x y hxy hx hy hx' hy'
      calc 2 = ({x, y} : Finset (TriRec r)).card := (Finset.card_pair hxy).symm
        _ ≤ _ := Finset.card_le_card (by
          intro w hw
          rw [Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl
          · exact Finset.mem_filter.2 ⟨hx, hx'⟩
          · exact Finset.mem_filter.2 ⟨hy, hy'⟩)
    have m1 : TriRec.u i j ∈ tri (i, j) := by simp [tri]
    have m2 : TriRec.v i j ∈ tri (i, j) := by simp [tri]
    have m3 : TriRec.t i j ∈ tri (i, j) := by simp [tri]
    by_cases a1 : TriRec.u i j ∈ S <;> by_cases a2 : TriRec.v i j ∈ S <;>
      by_cases a3 : TriRec.t i j ∈ S <;> simp_all
    · exact pair _ _ (by simp) a1 a2 m1 m2
    · exact pair _ _ (by simp) a1 a2 m1 m2
    · exact pair _ _ (by simp) a1 a3 m1 m3
    · exact pair _ _ (by simp) a2 a3 m2 m3
  have hdisj : ∀ p ∈ (Finset.univ : Finset (Fin r × Fin r)), ∀ p' ∈ Finset.univ, p ≠ p' →
      Disjoint (S.filter (· ∈ tri p)) (S.filter (· ∈ tri p')) := by
    rintro ⟨i, j⟩ _ ⟨i', j'⟩ _ hne
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_filter, tri, Finset.mem_insert, Finset.mem_singleton] at hx hx'
    apply hne
    rcases hx.2 with rfl | rfl | rfl <;> rcases hx'.2 with h | h | h <;> (cases h <;> rfl)
  calc 2 * r ^ 2 = ∑ _p : Fin r × Fin r, 2 := by simp [Finset.card_univ]; ring
    _ ≤ ∑ p : Fin r × Fin r, (S.filter (· ∈ tri p)).card := Finset.sum_le_sum fun p _ => htwo p
    _ = (Finset.univ.biUnion fun p => S.filter (· ∈ tri p)).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ S.card := Finset.card_le_card (by
        intro x hx
        simp only [Finset.mem_biUnion, Finset.mem_filter] at hx
        obtain ⟨_, _, hx, _⟩ := hx
        exact hx)

/-- **Disjoint moral triangles** (009e, Theorem 4.2): the moral edges `A_i B_j` form a
complete bipartite graph `K_{r,r}`. -/
theorem triGrid_Krr (r : ℕ) (i j : Fin r) :
    (moralGraph (triScope r)).Adj (.A i) (.B j) :=
  moralGraph_adj (e := .u i j) ⟨i, j, Or.inl ⟨rfl, rfl, rfl⟩⟩ (Or.inr (Or.inl rfl))
    (Or.inr (Or.inr rfl)) (by simp)

end GC.GridCompilers
