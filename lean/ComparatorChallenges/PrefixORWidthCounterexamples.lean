import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.DeriveFintype
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Comparator challenge: Prefix-OR Defeats Treewidth and Curvature Measures (009e)

Self-contained statement file (imports only Mathlib). The definitions are copied verbatim
from the solution files; the main theorems are stated with `sorry`.
-/

namespace GC.GridCompilers

/-- `restrictLT y e` keeps the coordinates `i < e` of `y` and zeroes the others. -/
def restrictLT (y : ℕ → Bool) (e : ℕ) : ℕ → Bool := fun i => if i < e then y i else false

/-- The masked recurrence `y_e = x_e ⊕ g_e(y_{<e})`. -/
def maskedY (g : ℕ → (ℕ → Bool) → Bool) (x : ℕ → Bool) : ℕ → Bool
  | e => Bool.xor (x e) (g e (fun i => if _h : i < e then maskedY g x i else false))
termination_by e => e

/-- The inverse map `x_e = y_e ⊕ g_e(y_{<e})`. -/
def unmask (g : ℕ → (ℕ → Bool) → Bool) (y : ℕ → Bool) : ℕ → Bool :=
  fun e => Bool.xor (y e) (g e (restrictLT y e))

/-- **Masking** (009e, Lemma 6.1), left inverse. -/
theorem unmask_maskedY (g : ℕ → (ℕ → Bool) → Bool) (x : ℕ → Bool) :
    unmask g (maskedY g x) = x := by
  sorry

/-- **Masking** (009e, Lemma 6.1), right inverse. -/
theorem maskedY_unmask (g : ℕ → (ℕ → Bool) → Bool) (y : ℕ → Bool) :
    maskedY g (unmask g y) = y := by
  sorry

/-- **Masking** (009e, Lemma 6.1): for fixed `g`, `x ↦ y` is a bijection. -/
theorem maskedY_bijective (g : ℕ → (ℕ → Bool) → Bool) : Function.Bijective (maskedY g) := by
  sorry

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
  sorry

/-- The prefix-OR functions `g_e(y) = ⋁_{i<e} y_i`. -/
def prefixOrG : ℕ → (ℕ → Bool) → Bool := fun e y => decide (∃ i < e, y i = true)

/-- **Masked prefix OR** (009e, Theorem 6.2): `⋁_{i ≤ e} y_i = ⋁_{i ≤ e} x_i`. -/
theorem maskedPrefixOr_prefix (x : ℕ → Bool) (e : ℕ) :
    (∃ i ≤ e, maskedY prefixOrG x i = true) ↔ (∃ i ≤ e, x i = true) := by
  sorry

/-- **Masked prefix OR** (009e, Theorem 6.2): `y_e = x_e ⊕ ⋁_{i<e} x_i`. -/
theorem maskedPrefixOr_formula (x : ℕ → Bool) (e : ℕ) :
    maskedY prefixOrG x e = Bool.xor (x e) (decide (∃ i < e, x i = true)) := by
  sorry

/-- **Masked prefix OR** (009e, Theorem 6.2): the curvature hypergraph is complete: for all
`u < v < e`, `{u, v}` is a curvature pair of `g_e` (the mixed derivative is `1` at `y = 0`). -/
theorem maskedPrefixOr_curvature_complete (u v e : ℕ) (huv : u < v) (hve : v < e) :
    mixedDeriv u v (prefixOrG e) (fun _ => false) = true := by
  sorry

/-- The reduction of Theorem 6.3 (009e): with the zero mask, the masked recurrence is the
chronological evaluation `y_e = g_e(y_{<e})`. -/
theorem maskedY_zero_mask (g : ℕ → (ℕ → Bool) → Bool) (e : ℕ) :
    maskedY g (fun _ => false) e = g e (restrictLT (maskedY g (fun _ => false)) e) := by
  sorry

/-- The moral graph of a literal-binary program whose operator scopes are the triples
`(e, p, q)` satisfying `scope`: the scope of every operator is a clique. -/
def moralGraph {R : Type*} (scope : R → R → R → Prop) : SimpleGraph R :=
  SimpleGraph.fromRel fun u v => ∃ e p q, scope e p q ∧ (u = e ∨ u = p ∨ u = q) ∧
    (v = e ∨ v = p ∨ v = q)

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

/-- **Reverse prefix, value** (009e, Theorem 4.1): `z_r = z_1 ∨ z_2` for all `r ≥ 3`. -/
theorem revPrefix_value (z₁ z₂ : Bool) (r : ℕ) (hr : 3 ≤ r) :
    rpVal z₁ z₂ (.z r) = (z₁ || z₂) := by
  sorry

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
  sorry

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
  sorry

/-- **Disjoint moral triangles** (009e, Theorem 4.2): every vertex cover of the moral graph of
the triangle grid has at least `2r²` vertices. -/
theorem triGrid_vertexCover_card (r : ℕ) (S : Finset (TriRec r))
    (hS : ∀ x y, (moralGraph (triScope r)).Adj x y → x ∈ S ∨ y ∈ S) : 2 * r ^ 2 ≤ S.card := by
  sorry

/-- **Disjoint moral triangles** (009e, Theorem 4.2): the moral edges `A_i B_j` form a
complete bipartite graph `K_{r,r}`. -/
theorem triGrid_Krr (r : ℕ) (i j : Fin r) :
    (moralGraph (triScope r)).Adj (.A i) (.B j) := by
  sorry

end GC.GridCompilers
