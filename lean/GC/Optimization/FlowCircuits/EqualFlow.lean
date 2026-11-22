import GC.Optimization.FlowCircuits.Basic
import GC.Optimization.FlowCircuits.Circuit
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Combination
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Manuscript 003d: P-complete equal-flow programs with capacities at most two

* `nand_normalization` : Theorem 2.1 (in an alternating monotone circuit, complementing the values
  of the AND gates turns every gate into a NAND gate of its encoded inputs).
* `nand_polytope` : Theorem 3.1 (the convex hull of the four NAND triples is
  `{z + x ≥ 1, z + y ≥ 1, z + x + y ≤ 2} ∩ [0,1]^3`).
* `forcing` : Lemma 3.2.
* `dyadic_elimination` : Theorem 4.2 (iv)–(v) for the residual NAND program of Definition 4.1:
  the transcript point is feasible of cost `0`, every feasible point has cost `≥ 0`, and every
  feasible point of cost `0` coincides with the transcript point.
* `cut_bound`, `cut_size_bound` : Proposition 6.1.
-/

namespace GC.FlowCircuits

open Finset

namespace MonCircuit

variable {n : ℕ} (C : MonCircuit n)

/-- Alternation: a gate child of an AND gate is an OR gate and a gate child of an OR gate is an
AND gate. -/
def Alternating : Prop :=
  ∀ v a c₁ c₂, C.node v = .gate a c₁ c₂ → ∀ a' d₁ d₂,
    (C.node c₁ = .gate a' d₁ d₂ → a' = !a) ∧ (C.node c₂ = .gate a' d₁ d₂ → a' = !a)

/-- Is `v` a gate? -/
def isGate (v : Fin n) : Bool :=
  match C.node v with
  | .gate _ _ _ => true
  | .input _ => false

/-- The type of a gate (`true` = AND). -/
def gtype (v : Fin n) : Bool :=
  match C.node v with
  | .gate a _ _ => a
  | .input _ => false

/-- The `k`-th child of a gate (`k = 0, 1`). -/
def kid (v : Fin n) (k : Fin 2) : Fin n :=
  match C.node v with
  | .gate _ c₁ c₂ => ![c₁, c₂] k
  | .input _ => v

/-- The transformed bit `b_v`: `t_v` for an OR gate and `1 - t_v` for an AND gate. -/
def tbit (v : Fin n) : Bool :=
  match C.node v with
  | .gate a _ _ => if a then !C.val v else C.val v
  | .input _ => C.val v

/-- `b_{u → v}` for a predecessor `u` of a gate of type `a`: the transformed bit `b_u` if `u` is
a gate, and the encoded constant (`t_u` below an AND gate, `1 - t_u` below an OR gate) if `u` is
an input. -/
def edgeBit (a : Bool) (u : Fin n) : Bool :=
  match C.node u with
  | .input t => if a then t else !t
  | .gate _ _ _ => C.tbit u

variable {C}

lemma edgeBit_eq (hC : C.Alternating) {v c₁ c₂ : Fin n} {a : Bool}
    (h : C.node v = .gate a c₁ c₂) :
    C.edgeBit a c₁ = (if a then C.val c₁ else !C.val c₁) ∧
      C.edgeBit a c₂ = (if a then C.val c₂ else !C.val c₂) := by
  constructor
  · unfold edgeBit
    split
    · rename_i t ht; rw [C.val_input ht]
    · rename_i a' d₁ d₂ hg
      have := (hC v a c₁ c₂ h a' d₁ d₂).1 hg
      unfold tbit; rw [hg]; subst this; cases a <;> simp
  · unfold edgeBit
    split
    · rename_i t ht; rw [C.val_input ht]
    · rename_i a' d₁ d₂ hg
      have := (hC v a c₁ c₂ h a' d₁ d₂).2 hg
      unfold tbit; rw [hg]; subst this; cases a <;> simp

/-- **Theorem 2.1 (NAND normalization).** In an alternating monotone circuit every gate `v` with
predecessors `u, w` satisfies `b_v = NAND(b_{u→v}, b_{w→v})`. -/
theorem nand_normalization (hC : C.Alternating) {v c₁ c₂ : Fin n} {a : Bool}
    (h : C.node v = .gate a c₁ c₂) :
    C.tbit v = !(C.edgeBit a c₁ && C.edgeBit a c₂) := by
  obtain ⟨e1, e2⟩ := edgeBit_eq hC h
  rw [e1, e2]
  unfold tbit; rw [h, C.val_gate h]
  cases a <;> cases C.val c₁ <;> cases C.val c₂ <;> rfl

lemma kid_lt {v c₁ c₂ : Fin n} {a : Bool} (h : C.node v = .gate a c₁ c₂) (k : Fin 2) :
    C.kid v k < v := by
  have := C.topo v a c₁ c₂ h
  unfold kid; rw [h]; fin_cases k
  · exact this.1
  · exact this.2

lemma edgeBit_of_isGate {u : Fin n} (a : Bool) (hu : C.isGate u = true) :
    C.edgeBit a u = C.tbit u := by
  unfold edgeBit; unfold isGate at hu; split <;> simp_all

end MonCircuit

/-! ### The NAND polytope -/

/-- The four NAND triples `(x, y, NAND(x, y))`. -/
def nandPoints : Set (ℝ × ℝ × ℝ) := {(0, 0, 1), (0, 1, 1), (1, 0, 1), (1, 1, 0)}

/-- The polytope `P = {(x,y,z) ∈ [0,1]^3 : z + x ≥ 1, z + y ≥ 1, z + x + y ≤ 2}`. -/
def nandPolytope : Set (ℝ × ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2.1 ∧ p.2.1 ≤ 1 ∧ 0 ≤ p.2.2 ∧ p.2.2 ≤ 1 ∧
    1 ≤ p.2.2 + p.1 ∧ 1 ≤ p.2.2 + p.2.1 ∧ p.2.2 + p.1 + p.2.1 ≤ 2}

lemma nandPolytope_convex : Convex ℝ nandPolytope := by
  intro p hp q hq a b ha hb hab
  obtain ⟨p1, p2, p3⟩ := p
  obtain ⟨q1, q2, q3⟩ := q
  simp only [nandPolytope, Set.mem_setOf_eq, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at *
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hp
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9⟩ := hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    nlinarith [mul_nonneg ha h1, mul_nonneg hb k1, mul_nonneg ha h3, mul_nonneg hb k3,
      mul_nonneg ha h5, mul_nonneg hb k5, mul_nonneg ha (sub_nonneg.mpr h2),
      mul_nonneg hb (sub_nonneg.mpr k2), mul_nonneg ha (sub_nonneg.mpr h4),
      mul_nonneg hb (sub_nonneg.mpr k4), mul_nonneg ha (sub_nonneg.mpr h6),
      mul_nonneg hb (sub_nonneg.mpr k6), mul_nonneg ha (sub_nonneg.mpr h7),
      mul_nonneg hb (sub_nonneg.mpr k7), mul_nonneg ha (sub_nonneg.mpr h8),
      mul_nonneg hb (sub_nonneg.mpr k8), mul_nonneg ha (sub_nonneg.mpr h9),
      mul_nonneg hb (sub_nonneg.mpr k9)]

/-- **Theorem 3.1 (NAND polytope).** The convex hull of the four NAND triples is cut out of the
unit cube by `z + x ≥ 1`, `z + y ≥ 1` and `z + x + y ≤ 2`. -/
theorem nand_polytope : convexHull ℝ nandPoints = nandPolytope := by
  apply Set.Subset.antisymm
  · apply convexHull_min _ nandPolytope_convex
    intro p hp
    simp only [nandPoints, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> simp [nandPolytope] <;> norm_num
  · rintro ⟨x, y, z⟩ ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    -- barycentric coordinates
    let w : Fin 4 → ℝ := ![2 - x - y - z, y + z - 1, x + z - 1, 1 - z]
    let pt : Fin 4 → ℝ × ℝ × ℝ := ![(0, 0, 1), (0, 1, 1), (1, 0, 1), (1, 1, 0)]
    have hmem : ∑ i, w i • pt i ∈ convexHull ℝ nandPoints := by
      apply Convex.sum_mem (convex_convexHull ℝ nandPoints)
      · intro i _; fin_cases i <;> simp [w] <;> linarith
      · simp [w, Fin.sum_univ_four]; ring
      · intro i _; apply subset_convexHull; fin_cases i <;> simp [pt, nandPoints]
    have heq : ∑ i, w i • pt i = (x, y, z) := by
      ext <;> simp [Fin.sum_univ_four, w, pt] <;> ring
    rw [heq] at hmem
    exact hmem

/-- **Lemma 3.2 (forcing).** If `x, y ∈ {0,1}` and `z ∈ [0,1]` satisfy the three NAND
inequalities, then `z = NAND(x, y)`. -/
theorem forcing (x y : Bool) (z : ℝ) (h0 : 0 ≤ z) (h1 : z ≤ 1) (hx : 1 ≤ z + b2r x)
    (hy : 1 ≤ z + b2r y) (hs : z + b2r x + b2r y ≤ 2) : z = b2r (!(x && y)) := by
  cases x <;> cases y <;> simp [b2r] at * <;> linarith

/-! ### The residual NAND program -/

/-- A point of the residual NAND program (Definition 4.1). For a gate `v`: `zocc v = z_v` is its
own occurrence, `cocc v k` (`k = 0, 1`) are the occurrences `x_v, y_v` of its two predecessors;
`slack v = s` and `surplus v k = r_x, r_y` are the slacks of the rows (3.1); `pos v k`, `neg v k`
are the variables `p, n` of the spanning-tree edge joining the occurrence `cocc v k` of the `k`-th
child, when it is a gate `u`, to the occurrence `zocc u` (we use the star spanning tree of
`Occ(u)` centred at `z_u`). -/
structure ResPoint (n : ℕ) where
  zocc : Fin n → ℝ
  cocc : Fin n → Fin 2 → ℝ
  slack : Fin n → ℝ
  surplus : Fin n → Fin 2 → ℝ
  pos : Fin n → Fin 2 → ℝ
  neg : Fin n → Fin 2 → ℝ

namespace MonCircuit

variable {n : ℕ} (C : MonCircuit n)

/-- Feasibility for the residual NAND program (Definition 4.1): bounds, the three rows
`z + x + y + s = 2`, `z + x - r_x = 1`, `z + y - r_y = 1` of every gate, input occurrences fixed
to their encoded constants, and the tree-edge equations `o_a - o_{a'} - p + n = 0`. -/
def ResFeasible (P : ResPoint n) : Prop :=
  ∀ v, C.isGate v = true →
    (0 ≤ P.zocc v ∧ P.zocc v ≤ 1) ∧ (∀ k, 0 ≤ P.cocc v k ∧ P.cocc v k ≤ 1) ∧
    (0 ≤ P.slack v ∧ P.slack v ≤ 2) ∧ (∀ k, 0 ≤ P.surplus v k ∧ P.surplus v k ≤ 1) ∧
    P.zocc v + P.cocc v 0 + P.cocc v 1 + P.slack v = 2 ∧
    (∀ k, P.zocc v + P.cocc v k - P.surplus v k = 1) ∧
    ∀ k,
      (C.isGate (C.kid v k) = false →
        P.cocc v k = b2r (C.edgeBit (C.gtype v) (C.kid v k))) ∧
      (C.isGate (C.kid v k) = true →
        0 ≤ P.pos v k ∧ P.pos v k ≤ 1 ∧ 0 ≤ P.neg v k ∧ P.neg v k ≤ 1 ∧
        P.cocc v k - P.zocc (C.kid v k) - P.pos v k + P.neg v k = 0)

/-- The objective `∑ (p + n)` over all tree edges. -/
def resCost (P : ResPoint n) : ℝ :=
  ∑ v, ∑ k : Fin 2,
    if C.isGate v = true ∧ C.isGate (C.kid v k) = true then P.pos v k + P.neg v k else 0

/-- The transcript point: every occurrence of a gate `u` is `b_u`, every input occurrence is its
encoded constant, the slacks are determined by the rows, and `p = n = 0`. -/
def transcript : ResPoint n where
  zocc v := b2r (C.tbit v)
  cocc v k := b2r (C.edgeBit (C.gtype v) (C.kid v k))
  slack v := 2 - (b2r (C.tbit v) + b2r (C.edgeBit (C.gtype v) (C.kid v 0)) +
    b2r (C.edgeBit (C.gtype v) (C.kid v 1)))
  surplus v k := b2r (C.tbit v) + b2r (C.edgeBit (C.gtype v) (C.kid v k)) - 1
  pos _ _ := 0
  neg _ _ := 0

variable {C}

lemma gate_of_isGate {v : Fin n} (hv : C.isGate v = true) :
    ∃ a c₁ c₂, C.node v = .gate a c₁ c₂ := by
  unfold isGate at hv; split at hv
  · rename_i a c₁ c₂ h; exact ⟨a, c₁, c₂, h⟩
  · simp at hv

lemma tbit_nand (hC : C.Alternating) {v : Fin n} (hv : C.isGate v = true) :
    C.tbit v = !(C.edgeBit (C.gtype v) (C.kid v 0) && C.edgeBit (C.gtype v) (C.kid v 1)) := by
  obtain ⟨a, c₁, c₂, h⟩ := gate_of_isGate hv
  have hg : C.gtype v = a := by unfold gtype; rw [h]
  have hk0 : C.kid v 0 = c₁ := by unfold kid; rw [h]; rfl
  have hk1 : C.kid v 1 = c₂ := by unfold kid; rw [h]; rfl
  rw [hg, hk0, hk1]; exact nand_normalization hC h

lemma b2r_cases (b : Bool) : b2r b = 0 ∨ b2r b = 1 := by cases b <;> simp [b2r]

lemma b2r_mem (b : Bool) : 0 ≤ b2r b ∧ b2r b ≤ 1 := by cases b <;> simp [b2r]

lemma nand_facts (x y : Bool) :
    (0 ≤ 2 - (b2r (!(x && y)) + b2r x + b2r y) ∧ 2 - (b2r (!(x && y)) + b2r x + b2r y) ≤ 2) ∧
    (0 ≤ b2r (!(x && y)) + b2r x - 1 ∧ b2r (!(x && y)) + b2r x - 1 ≤ 1) ∧
    (0 ≤ b2r (!(x && y)) + b2r y - 1 ∧ b2r (!(x && y)) + b2r y - 1 ≤ 1) := by
  cases x <;> cases y <;> simp [b2r] <;> norm_num

/-- **Theorem 4.2 (iv)–(v) (dyadic elimination).** For an alternating monotone circuit, the
residual NAND program has optimum value `0`, attained by the transcript point, and every optimal
(cost-`0`) feasible point coincides with the transcript point on all variables of the program; in
particular every occurrence of a gate `u` carries the transformed bit `b_u`. -/
theorem dyadic_elimination (hC : C.Alternating) :
    C.ResFeasible C.transcript ∧ C.resCost C.transcript = 0 ∧
    (∀ P, C.ResFeasible P → 0 ≤ C.resCost P) ∧
    ∀ P, C.ResFeasible P → C.resCost P = 0 → ∀ v, C.isGate v = true →
      P.zocc v = C.transcript.zocc v ∧ P.cocc v = C.transcript.cocc v ∧
      P.slack v = C.transcript.slack v ∧ P.surplus v = C.transcript.surplus v ∧
      ∀ k, C.isGate (C.kid v k) = true → P.pos v k = 0 ∧ P.neg v k = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the transcript is feasible
    intro v hv
    have hn := tbit_nand hC hv
    have hf := nand_facts (C.edgeBit (C.gtype v) (C.kid v 0)) (C.edgeBit (C.gtype v) (C.kid v 1))
    rw [← hn] at hf
    refine ⟨b2r_mem _, fun k => b2r_mem _, hf.1, ?_, ?_, ?_, ?_⟩
    · intro k; fin_cases k
      · exact hf.2.1
      · exact hf.2.2
    · simp only [transcript]; ring
    · intro k; simp only [transcript]; ring
    · intro k
      refine ⟨fun _ => rfl, fun hk => ?_⟩
      simp only [transcript, edgeBit_of_isGate _ hk]
      norm_num
  · simp [resCost, transcript]
  · intro P hP
    apply sum_nonneg; intro v _; apply sum_nonneg; intro k _
    split_ifs with h
    · have := ((hP v h.1).2.2.2.2.2.2 k).2 h.2
      linarith [this.1, this.2.2.1]
    · exact le_rfl
  · intro P hP hcost
    -- all disagreement variables vanish
    have hpn : ∀ v, C.isGate v = true → ∀ k, C.isGate (C.kid v k) = true →
        P.pos v k = 0 ∧ P.neg v k = 0 := by
      intro v hv k hk
      have hnn : ∀ v k, 0 ≤ (if C.isGate v = true ∧ C.isGate (C.kid v k) = true then
          P.pos v k + P.neg v k else 0) := by
        intro v k
        split_ifs with h
        · have := ((hP v h.1).2.2.2.2.2.2 k).2 h.2; linarith [this.1, this.2.2.1]
        · exact le_rfl
      have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun v _ =>
        Finset.sum_nonneg (fun k _ => hnn v k))).mp hcost v (mem_univ v)
      have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hnn v k)).mp h1 k (mem_univ k)
      rw [if_pos ⟨hv, hk⟩] at h2
      have := ((hP v hv).2.2.2.2.2.2 k).2 hk
      constructor <;> linarith [this.1, this.2.2.1]
    -- the occurrences of the children carry the encoded bits, and `z_v = b_v`
    have hz : ∀ m : ℕ, ∀ v : Fin n, v.val = m → C.isGate v = true →
        P.zocc v = b2r (C.tbit v) := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
      intro v hvm hv
      obtain ⟨a, c₁, c₂, hnode⟩ := gate_of_isGate hv
      have hkid : ∀ k, P.cocc v k = b2r (C.edgeBit (C.gtype v) (C.kid v k)) := by
        intro k
        cases hk : C.isGate (C.kid v k)
        · exact ((hP v hv).2.2.2.2.2.2 k).1 hk
        · have e := ((hP v hv).2.2.2.2.2.2 k).2 hk
          obtain ⟨hp, hn⟩ := hpn v hv k hk
          have hlt := kid_lt hnode k
          have := ih (C.kid v k).val (hvm ▸ hlt) (C.kid v k) rfl hk
          rw [edgeBit_of_isGate _ hk, ← this]
          linarith [e.2.2.2.2]
      obtain ⟨hz01, _, hs, hr, _, hrows, _⟩ := hP v hv
      rw [tbit_nand hC hv]
      apply forcing _ _ _ hz01.1 hz01.2
      · rw [← hkid 0]; linarith [hrows 0, (hr 0).1]
      · rw [← hkid 1]; linarith [hrows 1, (hr 1).1]
      · rw [← hkid 0, ← hkid 1]; linarith [hs.1, ‹P.zocc v + P.cocc v 0 + P.cocc v 1 + P.slack v = 2›]
    intro v hv
    have hz0 := hz v.val v rfl hv
    have hkid : ∀ k, P.cocc v k = b2r (C.edgeBit (C.gtype v) (C.kid v k)) := by
      intro k
      cases hk : C.isGate (C.kid v k)
      · exact ((hP v hv).2.2.2.2.2.2 k).1 hk
      · have e := ((hP v hv).2.2.2.2.2.2 k).2 hk
        obtain ⟨hp, hn⟩ := hpn v hv k hk
        have := hz _ (C.kid v k) rfl hk
        rw [edgeBit_of_isGate _ hk, ← this]
        linarith [e.2.2.2.2]
    obtain ⟨_, _, _, _, hrow, hrows, _⟩ := hP v hv
    refine ⟨hz0, funext hkid, ?_, ?_, hpn v hv⟩
    · simp only [transcript]; rw [← hz0, ← hkid 0, ← hkid 1]; linarith
    · funext k; simp only [transcript]; rw [← hz0, ← hkid k]; linarith [hrows k]


/-- **Theorem 5.1, the equal-flow form (logical content).** Replace the disagreement objective by
hard equality of all occurrences of each gate (`p = n = 0` on every tree edge). Then the feasible
point is unique: it is the transcript point; it is integral (every occurrence is `0` or `1`), and
the common value of the occurrences of a gate `u` (its own `z_u` and every `x_v`, `y_v` that uses
`u`) is the transformed bit `b_u`. -/
theorem equalFlow_unique (hC : C.Alternating) (P : ResPoint n) (hP : C.ResFeasible P)
    (heq : ∀ v, C.isGate v = true → ∀ k, C.isGate (C.kid v k) = true →
      P.pos v k = 0 ∧ P.neg v k = 0) :
    (∀ v, C.isGate v = true →
      P.zocc v = C.transcript.zocc v ∧ P.cocc v = C.transcript.cocc v ∧
      P.slack v = C.transcript.slack v ∧ P.surplus v = C.transcript.surplus v) ∧
    (∀ v, C.isGate v = true → (P.zocc v = 0 ∨ P.zocc v = 1) ∧ ∀ k, P.cocc v k = 0 ∨ P.cocc v k = 1) ∧
    (∀ u, C.isGate u = true → P.zocc u = b2r (C.tbit u) ∧
      ∀ v k, C.isGate v = true → C.kid v k = u → P.cocc v k = b2r (C.tbit u)) := by
  have hcost : C.resCost P = 0 := by
    apply Finset.sum_eq_zero; intro v _; apply Finset.sum_eq_zero; intro k _
    split_ifs with h
    · rw [(heq v h.1 k h.2).1, (heq v h.1 k h.2).2]; ring
    · rfl
  have hu := (dyadic_elimination hC).2.2.2 P hP hcost
  refine ⟨fun v hv => ⟨(hu v hv).1, (hu v hv).2.1, (hu v hv).2.2.1, (hu v hv).2.2.2.1⟩, ?_, ?_⟩
  · intro v hv
    obtain ⟨h1, h2, _⟩ := hu v hv
    refine ⟨?_, fun k => ?_⟩
    · rw [h1]; simp only [transcript]; exact b2r_cases _
    · rw [h2]; simp only [transcript]; exact b2r_cases _
  · intro u hu'
    refine ⟨by rw [(hu u hu').1]; rfl, fun v k hv hk => ?_⟩
    rw [(hu v hv).2.1]
    simp only [transcript]
    rw [hk, edgeBit_of_isGate _ (hk ▸ hu')]

end MonCircuit

/-! ### Proposition 6.1: the cut-size bound -/

/-- Weak max-flow/min-cut: the value of a flow from `s` to `t` (its net outflow at `s`) is at most
the capacity of every cut `S` with `s ∈ S`, `t ∉ S`. -/
theorem cut_bound {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V]
    (tail head : A → V) (cap f : A → ℤ) {s t : V} {S : Finset V} (hs : s ∈ S) (ht : t ∉ S)
    (hf : ∀ a, 0 ≤ f a ∧ f a ≤ cap a)
    (hcons : ∀ v, v ≠ s → v ≠ t → netOut tail head f v = 0) :
    netOut tail head f s ≤ ∑ a ∈ univ.filter (fun a => tail a ∈ S ∧ head a ∉ S), cap a := by
  have hsum : ∑ v ∈ S, netOut tail head f v = netOut tail head f s := by
    rw [Finset.sum_eq_single s]
    · intro v hv hvs; exact hcons v hvs (fun h => ht (h ▸ hv))
    · intro h; exact absurd hs h
  have hinc : ∀ a, ∑ v ∈ S, inc tail head a v =
      (if tail a ∈ S then 1 else 0) - (if head a ∈ S then 1 else 0) := by
    intro a
    simp [inc, Finset.sum_sub_distrib, Finset.sum_ite_eq]
  rw [← hsum]
  unfold netOut
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hinc]
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro a _
  have := hf a
  by_cases h1 : tail a ∈ S <;> by_cases h2 : head a ∈ S <;> simp [h1, h2] <;> omega

/-- **Proposition 6.1 (cut-size bound).** If a two-terminal network with arc capacities at most
`U` carries a flow of value at least `2^i`, every separating cut has at least `2^i / U` arcs, i.e.
`(#cut) * U ≥ 2^i`. -/
theorem cut_size_bound {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V]
    (tail head : A → V) (cap f : A → ℤ) {s t : V} {S : Finset V} (hs : s ∈ S) (ht : t ∉ S)
    (hf : ∀ a, 0 ≤ f a ∧ f a ≤ cap a)
    (hcons : ∀ v, v ≠ s → v ≠ t → netOut tail head f v = 0) (U : ℤ) (hU : ∀ a, cap a ≤ U)
    (i : ℕ) (hval : 2 ^ i ≤ netOut tail head f s) :
    2 ^ i ≤ ((univ.filter (fun a => tail a ∈ S ∧ head a ∉ S)).card : ℤ) * U := by
  have h1 := cut_bound tail head cap f hs ht hf hcons
  have h2 : ∑ a ∈ univ.filter (fun a => tail a ∈ S ∧ head a ∉ S), cap a ≤
      ∑ _a ∈ univ.filter (fun a => tail a ∈ S ∧ head a ∉ S), U := Finset.sum_le_sum (fun a _ => hU a)
  rw [Finset.sum_const, nsmul_eq_mul] at h2
  linarith

end GC.FlowCircuits
