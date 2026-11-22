import GC.Optimization.FlowCircuits.Carrier
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.ChainOfFn
import Mathlib.Logic.Relation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# Manuscript 003e: Circuit evaluation in depth governed by catalyst height

* `CarrierGraph.rounding`, `CarrierGraph.integrality_gap_two` : Theorem 5.2 (threshold rounding
  at `1/2`, `d* ≤ χ ≤ 2 d*`), and `tightGraph_*` : the factor two is attained.
* `CarrierGraph.weight_le_of_potentials` : Lemma 5.3, "if" direction (path potentials certify the
  path constraints).
* `compiler_round_functional`, `functional_rel_cover` : the combinatorial core of Theorem 3.2 and
  Theorem 2.4: in round `r` of the catalyst-height compiler, every node of the cone `C_r` has at
  most one predecessor whose value is not yet known.
* `CarrierGraph.heightLE_one_of_sources` : a cover consisting of sources has height one
  (the batch-side accumulator, Theorem 4.1).
* `twoRegister_height` : Example 4.2 (every catalyst cover of the two-register recurrence of
  length `m` has height at least `m`).
-/

namespace GC.FlowCircuits

open Finset

namespace CarrierGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : CarrierGraph V)

/-- The threshold set `{v : x_v ≥ 1/2}`. -/
noncomputable def threshold (x : V → ℝ) : Finset V := by
  classical
  exact univ.filter (fun v => 1 / 2 ≤ x v)

lemma mem_threshold {x : V → ℝ} {v : V} : v ∈ threshold x ↔ 1 / 2 ≤ x v := by
  classical
  unfold threshold
  simp

variable {G}

/-- **Theorem 5.2 (factor-two rounding).** If `(x, d)` is fractionally feasible, then
`H = {v : x_v ≥ 1/2}` is a catalyst cover and every directed path contains at most `2d` of its
nodes. -/
theorem rounding {x : V → ℝ} {d : ℝ} (hx : G.FracFeasible x d) :
    G.IsCatalystCover (threshold x) ∧
      ∀ P, G.IsPath P → (coverCount (threshold x) P : ℝ) ≤ 2 * d := by
  obtain ⟨hb, hf, hp⟩ := hx
  constructor
  · intro e he
    have := hf e he
    by_contra hcon
    push_neg at hcon
    rw [mem_threshold, mem_threshold] at hcon
    linarith [hcon.1, hcon.2]
  · intro P hP
    have hw := hp P hP
    unfold coverCount
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    calc (∑ v ∈ P.toFinset.filter (· ∈ threshold x), ((1 : ℕ) : ℝ))
        ≤ ∑ v ∈ P.toFinset.filter (· ∈ threshold x), 2 * x v := by
          apply Finset.sum_le_sum
          intro v hv
          rw [Finset.mem_filter, mem_threshold] at hv
          push_cast; linarith [hv.2]
      _ ≤ ∑ v ∈ P.toFinset, 2 * x v := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro v _ _; linarith [(hb v).1]
      _ = 2 * weight x P := by rw [weight, Finset.mul_sum]
      _ ≤ 2 * d := by linarith

/-- A catalyst cover `H` of height at most `k` gives the fractionally feasible pair
`(1_H, k)`. -/
theorem cover_fracFeasible {H : Finset V} {k : ℕ} (hH : G.IsCatalystCover H)
    (hk : G.HeightLE H k) :
    G.FracFeasible (fun v => if v ∈ H then 1 else 0) k := by
  refine ⟨fun v => by dsimp only; split_ifs <;> norm_num, ?_, ?_⟩
  · intro e he
    rcases hH e he with h | h
    · have : (0 : ℝ) ≤ if e.2 ∈ H then 1 else 0 := by split_ifs <;> norm_num
      simp [h]; linarith
    · have : (0 : ℝ) ≤ if e.1 ∈ H then 1 else 0 := by split_ifs <;> norm_num
      simp [h]; linarith
  · intro P hP
    have := hk P hP
    unfold weight
    rw [Finset.sum_boole]
    unfold coverCount at this
    exact_mod_cast this

/-- **Theorem 5.2 (`d* ≤ χ ≤ 2 d*`).** A catalyst cover of height `≤ k` gives a fractional
certificate of value `k`, and a fractional certificate of value `d` rounds to a catalyst cover
meeting every path in at most `2d` nodes. -/
theorem integrality_gap_two :
    (∀ (H : Finset V) (k : ℕ), G.IsCatalystCover H → G.HeightLE H k →
      ∃ x : V → ℝ, G.FracFeasible x k) ∧
    (∀ (x : V → ℝ) (d : ℝ), G.FracFeasible x d →
      ∃ H, G.IsCatalystCover H ∧ ∀ P, G.IsPath P → (coverCount H P : ℝ) ≤ 2 * d) :=
  ⟨fun _ _ hH hk => ⟨_, cover_fracFeasible hH hk⟩,
   fun _ _ hx => ⟨_, (rounding hx).1, (rounding hx).2⟩⟩

lemma weight_cons_le (x : V → ℝ) (hx : ∀ v, 0 ≤ x v) (a : V) (l : List V) :
    weight x (a :: l) ≤ x a + weight x l := by
  unfold weight
  rw [List.toFinset_cons]
  by_cases ha : a ∈ l.toFinset
  · rw [Finset.insert_eq_of_mem ha]; linarith [hx a]
  · rw [Finset.sum_insert ha]

lemma weight_le_sum (x : V → ℝ) (hx : ∀ v, 0 ≤ x v) :
    ∀ l : List V, weight x l ≤ (l.map x).sum
  | [] => by simp [weight]
  | a :: l => by
    have := weight_le_sum x hx l
    have := weight_cons_le x hx a l
    simp only [List.map_cons, List.sum_cons]
    linarith

lemma chain_sum_le (x p : V → ℝ) (hp : ∀ u v, G.arc u v → p u + x v ≤ p v) :
    ∀ (l : List V) (a : V) (c : ℝ), (a :: l).IsChain G.arc → c + x a ≤ p a →
      ∃ w, c + ((a :: l).map x).sum ≤ p w
  | [], a, c, _, h => ⟨a, by simpa using h⟩
  | b :: l, a, c, hch, h => by
    rw [List.isChain_cons_cons] at hch
    obtain ⟨w, hw⟩ := chain_sum_le x p hp l b (c + x a) hch.2 (by linarith [hp a b hch.1])
    exact ⟨w, by simp only [List.map_cons, List.sum_cons] at hw ⊢; linarith⟩

/-- **Lemma 5.3 (path potentials), "if" direction.** If `x ≥ 0` and numbers `p_v` satisfy
`p_v ≥ x_v`, `p_v ≥ p_u + x_v` for every arc `u → v`, and `p_v ≤ d`, then every directed path has
`x`-weight at most `d`. -/
theorem weight_le_of_potentials (x p : V → ℝ) (d : ℝ) (hx : ∀ v, 0 ≤ x v)
    (h1 : ∀ v, x v ≤ p v) (h2 : ∀ u v, G.arc u v → p u + x v ≤ p v) (h3 : ∀ v, p v ≤ d) :
    ∀ P, G.IsPath P → weight x P ≤ d := by
  rintro (_ | ⟨a, l⟩) ⟨hne, hch⟩
  · exact absurd rfl hne
  obtain ⟨w, hw⟩ := chain_sum_le x p h2 l a 0 hch (by linarith [h1 a])
  linarith [weight_le_sum x hx (a :: l), h3 w]

lemma exists_pred_of_mem_tail {R : V → V → Prop} :
    ∀ (l : List V) (a : V), (a :: l).IsChain R → ∀ w ∈ l, ∃ u, R u w
  | [], _, _, w, hw => by simp at hw
  | b :: l, a, hch, w, hw => by
    rw [List.isChain_cons_cons] at hch
    rcases List.mem_cons.mp hw with rfl | hw
    · exact ⟨a, hch.1⟩
    · exact exists_pred_of_mem_tail l b hch.2 w hw

/-- **Batch-side accumulator (Theorem 4.1).** A catalyst cover consisting of sources (nodes without
incoming arcs) has height at most one. -/
theorem heightLE_one_of_sources (H : Finset V) (hsrc : ∀ h ∈ H, ∀ u, ¬ G.arc u h) :
    G.HeightLE H 1 := by
  rintro (_ | ⟨a, l⟩) ⟨hne, hch⟩
  · exact absurd rfl hne
  unfold coverCount
  calc ((a :: l).toFinset.filter (· ∈ H)).card ≤ ({a} : Finset V).card := by
        apply Finset.card_le_card
        intro w hw
        rw [Finset.mem_filter, List.mem_toFinset] at hw
        rcases List.mem_cons.mp hw.1 with rfl | hwl
        · simp
        · obtain ⟨u, hu⟩ := exists_pred_of_mem_tail l a hch w hwl
          exact absurd hu (hsrc w hw.2 u)
    _ = 1 := Finset.card_singleton a

end CarrierGraph

/-! ### Tightness of the factor two -/

/-- One fusion `v = ψ(u, w)` of two sources `u = 0`, `w = 1`, with `v = 2`. -/
def tightGraph : CarrierGraph (Fin 3) where
  arc u v := (u = 0 ∨ u = 1) ∧ v = 2
  fusion := {(0, 1)}

lemma tightGraph_path (P : List (Fin 3)) (hP : tightGraph.IsPath P) :
    ∃ a, P = [a] ∨ (P = [a, 2] ∧ (a = 0 ∨ a = 1)) := by
  obtain ⟨hne, hch⟩ := hP
  rcases P with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · exact absurd rfl hne
  · exact ⟨a, Or.inl rfl⟩
  · rw [List.isChain_cons_cons] at hch
    obtain ⟨⟨ha, rfl⟩, _⟩ := hch
    exact ⟨a, Or.inr ⟨rfl, ha⟩⟩
  · rw [List.isChain_cons_cons, List.isChain_cons_cons] at hch
    obtain ⟨⟨_, rfl⟩, ⟨h2, _⟩, _⟩ := hch
    rcases h2 with h2 | h2 <;> exact absurd h2 (by decide)

/-- **Tightness in Theorem 5.2.** For one fusion of two sources, `d* = 1/2` while the least
catalyst height is `χ = 1`. -/
theorem tightGraph_gap :
    tightGraph.FracFeasible ![1 / 2, 1 / 2, 0] (1 / 2) ∧
    (∀ x d, tightGraph.FracFeasible x d → 1 / 2 ≤ d) ∧
    (tightGraph.IsCatalystCover {0} ∧ tightGraph.HeightLE {0} 1) ∧
    (∀ H, tightGraph.IsCatalystCover H → ¬ tightGraph.HeightLE H 0) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ⟨?_, ?_⟩, ?_⟩
  · intro v; fin_cases v <;> simp <;> norm_num
  · intro e he; simp [tightGraph] at he; subst he; simp; norm_num
  · intro P hP
    obtain ⟨a, rfl | ⟨rfl, ha⟩⟩ := tightGraph_path P hP
    · fin_cases a <;> simp [CarrierGraph.weight] <;> norm_num
    · rcases ha with rfl | rfl <;> simp [CarrierGraph.weight] <;> norm_num
  · rintro x d ⟨_, hf, hp⟩
    have h0 := hp [0] ⟨by simp, List.isChain_singleton _⟩
    have h1 := hp [1] ⟨by simp, List.isChain_singleton _⟩
    have := hf (0, 1) (by simp [tightGraph])
    simp [CarrierGraph.weight] at h0 h1 this
    linarith
  · intro e he; simp [tightGraph] at he; subst he; simp
  · intro P _
    unfold CarrierGraph.coverCount
    calc (P.toFinset.filter (· ∈ ({0} : Finset (Fin 3)))).card
        ≤ ({0} : Finset (Fin 3)).card := Finset.card_le_card (fun w hw => (Finset.mem_filter.mp hw).2)
      _ = 1 := rfl
  · intro H hH hk
    rcases hH (0, 1) (by simp [tightGraph]) with h | h
    · have := hk [0] ⟨by simp, List.isChain_singleton _⟩
      simp [CarrierGraph.coverCount, h] at this
    · have := hk [1] ⟨by simp, List.isChain_singleton _⟩
      simp [CarrierGraph.coverCount, h] at this

/-! ### The catalyst-height compiler: one round is functional -/

section Compiler

variable {V : Type*} (par : V → Finset V)

/-- Parent relation `u → v` (`u` is a predecessor of `v`). -/
def ParRel (u v : V) : Prop := u ∈ par v

/-- The closed ancestor cone `C_r` of the cover nodes of level `r`. -/
def InCone (H : Finset V) (ℓ : V → ℕ) (r : ℕ) (v : V) : Prop :=
  ∃ h ∈ H, ℓ h = r ∧ Relation.ReflTransGen (ParRel par) v h

/-- Nodes known before round `r`: the sources and the cones `C_s`, `s < r`. -/
def KnownBefore (H : Finset V) (ℓ : V → ℕ) (r : ℕ) (v : V) : Prop :=
  par v = ∅ ∨ ∃ s < r, InCone par H ℓ s v

/-- **Theorem 3.2, combinatorial core.** Let every node have at most two predecessors, let `H` be
a catalyst cover (every node with two predecessors has one in `H`), and let `ℓ` be a grading of
`H` that strictly increases along proper ancestry inside `H` (for instance the levels `ℓ_H`, whose
maximum is `cht(H)`). Then in round `r` every node of the cone `C_r` has at most one predecessor
that is not known before round `r`; that is, `C_r` is functional relative to the known nodes, so
`cht(H)` rounds of functional closure (plus one final round, `functional_rel_cover`) evaluate the
circuit. -/
theorem compiler_round_functional (hdeg : ∀ v, (par v).card ≤ 2) (H : Finset V)
    (hH : ∀ v, (par v).card = 2 → ∃ u ∈ par v, u ∈ H) (ℓ : V → ℕ)
    (hℓ : ∀ h ∈ H, ∀ h' ∈ H, Relation.TransGen (ParRel par) h' h → ℓ h' < ℓ h)
    (r : ℕ) (v : V) (hv : InCone par H ℓ r v) :
    ∀ u₁ ∈ par v, ∀ u₂ ∈ par v, ¬ KnownBefore par H ℓ r u₁ → ¬ KnownBefore par H ℓ r u₂ →
      u₁ = u₂ := by
  classical
  intro u₁ h₁ u₂ h₂ hk₁ hk₂
  rcases Nat.lt_or_ge (par v).card 2 with hc | hc
  · exact Finset.card_le_one.mp (by omega) u₁ h₁ u₂ h₂
  · have hc2 : (par v).card = 2 := le_antisymm (hdeg v) hc
    obtain ⟨u, hu, huH⟩ := hH v hc2
    obtain ⟨h, hh, hℓh, hvh⟩ := hv
    -- the cover parent `u` is a proper ancestor of `h`, hence of lower level, hence known
    have hlt : ℓ u < r := by
      rw [← hℓh]
      exact hℓ h hh u huH (Relation.TransGen.head' hu hvh)
    have hu_known : KnownBefore par H ℓ r u :=
      Or.inr ⟨ℓ u, hlt, u, huH, rfl, Relation.ReflTransGen.refl⟩
    have hne₁ : u₁ ≠ u := fun e => hk₁ (e ▸ hu_known)
    have hne₂ : u₂ ≠ u := fun e => hk₂ (e ▸ hu_known)
    have hcard : ((par v).erase u).card = 1 := by rw [Finset.card_erase_of_mem hu, hc2]
    exact Finset.card_le_one.mp hcard.le u₁ (Finset.mem_erase.mpr ⟨hne₁, h₁⟩)
      u₂ (Finset.mem_erase.mpr ⟨hne₂, h₂⟩)

/-- **Theorem 2.4 (joint catalyst composition), combinatorial core.** Relative to a catalyst
cover `H`, every node has at most one predecessor outside `H`. -/
theorem functional_rel_cover (hdeg : ∀ v, (par v).card ≤ 2) (H : Finset V)
    (hH : ∀ v, (par v).card = 2 → ∃ u ∈ par v, u ∈ H) (v : V) :
    ∀ u₁ ∈ par v, ∀ u₂ ∈ par v, u₁ ∉ H → u₂ ∉ H → u₁ = u₂ := by
  classical
  intro u₁ h₁ u₂ h₂ hk₁ hk₂
  rcases Nat.lt_or_ge (par v).card 2 with hc | hc
  · exact Finset.card_le_one.mp (by omega) u₁ h₁ u₂ h₂
  · have hc2 : (par v).card = 2 := le_antisymm (hdeg v) hc
    obtain ⟨u, hu, huH⟩ := hH v hc2
    have hcard : ((par v).erase u).card = 1 := by rw [Finset.card_erase_of_mem hu, hc2]
    exact Finset.card_le_one.mp hcard.le u₁ (Finset.mem_erase.mpr ⟨fun e => hk₁ (e ▸ huH), h₁⟩)
      u₂ (Finset.mem_erase.mpr ⟨fun e => hk₂ (e ▸ huH), h₂⟩)

/-- Every cover node `h` lies in the cone `C_{ℓ h}`, so after the last round all of `H` is
known. -/
lemma mem_cone_self (H : Finset V) (ℓ : V → ℕ) {h : V} (hh : h ∈ H) :
    InCone par H ℓ (ℓ h) h :=
  ⟨h, hh, rfl, Relation.ReflTransGen.refl⟩

end Compiler

/-! ### Example 4.2: the two-register recurrence -/

/-- The two-register recurrence `a_t = ψ_t(a_{t-1}, b_{t-1})`, `b_t = ψ'_t(a_{t-1}, b_{t-1})`,
`1 ≤ t ≤ m`: vertices `(t, false) = a_t`, `(t, true) = b_t`; both registers of level `t` are
predecessors of both registers of level `t + 1`; the fusion pairs are `{a_t, b_t}`, `t < m`. -/
def twoRegister (m : ℕ) : CarrierGraph (Fin (m + 1) × Bool) where
  arc u v := v.1.val = u.1.val + 1
  fusion := (univ.filter (fun t : Fin (m + 1) => t.val < m)).image (fun t => ((t, false), (t, true)))

/-- **Example 4.2.** Every catalyst cover of the two-register recurrence of length `m ≥ 1` has a
directed path containing `m` of its nodes, so its height is at least `m`. -/
theorem twoRegister_height (m : ℕ) (hm : 1 ≤ m) (H : Finset (Fin (m + 1) × Bool))
    (hH : (twoRegister m).IsCatalystCover H) :
    ∃ P, (twoRegister m).IsPath P ∧ m ≤ CarrierGraph.coverCount H P := by
  classical
  let c : Fin m → Fin (m + 1) × Bool := fun t =>
    if (Fin.castSucc t, false) ∈ H then (Fin.castSucc t, false) else (Fin.castSucc t, true)
  have hcH : ∀ t, c t ∈ H := by
    intro t
    have := hH ((Fin.castSucc t, false), (Fin.castSucc t, true))
      (by simp [twoRegister])
    simp only [c]; split_ifs with h
    · exact h
    · rcases this with h' | h'
      · exact absurd h' h
      · exact h'
  have hc1 : ∀ t, (c t).1 = Fin.castSucc t := by intro t; simp only [c]; split_ifs <;> rfl
  have hinj : Function.Injective c := by
    intro s t hst
    have := congrArg Prod.fst hst
    rw [hc1, hc1] at this
    exact Fin.castSucc_injective _ this
  refine ⟨List.ofFn c, ⟨?_, ?_⟩, ?_⟩
  · simp; omega
  · rw [List.isChain_ofFn]
    intro i hi
    simp only [twoRegister, hc1, Fin.coe_castSucc]
  · unfold CarrierGraph.coverCount
    have hfil : (List.ofFn c).toFinset.filter (· ∈ H) = (List.ofFn c).toFinset := by
      apply Finset.filter_true_of_mem
      intro w hw
      rw [List.mem_toFinset, List.mem_ofFn] at hw
      obtain ⟨t, rfl⟩ := hw
      exact hcH t
    rw [hfil, List.toFinset_card_of_nodup (List.nodup_ofFn.mpr hinj), List.length_ofFn]

end GC.FlowCircuits
