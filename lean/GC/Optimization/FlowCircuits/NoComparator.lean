import GC.Optimization.FlowCircuits.Basic
import Mathlib.Algebra.Order.Ring.WithTop
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Lattice
import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.Order.AbsoluteValue.Basic

/-!
# Manuscript 003a: Min-cost flow has no read-only comparator

* `Network.boundary` is the boundary function `Φ_G(b)` of an open network (Section 2): the least
  cost of an integral flow within the bounds whose net outflow is `b` on the terminals and the
  fixed internal excess `d` on the internal vertices, and `⊤` if there is none.
* `Network.flow_exchange` and `Network.boundary_isMConvex` : Theorem 3.1 (boundary exchange):
  `Φ_G` satisfies the exchange axiom, i.e. it is M-convex.
* `Network.no_allEqualSensor` : Corollary 4.4 (no all-equal sensor on `r ≥ 2` channels).
* `Network.no_readOnlyComparator` : Theorem 4.3 (no read-only comparator).
* `crossbar_table` : Remark 4.6, condition (ii) cannot be dropped.
* `oneShot_isLeast` : Proposition 4.1 (one-shot comparator).
* `no_submodular_nand`, `no_submodular_nand_any_polarity` : Theorem 5.2 and the remark after it.
-/

namespace GC.FlowCircuits

open Finset

/-- An open network: arcs `A` between vertices `T ⊕ I` (terminals `T`, internal vertices `I`),
with integral lower and upper bounds and costs on the arcs, and a fixed integral excess on every
internal vertex. Costs may be negative and lower bounds nonzero. -/
structure Network (T I A : Type*) where
  tail : A → T ⊕ I
  head : A → T ⊕ I
  lower : A → ℤ
  upper : A → ℤ
  cost : A → ℤ
  supply : I → ℤ

namespace Network

variable {T I A : Type*} [Fintype A] [DecidableEq T] [DecidableEq I]

/-- `f` is a feasible integral flow with boundary `b`: bounds hold, net outflow is `b` at the
terminals and the fixed excess at internal vertices. -/
def Feasible (N : Network T I A) (b : T → ℤ) (f : A → ℤ) : Prop :=
  (∀ a, N.lower a ≤ f a ∧ f a ≤ N.upper a) ∧
    ∀ v, netOut N.tail N.head f v = Sum.elim b N.supply v

/-- Cost `c^T f` of a flow. -/
def flowCost (N : Network T I A) (f : A → ℤ) : ℤ := ∑ a, N.cost a * f a

/-- The (finite) set of feasible integral flows with boundary `b`. -/
noncomputable def feasibleSet [DecidableEq A] (N : Network T I A) (b : T → ℤ) :
    Finset (A → ℤ) := by
  classical
  exact (Fintype.piFinset fun a => Finset.Icc (N.lower a) (N.upper a)).filter (N.Feasible b)

/-- The boundary function `Φ_G(b)`: least cost of a feasible flow with boundary `b`,
or `⊤` if there is none. -/
noncomputable def boundary [DecidableEq A] (N : Network T I A) (b : T → ℤ) : WithTop ℤ :=
  ((N.feasibleSet b).image N.flowCost).min

variable [DecidableEq A] (N : Network T I A)

lemma mem_feasibleSet {b : T → ℤ} {f : A → ℤ} : f ∈ N.feasibleSet b ↔ N.Feasible b f := by
  classical
  unfold feasibleSet
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨fun a => Finset.mem_Icc.mpr (h.1 a), h⟩

lemma boundary_le {b : T → ℤ} {f : A → ℤ} (hf : N.Feasible b f) :
    N.boundary b ≤ N.flowCost f :=
  Finset.min_le (Finset.mem_image_of_mem _ ((N.mem_feasibleSet).mpr hf))

lemma exists_of_boundary_ne_top {b : T → ℤ} (h : N.boundary b ≠ ⊤) :
    ∃ f, N.Feasible b f ∧ N.boundary b = N.flowCost f := by
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp h
  have hmem := Finset.mem_of_min hm.symm
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hmem
  exact ⟨f, (N.mem_feasibleSet).mp hf, hm.symm⟩

lemma boundary_eq_of {b : T → ℤ} {f : A → ℤ} {c : ℤ} (hf : N.Feasible b f)
    (hc : N.flowCost f = c) (hlow : ∀ g, N.Feasible b g → c ≤ N.flowCost g) :
    N.boundary b = c := by
  apply le_antisymm
  · rw [← hc]; exact N.boundary_le hf
  · apply Finset.le_min
    intro m hm
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hm
    exact WithTop.coe_le_coe.mpr (hlow g ((N.mem_feasibleSet).mp hg))

/-- **Flow exchange** (the flow-level content of Theorem 3.1). For feasible flows `f`, `g` with
boundaries `b`, `b'` and a terminal `i` with `b' i < b i`, there is a terminal `j` with
`b j < b' j` and feasible flows with the exchanged boundaries `b - e_i + e_j` and
`b' + e_i - e_j` whose total cost equals that of `f` and `g`. -/
theorem flow_exchange {b b' : T → ℤ} {f g : A → ℤ} (hf : N.Feasible b f) (hg : N.Feasible b' g)
    {i : T} (hi : b' i < b i) :
    ∃ j, b j < b' j ∧ ∃ f' g', N.Feasible (b - Pi.single i 1 + Pi.single j 1) f' ∧
      N.Feasible (b' + Pi.single i 1 - Pi.single j 1) g' ∧
      N.flowCost f' + N.flowCost g' = N.flowCost f + N.flowCost g := by
  have hdiff : ∀ v, netOut N.tail N.head (f - g) v =
      Sum.elim b N.supply v - Sum.elim b' N.supply v := by
    intro v; rw [netOut_sub, hf.2 v, hg.2 v]
  have hpos : 0 < netOut N.tail N.head (f - g) (Sum.inl i) := by
    rw [hdiff]; simp; omega
  obtain ⟨χ, k, hconf, hk, hχ⟩ := exists_conformal_path N.tail N.head (f - g) (Sum.inl i) hpos
  rcases k with j | x
  swap
  · rw [hdiff] at hk; simp at hk
  rw [hdiff] at hk
  simp only [Sum.elim_inl] at hk
  refine ⟨j, by omega, f - χ, g + χ, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · intro a
    have := hconf a; have := hf.1 a; have := hg.1 a
    simp only [Pi.sub_apply] at *
    omega
  · intro v
    rw [netOut_sub, hf.2 v, hχ v]
    rcases v with t | x
    · simp only [Sum.elim_inl, Pi.sub_apply, Pi.add_apply, Pi.single_apply, Sum.inl.injEq]; ring
    · simp
  · intro a
    have := hconf a; have := hf.1 a; have := hg.1 a
    simp only [Pi.sub_apply, Pi.add_apply] at *
    omega
  · intro v
    rw [netOut_add, hg.2 v, hχ v]
    rcases v with t | x
    · simp only [Sum.elim_inl, Pi.sub_apply, Pi.add_apply, Pi.single_apply, Sum.inl.injEq]; ring
    · simp
  · simp only [flowCost, Pi.sub_apply, Pi.add_apply, mul_sub, mul_add, sum_sub_distrib,
      sum_add_distrib]
    ring

/-- **Boundary exchange** (Theorem 3.1). For `b, b' ∈ dom Φ_G` and `i` with `b' i < b i` there is
`j` with `b j < b' j` and `Φ(b) + Φ(b') ≥ Φ(b - e_i + e_j) + Φ(b' + e_i - e_j)`. -/
theorem boundary_exchange {b b' : T → ℤ} (hb : N.boundary b ≠ ⊤) (hb' : N.boundary b' ≠ ⊤)
    {i : T} (hi : b' i < b i) :
    ∃ j, b j < b' j ∧
      N.boundary (b - Pi.single i 1 + Pi.single j 1) +
        N.boundary (b' + Pi.single i 1 - Pi.single j 1) ≤ N.boundary b + N.boundary b' := by
  obtain ⟨f, hf, hfb⟩ := N.exists_of_boundary_ne_top hb
  obtain ⟨g, hg, hgb⟩ := N.exists_of_boundary_ne_top hb'
  obtain ⟨j, hj, f', g', hf', hg', hcost⟩ := N.flow_exchange hf hg hi
  refine ⟨j, hj, ?_⟩
  rw [hfb, hgb]
  calc N.boundary (b - Pi.single i 1 + Pi.single j 1) +
        N.boundary (b' + Pi.single i 1 - Pi.single j 1)
      ≤ (N.flowCost f' : WithTop ℤ) + N.flowCost g' := add_le_add (N.boundary_le hf') (N.boundary_le hg')
    _ = (N.flowCost f : WithTop ℤ) + N.flowCost g := by
        rw [← WithTop.coe_add, ← WithTop.coe_add, hcost]

end Network

/-- M-convexity (Murota): nonempty domain and the exchange axiom (2.2). -/
def IsMConvex {T : Type*} [DecidableEq T] (Φ : (T → ℤ) → WithTop ℤ) : Prop :=
  (∃ b, Φ b ≠ ⊤) ∧
    ∀ b b' : T → ℤ, Φ b ≠ ⊤ → Φ b' ≠ ⊤ → ∀ i, b' i < b i →
      ∃ j, b j < b' j ∧
        Φ (b - Pi.single i 1 + Pi.single j 1) + Φ (b' + Pi.single i 1 - Pi.single j 1) ≤
          Φ b + Φ b'

/-- **Theorem 3.1.** The boundary function of every network with nonempty domain is M-convex. -/
theorem Network.boundary_isMConvex {T I A : Type*} [Fintype A] [DecidableEq T] [DecidableEq I]
    [DecidableEq A] (N : Network T I A) (hdom : ∃ b, N.boundary b ≠ ⊤) :
    IsMConvex N.boundary :=
  ⟨hdom, fun _ _ hb hb' _ hi => N.boundary_exchange hb hb' hi⟩

/-! ### Pass-through gadgets -/

/-- Intended boundary state `β_S = ∑_{k ∈ S} (e_{X_k^in} - e_{X_k^out})` of a gadget whose
terminals are `Sum.inl k = X_k^in` and `Sum.inr k = X_k^out`. -/
def intended {K : Type*} [DecidableEq K] (S : Finset K) : K ⊕ K → ℤ :=
  Sum.elim (fun k => if k ∈ S then 1 else 0) (fun k => if k ∈ S then -1 else 0)

/-- Definition 4.2: `N` is a pass-through gadget with cost table `τ` if, for a constant `c`,
(i) `Φ(β_S) = c + τ(S)` for every `S`, and (ii) `Φ(b) > c` for every boundary `b` that is not an
intended state. (The normalization `τ ≥ 0`, `min τ = 0` of the paper is not needed below.) -/
def IsPassThrough {K I A : Type*} [Fintype A] [DecidableEq K] [DecidableEq I] [DecidableEq A]
    (N : Network (K ⊕ K) I A) (τ : Finset K → ℤ) : Prop :=
  ∃ c : ℤ, (∀ S, N.boundary (intended S) = ((c + τ S : ℤ) : WithTop ℤ)) ∧
    ∀ b : K ⊕ K → ℤ, (∀ S, b ≠ intended S) → ((c : ℤ) : WithTop ℤ) < N.boundary b

/-- The read-only comparator table `τ(x, y) = |x - y|` on two channels. -/
def comparatorTable (S : Finset (Fin 2)) : ℤ :=
  |(if (0 : Fin 2) ∈ S then 1 else 0) - (if (1 : Fin 2) ∈ S then 1 else 0)|

lemma lt_add_of_lt_of_lt {c : ℤ} {x y : WithTop ℤ} (hx : (c : WithTop ℤ) < x)
    (hy : (c : WithTop ℤ) < y) : ((c + c : ℤ) : WithTop ℤ) < x + y := by
  induction x using WithTop.recTopCoe with
  | top => simp
  | coe x =>
    induction y using WithTop.recTopCoe with
    | top => simp
    | coe y =>
      rw [← WithTop.coe_add, WithTop.coe_lt_coe]
      rw [WithTop.coe_lt_coe] at hx hy
      omega

/-- **Corollary 4.4 (no all-equal sensor).** Let `K` have at least two channels. No network is a
pass-through gadget whose table vanishes at `∅` and at the full set and is positive on every proper
nonempty set of channels. -/
theorem Network.no_allEqualSensor {K I A : Type*} [Fintype K] [DecidableEq K] [Nontrivial K]
    [Fintype A] [DecidableEq I] [DecidableEq A] (N : Network (K ⊕ K) I A) (τ : Finset K → ℤ)
    (h0 : τ ∅ = 0) (huniv : τ univ = 0)
    (hpos : ∀ S : Finset K, S.Nonempty → S ≠ univ → 0 < τ S) :
    ¬ IsPassThrough N τ := by
  rintro ⟨c, hc, hother⟩
  obtain ⟨k₁⟩ : Nonempty K := inferInstance
  obtain ⟨k₂, hk₂⟩ := exists_ne k₁
  have hb : N.boundary (intended univ) ≠ ⊤ := by rw [hc]; simp
  have hb' : N.boundary (intended ∅) ≠ ⊤ := by rw [hc]; simp
  have hi : intended (∅ : Finset K) (Sum.inl k₁) < intended univ (Sum.inl k₁) := by
    simp [intended]
  obtain ⟨j, hj, hle⟩ := N.boundary_exchange hb hb' hi
  rw [hc, hc, h0, huniv, add_zero, ← WithTop.coe_add] at hle
  -- every term on the left exceeds `c`
  have hgt : ∀ S : Finset K, S.Nonempty → S ≠ univ →
      ((c : ℤ) : WithTop ℤ) < N.boundary (intended S) := by
    intro S hne hnu; rw [hc]; exact WithTop.coe_lt_coe.mpr (by linarith [hpos S hne hnu])
  rcases j with k | k
  · simp [intended] at hj
  by_cases hk : k = k₁
  · subst hk
    have e1 : intended univ - Pi.single (Sum.inl k) 1 + Pi.single (Sum.inr k) 1 =
        intended (univ.erase k) := by
      funext v; rcases v with t | t <;> by_cases ht : t = k <;> simp [intended, Pi.single_apply, ht]
    have e2 : intended ∅ + Pi.single (Sum.inl k) 1 - Pi.single (Sum.inr k) 1 =
        intended {k} := by
      funext v; rcases v with t | t <;> by_cases ht : t = k <;> simp [intended, Pi.single_apply, ht]
    rw [e1, e2] at hle
    have h1 := hgt (univ.erase k) ⟨k₂, by simp [hk₂]⟩ (by
      intro h; have := h ▸ (mem_univ k); simp at this)
    have h2 := hgt {k} (by simp) (by
      intro h; have := h ▸ (mem_univ k₂); simp [hk₂] at this)
    exact absurd hle (not_le.mpr (lt_add_of_lt_of_lt h1 h2))
  · -- crossed states: neither exchanged vector is intended
    have n1 : ∀ S, intended univ - Pi.single (Sum.inl k₁) 1 + Pi.single (Sum.inr k) 1 ≠
        intended S := by
      intro S h
      have a1 := congrFun h (Sum.inl k₁)
      have a2 := congrFun h (Sum.inr k₁)
      simp [intended, Pi.single_apply, Ne.symm hk] at a1 a2
      by_cases hS : k₁ ∈ S <;> simp [hS] at a1 a2
    have n2 : ∀ S, intended ∅ + Pi.single (Sum.inl k₁) 1 - Pi.single (Sum.inr k) 1 ≠
        intended S := by
      intro S h
      have a1 := congrFun h (Sum.inl k₁)
      have a2 := congrFun h (Sum.inr k₁)
      simp [intended, Pi.single_apply, Ne.symm hk] at a1 a2
      by_cases hS : k₁ ∈ S <;> simp [hS] at a1 a2
    exact absurd hle (not_le.mpr (lt_add_of_lt_of_lt (hother _ n1) (hother _ n2)))

/-- **Theorem 4.3 (no read-only comparator).** No network, of any size and with arbitrary integral
bounds, internal supplies and costs, is a pass-through gadget on two channels with cost table
`|x - y|`. -/
theorem Network.no_readOnlyComparator {I A : Type*} [Fintype A] [DecidableEq I] [DecidableEq A]
    (N : Network (Fin 2 ⊕ Fin 2) I A) : ¬ IsPassThrough N comparatorTable :=
  N.no_allEqualSensor comparatorTable (by decide) (by decide) (by
    have hS : ∀ S : Finset (Fin 2), S = ∅ ∨ S = {0} ∨ S = {1} ∨ S = univ := by decide
    intro S hne hnu
    rcases hS S with rfl | rfl | rfl | rfl
    · simp at hne
    · decide
    · decide
    · exact absurd rfl hnu)

/-! ### Remark 4.6: the crossbar -/

/-- The four-arc crossbar: arcs `X_in → X_out`, `Y_in → Y_out` of cost `1` and the crossing arcs
`X_in → Y_out`, `Y_in → X_out` of cost `0`, all with bounds `[0, 1]`, no internal vertices. -/
def crossbar : Network (Fin 2 ⊕ Fin 2) Empty (Fin 4) where
  tail := ![Sum.inl (Sum.inl 0), Sum.inl (Sum.inl 1), Sum.inl (Sum.inl 0), Sum.inl (Sum.inl 1)]
  head := ![Sum.inl (Sum.inr 0), Sum.inl (Sum.inr 1), Sum.inl (Sum.inr 1), Sum.inl (Sum.inr 0)]
  lower := fun _ => 0
  upper := fun _ => 1
  cost := ![1, 1, 0, 0]
  supply := fun e => e.elim

lemma crossbar_feasible_iff (b : Fin 2 ⊕ Fin 2 → ℤ) (f : Fin 4 → ℤ) :
    crossbar.Feasible b f ↔ (∀ a, 0 ≤ f a ∧ f a ≤ 1) ∧
      f 0 + f 2 = b (Sum.inl 0) ∧ f 1 + f 3 = b (Sum.inl 1) ∧
      -(f 0 + f 3) = b (Sum.inr 0) ∧ -(f 1 + f 2) = b (Sum.inr 1) := by
  unfold Network.Feasible
  constructor
  · rintro ⟨hb, hv⟩
    refine ⟨hb, ?_, ?_, ?_, ?_⟩
    · have := hv (Sum.inl (Sum.inl 0))
      simpa [netOut, inc, crossbar, Fin.sum_univ_four] using this
    · have := hv (Sum.inl (Sum.inl 1))
      simpa [netOut, inc, crossbar, Fin.sum_univ_four] using this
    · have := hv (Sum.inl (Sum.inr 0))
      simp [netOut, inc, crossbar, Fin.sum_univ_four] at this; linarith
    · have := hv (Sum.inl (Sum.inr 1))
      simp [netOut, inc, crossbar, Fin.sum_univ_four] at this; linarith
  · rintro ⟨hb, h1, h2, h3, h4⟩
    refine ⟨hb, ?_⟩
    rintro ((t | t) | e)
    · fin_cases t
      · simpa [netOut, inc, crossbar, Fin.sum_univ_four] using h1
      · simpa [netOut, inc, crossbar, Fin.sum_univ_four] using h2
    · fin_cases t
      · simp [netOut, inc, crossbar, Fin.sum_univ_four]; linarith
      · simp [netOut, inc, crossbar, Fin.sum_univ_four]; linarith
    · exact e.elim

lemma crossbar_cost (f : Fin 4 → ℤ) : crossbar.flowCost f = f 0 + f 1 := by
  simp [Network.flowCost, crossbar, Fin.sum_univ_four]

/-- **Remark 4.6 (the crossbar).** The crossbar realizes the intended table `Φ(β_S) = |x - y|`,
but the two crossed states `e_{X_in} - e_{Y_out}` and `e_{Y_in} - e_{X_out}` also cost `0`, so
condition (ii) of Definition 4.2 fails and cannot be dropped from Theorem 4.3. -/
theorem crossbar_table :
    (∀ S, crossbar.boundary (intended S) = (comparatorTable S : WithTop ℤ)) ∧
    crossbar.boundary (Pi.single (Sum.inl 0) 1 - Pi.single (Sum.inr 1) 1) = (0 : ℤ) ∧
    crossbar.boundary (Pi.single (Sum.inl 1) 1 - Pi.single (Sum.inr 0) 1) = (0 : ℤ) := by
  have hS : ∀ S : Finset (Fin 2), S = ∅ ∨ S = {0} ∨ S = {1} ∨ S = univ := by decide
  refine ⟨?_, ?_, ?_⟩
  · intro S
    rcases hS S with rfl | rfl | rfl | rfl
    · refine crossbar.boundary_eq_of (f := ![0, 0, 0, 0]) ?_ ?_ ?_
      · rw [crossbar_feasible_iff]; refine ⟨by decide, ?_⟩; simp [intended]
      · simp [crossbar_cost, comparatorTable]
      · intro g hg; rw [crossbar_feasible_iff] at hg
        obtain ⟨hb, _⟩ := hg; rw [crossbar_cost]
        have := hb 0; have := hb 1; simp [comparatorTable]; omega
    · refine crossbar.boundary_eq_of (f := ![1, 0, 0, 0]) ?_ ?_ ?_
      · rw [crossbar_feasible_iff]; refine ⟨by decide, ?_⟩; simp [intended]
      · simp [crossbar_cost, comparatorTable]
      · intro g hg; rw [crossbar_feasible_iff] at hg
        obtain ⟨hb, h1, h2, h3, h4⟩ := hg; rw [crossbar_cost]
        have := hb 0; have := hb 1; have := hb 2; have := hb 3
        simp [intended] at h1 h2 h3 h4; simp [comparatorTable]; omega
    · refine crossbar.boundary_eq_of (f := ![0, 1, 0, 0]) ?_ ?_ ?_
      · rw [crossbar_feasible_iff]; refine ⟨by decide, ?_⟩; simp [intended]
      · simp [crossbar_cost, comparatorTable]
      · intro g hg; rw [crossbar_feasible_iff] at hg
        obtain ⟨hb, h1, h2, h3, h4⟩ := hg; rw [crossbar_cost]
        have := hb 0; have := hb 1; have := hb 2; have := hb 3
        simp [intended] at h1 h2 h3 h4; simp [comparatorTable]; omega
    · refine crossbar.boundary_eq_of (f := ![0, 0, 1, 1]) ?_ ?_ ?_
      · rw [crossbar_feasible_iff]; refine ⟨by decide, ?_⟩; simp [intended]
      · simp [crossbar_cost, comparatorTable]
      · intro g hg; rw [crossbar_feasible_iff] at hg
        obtain ⟨hb, _⟩ := hg; rw [crossbar_cost]
        have := hb 0; have := hb 1; simp [comparatorTable]; omega
  · refine crossbar.boundary_eq_of (f := ![0, 0, 1, 0]) ?_ ?_ ?_
    · rw [crossbar_feasible_iff]; refine ⟨by decide, ?_⟩; simp [Pi.single_apply]
    · simp [crossbar_cost]
    · intro g hg; rw [crossbar_feasible_iff] at hg
      obtain ⟨hb, _⟩ := hg; rw [crossbar_cost]
      have := hb 0; have := hb 1; omega
  · refine crossbar.boundary_eq_of (f := ![0, 0, 0, 1]) ?_ ?_ ?_
    · rw [crossbar_feasible_iff]; refine ⟨by decide, ?_⟩; simp [Pi.single_apply]
    · simp [crossbar_cost]
    · intro g hg; rw [crossbar_feasible_iff] at hg
      obtain ⟨hb, _⟩ := hg; rw [crossbar_cost]
      have := hb 0; have := hb 1; omega

/-! ### Proposition 4.1: the one-shot comparator -/

/-- **Proposition 4.1.** `min {p + n : x + n = y + p, p, n ≥ 0} = |x - y|`. -/
theorem oneShot_isLeast (x y : ℝ) :
    IsLeast {t | ∃ p n : ℝ, 0 ≤ p ∧ 0 ≤ n ∧ x + n = y + p ∧ t = p + n} |x - y| := by
  constructor
  · rcases le_total y x with h | h
    · exact ⟨x - y, 0, by linarith, le_rfl, by ring, by rw [abs_of_nonneg (by linarith)]; ring⟩
    · exact ⟨0, y - x, le_rfl, by linarith, by ring, by rw [abs_of_nonpos (by linarith)]; ring⟩
  · rintro t ⟨p, n, hp, hn, hxy, rfl⟩
    rw [abs_le']
    constructor <;> linarith

/-! ### Section 5: no submodular NAND gadget -/

/-- Submodularity on a lattice: `F(a) + F(a') ≥ F(a ⊓ a') + F(a ⊔ a')`. -/
def Submodular {L : Type*} [Lattice L] (F : L → ℝ) : Prop :=
  ∀ z z', F (z ⊓ z') + F (z ⊔ z') ≤ F z + F z'

/-- Projected minimizer relation `R_F = {x : F(x, a) = min F for some a}` (minimum = global
minimum of `F`). -/
def projMinRel {X Y : Type*} (F : X × Y → ℝ) : Set X :=
  {x | ∃ a, ∀ z, F (x, a) ≤ F z}

/-- The NAND relation `{(x₁, x₂, z) : z = 1 - x₁ x₂}` on Boolean labels. -/
def nandRel : Set (Fin 3 → Bool) := {x | x 2 = !(x 0 && x 1)}

/-- **Lemma 5.1 (Topkis).** Minimizers of a submodular function are closed under `⊓` and `⊔`. -/
lemma minimizers_lattice {L : Type*} [Lattice L] {F : L → ℝ} (hF : Submodular F) {z z' : L}
    (hz : ∀ w, F z ≤ F w) (hz' : ∀ w, F z' ≤ F w) :
    (∀ w, F (z ⊓ z') ≤ F w) ∧ ∀ w, F (z ⊔ z') ≤ F w := by
  have h := hF z z'
  constructor
  · intro w; have := hz (z ⊔ z'); have := hz' w; linarith
  · intro w; have := hz (z ⊓ z'); have := hz' w; linarith

/-- The projected minimizer relation of a submodular function is closed under `⊓` and `⊔`. -/
lemma projMinRel_closed {X Y : Type*} [Lattice X] [Lattice Y] {F : X × Y → ℝ}
    (hF : Submodular F) {x x' : X} (hx : x ∈ projMinRel F) (hx' : x' ∈ projMinRel F) :
    x ⊓ x' ∈ projMinRel F ∧ x ⊔ x' ∈ projMinRel F := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨a', ha'⟩ := hx'
  obtain ⟨h1, h2⟩ := minimizers_lattice hF ha ha'
  exact ⟨⟨a ⊓ a', h1⟩, ⟨a ⊔ a', h2⟩⟩

/-- **Theorem 5.2 (no submodular NAND gadget).** No submodular function `F(x, a)` of three visible
Boolean labels and any family of auxiliary Boolean labels has the NAND relation as its projected
minimizer relation. -/
theorem no_submodular_nand {α : Type*} (F : (Fin 3 → Bool) × (α → Bool) → ℝ)
    (hF : Submodular F) : projMinRel F ≠ nandRel := by
  intro h
  have h1 : (![false, false, true] : Fin 3 → Bool) ∈ projMinRel F := by
    rw [h]; simp only [nandRel, Set.mem_setOf_eq]; decide
  have h2 : (![true, true, false] : Fin 3 → Bool) ∈ projMinRel F := by
    rw [h]; simp only [nandRel, Set.mem_setOf_eq]; decide
  have := (projMinRel_closed hF h1 h2).1
  rw [h] at this
  simp only [nandRel, Set.mem_setOf_eq] at this
  revert this
  decide

/-- **Remark after Theorem 5.2.** None of the eight complemented versions of the NAND relation is
closed under both `⊓` and `⊔`; hence no submodular function has any of them as its projected
minimizer relation. -/
theorem no_submodular_nand_any_polarity {α : Type*} (F : (Fin 3 → Bool) × (α → Bool) → ℝ)
    (hF : Submodular F) (m : Fin 3 → Bool) :
    projMinRel F ≠ {x | (fun i => xor (x i) (m i)) ∈ nandRel} := by
  have key : ∀ m : Fin 3 → Bool, ∃ x y : Fin 3 → Bool,
      (fun i => xor (x i) (m i)) ∈ nandRel ∧ (fun i => xor (y i) (m i)) ∈ nandRel ∧
      ((fun i => xor ((x ⊓ y) i) (m i)) ∉ nandRel ∨
        (fun i => xor ((x ⊔ y) i) (m i)) ∉ nandRel) := by
    simp only [nandRel, Set.mem_setOf_eq]; decide
  intro h
  obtain ⟨x, y, hx, hy, hxy⟩ := key m
  have hx' : x ∈ projMinRel F := by rw [h]; exact hx
  have hy' : y ∈ projMinRel F := by rw [h]; exact hy
  obtain ⟨c1, c2⟩ := projMinRel_closed hF hx' hy'
  rw [h] at c1 c2
  rcases hxy with hxy | hxy
  · exact hxy c1
  · exact hxy c2

end GC.FlowCircuits
