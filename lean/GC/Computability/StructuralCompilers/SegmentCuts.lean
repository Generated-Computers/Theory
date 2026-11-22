import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Segment cuts and the guard–router reduction (manuscript 007b)

Paths are measured by their number of vertices. A set `S` is *feasible for length `k`* if every
directed path with `k` vertices meets it, and `dvd_k(H)` is the minimum size of a feasible set
(Definition 7.1; viewing a DAG as its own skeleton, `dvd_k = scut_{k-1}`). Paths are given as
sequences `p 0 → p 1 → ⋯ → p (k-1)`; in a DAG such a sequence has distinct vertices.

* `maximal_packing_bound` (Theorem 6.4): the union of a maximal packing of vertex-disjoint
  `(L+1)`-vertex paths hits every such path and has at most `(L+1)·|M⋆|` vertices for every
  hitting set `M⋆`.
* `guardRouter_feasible_lift`, `guardRouter_feasible_project`, `guardRouter_dvd`
  (Lemma 7.4 and Theorem 7.5): for the guard–router expansion `R_d(H)` and `K = k(2d+1)`,
  `dvd_K(R_d(H)) = dvd_k(H)`; feasible sets map both ways (cores of `S`, owners of `S'`).
* `anonymity_scut_one`, `anonymity_class_union` (Theorem 8.6): on the family `𝒩_k`,
  `scut_1 = k+1`, while every feasible union of the classes `A`, `B` has `2k+1` vertices.
-/

namespace GC.StructuralCompilers

/-! ### Paths, feasible sets and `dvd_k` -/

section Paths

variable {V : Type*}

/-- `p 0 → p 1 → ⋯ → p (k-1)` is a directed path with `k` vertices. -/
def IsPathOf (adj : V → V → Prop) (k : ℕ) (p : ℕ → V) : Prop :=
  ∀ i, i + 1 < k → adj (p i) (p (i + 1))

/-- `S` is feasible for length `k`: every directed path with `k` vertices meets `S`. -/
def Feasible (adj : V → V → Prop) (k : ℕ) (S : Finset V) : Prop :=
  ∀ p, IsPathOf adj k p → ∃ i, i < k ∧ p i ∈ S

/-- `dvd_k(H)`: the minimum number of vertices meeting every directed path with `k` vertices. -/
noncomputable def dvd (adj : V → V → Prop) (k : ℕ) : ℕ :=
  sInf {n | ∃ S : Finset V, S.card = n ∧ Feasible adj k S}

end Paths

/-! ### Maximal path packings (Theorem 6.4) -/

/-- **Theorem 6.4 (maximal-packing approximation)**, in hypergraph form. Let `F` be a finite
family of vertex sets with `L + 1` elements each (the vertex sets of the `(L+1)`-vertex paths)
and `Q ⊆ F` a maximal family of pairwise disjoint members. Then the union `M(Q)` meets every
member of `F`, and `|M(Q)| ≤ (L+1)|M⋆|` for every set `M⋆` meeting every member of `F`. -/
theorem maximal_packing_bound {V : Type*} [DecidableEq V] (L : ℕ) (F Q : Finset (Finset V))
    (hcard : ∀ P ∈ F, P.card = L + 1) (hsub : Q ⊆ F)
    (hdisj : ∀ P ∈ Q, ∀ P' ∈ Q, P ≠ P' → Disjoint P P')
    (hmax : ∀ P ∈ F, ∃ P' ∈ Q, ¬ Disjoint P P') :
    (∀ P ∈ F, ¬ Disjoint P (Q.biUnion id)) ∧
    ∀ Mstar : Finset V, (∀ P ∈ F, ¬ Disjoint P Mstar) →
      (Q.biUnion id).card ≤ (L + 1) * Mstar.card := by
  classical
  refine ⟨?_, ?_⟩
  · intro P hP hd
    obtain ⟨P', hP', hnd⟩ := hmax P hP
    apply hnd
    exact Finset.disjoint_of_subset_right (Finset.subset_biUnion_of_mem id hP') hd
  · intro Mstar hM
    rcases isEmpty_or_nonempty V with hV | hV
    · rw [Finset.eq_empty_of_isEmpty (Q.biUnion id)]
      simp
    have hU : (Q.biUnion id).card = (L + 1) * Q.card := by
      calc (Q.biUnion id).card = ∑ P ∈ Q, (id P).card :=
            Finset.card_biUnion (fun P hP P' hP' hne => hdisj P hP P' hP' hne)
        _ = ∑ _P ∈ Q, (L + 1) := Finset.sum_congr rfl (fun P hP => hcard P (hsub hP))
        _ = (L + 1) * Q.card := by rw [Finset.sum_const]; simp [Nat.mul_comm]
    -- each packed path contains a vertex of `M⋆`, and these vertices are distinct
    have hpick : ∀ P ∈ Q, ∃ x, x ∈ P ∧ x ∈ Mstar := by
      intro P hP
      have := hM P (hsub hP)
      rw [Finset.not_disjoint_iff] at this
      exact this
    choose! f hf using hpick
    have hinj : Set.InjOn f Q := by
      intro P hP P' hP' heq
      by_contra hne
      have := hdisj P hP P' hP' hne
      exact Finset.disjoint_left.1 this (hf P hP).1 (heq ▸ (hf P' hP').1)
    have hle : Q.card ≤ Mstar.card := by
      rw [← Finset.card_image_of_injOn hinj]
      apply Finset.card_le_card
      intro x hx
      obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hx
      exact (hf P hP).2
    rw [hU]
    exact Nat.mul_le_mul_left _ hle

/-! ### The guard–router expansion (Definition 7.3) -/

/-- The vertices of the guard–router expansion `R_d(H)`: guards `g_{v,i+1}` (`i < d`), the core
`c_v`, and the routing-trie nodes `r_{v,s}` for binary words `s` of length less than `d`. The
virtual sink `⊤` is not a vertex. -/
inductive GRVertex (V : Type*) (d : ℕ) where
  | guard (v : V) (i : Fin d)
  | core (v : V)
  | route (v : V) (s : List Bool) (hs : s.length < d)
  deriving DecidableEq

/-- The arcs of `R_d(H)`; `lab v u` is the binary word assigned to the arc `v → u`. -/
def grAdj {V : Type*} (adj : V → V → Prop) (d : ℕ) (lab : V → V → List Bool) :
    GRVertex V d → GRVertex V d → Prop
  | .guard v i, .guard v' i' => v' = v ∧ i'.val = i.val + 1
  | .guard v i, .core v' => v' = v ∧ i.val + 1 = d
  | .core v, .route v' s _ => v' = v ∧ s = []
  | .route v s _, .route v' s' _ => v' = v ∧ ∃ b, s' = s ++ [b]
  | .route v s _, .guard u i => s.length + 1 = d ∧ i.val = 0 ∧ adj v u ∧ ∃ b, lab v u = s ++ [b]
  | _, _ => False

namespace GRVertex

variable {V : Type*} {d : ℕ}

/-- The owner `π(x)` of a gadget vertex. -/
def owner : GRVertex V d → V
  | guard v _ => v
  | core v => v
  | route v _ _ => v

/-- The position of a vertex in its gadget: guards `0, …, d-1`, core `d`, routing nodes
`d+1, …, 2d`. -/
def phase : GRVertex V d → ℕ
  | guard _ i => i.val
  | core _ => d
  | route _ s _ => d + 1 + s.length

lemma core_injective : Function.Injective (core : V → GRVertex V d) := by
  intro v w h
  cases h
  rfl

lemma phase_le (x : GRVertex V d) : x.phase ≤ 2 * d := by
  cases x with
  | guard v i => simp only [phase]; omega
  | core v => simp only [phase]; omega
  | route v s hs => simp only [phase]; omega

lemma eq_core_of_phase (x : GRVertex V d) (h : x.phase = d) : x = core x.owner := by
  cases x with
  | guard v i => simp only [phase] at h; omega
  | core v => rfl
  | route v s hs => simp only [phase] at h; omega

end GRVertex

open GRVertex

lemma grAdj_step {V : Type*} {adj : V → V → Prop} {d : ℕ} (hd : 1 ≤ d)
    {lab : V → V → List Bool} {x y : GRVertex V d} (h : grAdj adj d lab x y) :
    y.phase = (x.phase + 1) % (2 * d + 1) ∧
      (x.phase = 2 * d → adj x.owner y.owner) ∧ (x.phase ≠ 2 * d → y.owner = x.owner) := by
  cases x with
  | guard v i =>
    cases y with
    | guard v' i' =>
      obtain ⟨rfl, hi⟩ := h
      simp only [phase, owner]
      have := i'.isLt
      refine ⟨by rw [Nat.mod_eq_of_lt (by omega)]; omega, fun h => by omega, fun _ => by first | rfl | trivial⟩
    | core v' =>
      obtain ⟨rfl, hi⟩ := h
      simp only [phase, owner]
      refine ⟨by rw [Nat.mod_eq_of_lt (by omega)]; omega, fun h => by omega, fun _ => by first | rfl | trivial⟩
    | route v' s hs => exact absurd h (by simp [grAdj])
  | core v =>
    cases y with
    | guard v' i' => exact absurd h (by simp [grAdj])
    | core v' => exact absurd h (by simp [grAdj])
    | route v' s hs =>
      obtain ⟨rfl, rfl⟩ := h
      simp only [phase, owner, List.length_nil]
      refine ⟨by rw [Nat.mod_eq_of_lt (by omega)], fun h => by omega, fun _ => by first | rfl | trivial⟩
  | route v s hs =>
    cases y with
    | guard u i =>
      obtain ⟨hlen, hi, hadj, -⟩ := h
      simp only [phase, owner]
      refine ⟨?_, fun _ => hadj, fun h => by omega⟩
      rw [hi, show d + 1 + s.length + 1 = 2 * d + 1 by omega, Nat.mod_self]
    | core v' => exact absurd h (by simp [grAdj])
    | route v' s' hs' =>
      obtain ⟨rfl, b, rfl⟩ := h
      have hl : (s ++ [b]).length = s.length + 1 := by simp
      simp only [phase, owner, hl]
      refine ⟨by rw [Nat.mod_eq_of_lt (by omega)]; omega, fun h => by omega, fun _ => by first | rfl | trivial⟩

/-- **Lemma 7.4 / Theorem 7.5 (first direction).** If `S` is feasible for length `k` in `H`,
then the set of cores `{c_v : v ∈ S}` is feasible for length `K = k(2d+1)` in `R_d(H)`. -/
theorem guardRouter_feasible_lift {V : Type*} [DecidableEq V] (adj : V → V → Prop) (d : ℕ)
    (hd : 1 ≤ d) (lab : V → V → List Bool) (k : ℕ) (S : Finset V) (hS : Feasible adj k S) :
    Feasible (grAdj adj d lab) (k * (2 * d + 1)) (S.image core) := by
  intro p hp
  set m := 2 * d + 1 with hm
  have hmpos : 0 < m := by omega
  set ph0 := (p 0).phase with hph0
  have hph0le : ph0 ≤ 2 * d := (p 0).phase_le
  -- phases advance by one modulo `m`
  have hph : ∀ t, t < k * m → (p t).phase = (ph0 + t) % m := by
    intro t
    induction t with
    | zero =>
      intro _
      rw [Nat.add_zero, Nat.mod_eq_of_lt (by omega)]
    | succ t ih =>
      intro ht
      rw [(grAdj_step hd (hp t ht)).1, ih (by omega), Nat.mod_add_mod, Nat.add_assoc]
  -- the first core on the path
  set t0 := (d + m - ph0) % m with ht0
  have ht0lt : t0 < m := Nat.mod_lt _ hmpos
  have hbase : (ph0 + t0) % m = d := by
    rw [ht0, Nat.add_mod_mod, show ph0 + (d + m - ph0) = d + m by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  have hphase0 : ∀ i j, t0 + i * m + j < k * m →
      (p (t0 + i * m + j)).phase = (d + j) % m := by
    intro i j hij
    rw [hph _ hij, show ph0 + (t0 + i * m + j) = (ph0 + t0 + j) + i * m by ring,
      Nat.add_mul_mod_self_right, ← Nat.mod_add_mod, hbase]
  have hwin : ∀ i, i + 1 < k → t0 + (i + 1) * m < k * m := by
    intro i hi
    have : (i + 1) * m + m ≤ k * m := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hi
    omega
  -- owners along a window between consecutive cores
  have hown : ∀ i, i + 1 < k →
      adj (p (t0 + i * m)).owner (p (t0 + (i + 1) * m)).owner := by
    intro i hi
    have hb := hwin i hi
    have hsplit : t0 + (i + 1) * m = t0 + i * m + (d + 1) + d := by rw [hm]; ring
    have h1 : ∀ j, j ≤ d → (p (t0 + i * m + j)).owner = (p (t0 + i * m)).owner := by
      intro j
      induction j with
      | zero => intro _; rfl
      | succ j ih =>
        intro hj
        have hlt : t0 + i * m + j + 1 < k * m := by omega
        have hs := grAdj_step hd (hp (t0 + i * m + j) hlt)
        have hpj := hphase0 i j (by omega)
        rw [Nat.mod_eq_of_lt (by omega)] at hpj
        rw [← Nat.add_assoc, hs.2.2 (by omega), ih (by omega)]
    have h2 : ∀ j, j ≤ d → (p (t0 + i * m + (d + 1) + j)).owner =
        (p (t0 + i * m + (d + 1))).owner := by
      intro j
      induction j with
      | zero => intro _; rfl
      | succ j ih =>
        intro hj
        have hlt : t0 + i * m + (d + 1) + j + 1 < k * m := by omega
        have hs := grAdj_step hd (hp (t0 + i * m + (d + 1) + j) hlt)
        have hpj := hphase0 i ((d + 1) + j) (by omega)
        rw [show d + (d + 1 + j) = j + m by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega), ← Nat.add_assoc] at hpj
        rw [← Nat.add_assoc, hs.2.2 (by omega), ih (by omega)]
    have hmid := grAdj_step hd (hp (t0 + i * m + d) (by omega))
    have hpd := hphase0 i d (by omega)
    rw [Nat.mod_eq_of_lt (by omega)] at hpd
    have hadj := hmid.2.1 (by omega)
    rw [h1 d le_rfl] at hadj
    rw [hsplit, h2 d le_rfl]
    rw [show t0 + i * m + d + 1 = t0 + i * m + (d + 1) by ring] at hadj
    exact hadj
  obtain ⟨i, hi, hiS⟩ := hS (fun i => (p (t0 + i * m)).owner) (fun i hi => hown i hi)
  have hb : t0 + i * m < k * m := by
    have : i * m + m ≤ k * m := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hi
    omega
  refine ⟨t0 + i * m, hb, ?_⟩
  have hpc := hphase0 i 0 (by simpa using hb)
  rw [Nat.add_zero, Nat.add_zero, Nat.mod_eq_of_lt (by omega)] at hpc
  rw [eq_core_of_phase _ hpc]
  exact Finset.mem_image_of_mem _ hiS

/-- The gadget vertex of `v` at position `j` (`0 ≤ j ≤ 2d`), following the routing word `w`. -/
def gadgetVtx {V : Type*} (d : ℕ) (v : V) (w : List Bool) (j : ℕ) : GRVertex V d :=
  if h : j < d then .guard v ⟨j, h⟩
  else if j = d then .core v
  else if h' : j - d - 1 < d then
    .route v (w.take (j - d - 1)) (lt_of_le_of_lt (List.length_take_le _ _) h')
  else .core v

lemma owner_gadgetVtx {V : Type*} (d : ℕ) (v : V) (w : List Bool) (j : ℕ) :
    (gadgetVtx d v w j).owner = v := by
  unfold gadgetVtx
  split_ifs <;> rfl

lemma grAdj_gadget_inner {V : Type*} (adj : V → V → Prop) (d : ℕ) (hd : 1 ≤ d)
    (lab : V → V → List Bool) (v : V) (w : List Bool) (hw : w.length = d) (j : ℕ)
    (hj : j < 2 * d) : grAdj adj d lab (gadgetVtx d v w j) (gadgetVtx d v w (j + 1)) := by
  unfold gadgetVtx
  by_cases h1 : j + 1 < d
  · rw [dif_pos (by omega), dif_pos h1]
    exact ⟨rfl, rfl⟩
  · by_cases h2 : j + 1 = d
    · rw [dif_pos (by omega), dif_neg h1, if_pos h2]
      exact ⟨rfl, by simp; omega⟩
    · by_cases h3 : j = d
      · rw [dif_neg (by omega), if_pos h3, dif_neg h1, if_neg h2, dif_pos (by omega)]
        refine ⟨rfl, ?_⟩
        rw [show j + 1 - d - 1 = 0 by omega, List.take_zero]
      · rw [dif_neg (by omega), if_neg h3, dif_pos (by omega), dif_neg h1, if_neg h2,
          dif_pos (by omega)]
        refine ⟨rfl, w[j - d - 1]'(by omega), ?_⟩
        rw [show j + 1 - d - 1 = (j - d - 1) + 1 by omega, List.take_append_getElem]

lemma grAdj_gadget_exit {V : Type*} (adj : V → V → Prop) (d : ℕ) (hd : 1 ≤ d)
    (lab : V → V → List Bool) (v u : V) (hvu : adj v u) (hw : (lab v u).length = d) (w' : List Bool) :
    grAdj adj d lab (gadgetVtx d v (lab v u) (2 * d)) (gadgetVtx d u w' 0) := by
  unfold gadgetVtx
  rw [dif_neg (by omega), if_neg (by omega), dif_pos (by omega), dif_pos (by omega)]
  refine ⟨?_, rfl, hvu, (lab v u)[d - 1]'(by omega), ?_⟩
  · simp only [List.length_take]; omega
  · rw [show 2 * d - d - 1 = d - 1 by omega, List.take_append_getElem,
      show d - 1 + 1 = d by omega, ← hw, List.take_length]

/-- **Lemma 7.4 / Theorem 7.5 (second direction).** If `S'` is feasible for length
`K = k(2d+1)` in `R_d(H)` (all arc words of length `d`), then its set of owners `π(S')` is
feasible for length `k` in `H`. -/
theorem guardRouter_feasible_project {V : Type*} [DecidableEq V] (adj : V → V → Prop) (d : ℕ)
    (hd : 1 ≤ d) (lab : V → V → List Bool) (hlab : ∀ v u, adj v u → (lab v u).length = d)
    (k : ℕ) (S' : Finset (GRVertex V d))
    (hS' : Feasible (grAdj adj d lab) (k * (2 * d + 1)) S') :
    Feasible adj k (S'.image owner) := by
  intro q hq
  by_contra hno
  push Not at hno
  set m := 2 * d + 1 with hm
  have hmpos : 0 < m := by omega
  let word : ℕ → List Bool := fun i =>
    if i + 1 < k then lab (q i) (q (i + 1)) else List.replicate d false
  have hword : ∀ i, (word i).length = d := by
    intro i
    simp only [word]
    split_ifs with h
    · exact hlab _ _ (hq i h)
    · simp
  let p : ℕ → GRVertex V d := fun t => gadgetVtx d (q (t / m)) (word (t / m)) (t % m)
  have hpath : IsPathOf (grAdj adj d lab) (k * m) p := by
    intro t ht
    have hdm := Nat.mod_add_div t m
    have hjlt := Nat.mod_lt t hmpos
    by_cases hj : t % m < 2 * d
    · -- inside a gadget
      have h1 : (t + 1) / m = t / m ∧ (t + 1) % m = t % m + 1 :=
        (Nat.div_mod_unique hmpos).2 ⟨by omega, by omega⟩
      simp only [p, h1.1, h1.2]
      exact grAdj_gadget_inner adj d hd lab _ _ (hword _) _ hj
    · -- the exit into the next gadget
      have hj' : t % m = 2 * d := by omega
      have h1 : (t + 1) / m = t / m + 1 ∧ (t + 1) % m = 0 :=
        (Nat.div_mod_unique hmpos).2 ⟨by rw [Nat.mul_add]; omega, hmpos⟩
      have hik : t / m + 1 < k := by
        by_contra hcon
        have : k * m ≤ (t / m + 1) * m := Nat.mul_le_mul_right _ (by omega)
        rw [Nat.add_mul] at this
        rw [Nat.mul_comm] at hdm
        omega
      simp only [p, h1.1, h1.2, hj']
      have hw : word (t / m) = lab (q (t / m)) (q (t / m + 1)) := by
        simp only [word, if_pos hik]
      rw [hw]
      exact grAdj_gadget_exit adj d hd lab _ _ (hq _ hik) (hlab _ _ (hq _ hik)) _
  obtain ⟨t, ht, hpt⟩ := hS' p hpath
  have hown : (p t).owner = q (t / m) := owner_gadgetVtx _ _ _ _
  have htk : t / m < k := by
    rw [Nat.div_lt_iff_lt_mul hmpos]
    exact ht
  apply hno (t / m) htk
  rw [← hown]
  exact Finset.mem_image_of_mem _ hpt

/-- **Theorem 7.5 (exact degree-two reduction).** For every digraph `H`, every `d ≥ 1`, every
assignment of words of length `d` to the arcs, and every `k`, with `K = k(2d+1)`:
`dvd_K(R_d(H)) = dvd_k(H)`. -/
theorem guardRouter_dvd {V : Type*} [DecidableEq V] (adj : V → V → Prop) (d : ℕ) (hd : 1 ≤ d)
    (lab : V → V → List Bool) (hlab : ∀ v u, adj v u → (lab v u).length = d) (k : ℕ) :
    dvd (grAdj adj d lab) (k * (2 * d + 1)) = dvd adj k := by
  classical
  set AR := {n | ∃ S : Finset (GRVertex V d), S.card = n ∧
    Feasible (grAdj adj d lab) (k * (2 * d + 1)) S}
  set AH := {n | ∃ S : Finset V, S.card = n ∧ Feasible adj k S}
  have hHR : AH ⊆ AR := by
    rintro n ⟨S, rfl, hS⟩
    exact ⟨S.image core, Finset.card_image_of_injective _ core_injective,
      guardRouter_feasible_lift adj d hd lab k S hS⟩
  have hRH : ∀ n ∈ AR, ∃ n' ∈ AH, n' ≤ n := by
    rintro n ⟨S', rfl, hS'⟩
    exact ⟨_, ⟨_, rfl, guardRouter_feasible_project adj d hd lab hlab k S' hS'⟩,
      Finset.card_image_le⟩
  show sInf AR = sInf AH
  rcases Set.eq_empty_or_nonempty AH with hAH | hAH
  · have : AR = ∅ := by
      ext n
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hn
      obtain ⟨n', hn', -⟩ := hRH n hn
      rw [hAH] at hn'
      exact hn'
    rw [this, hAH]
  · apply le_antisymm
    · exact Nat.sInf_le (hHR (Nat.sInf_mem hAH))
    · obtain ⟨n', hn', hle⟩ := hRH _ (Nat.sInf_mem (hAH.mono hHR))
      exact (Nat.sInf_le hn').trans hle

/-! ### Rank anonymity (Theorem 8.6) -/

/-- The internal arcs of the skeleton `𝒩_k`: vertices `a_{i+1}` (`inl i`) and `b_j` (`inr j`),
`0 ≤ i, j ≤ 2k`; `a_{i+1} → b_{2i+1}, b_{2i+2}` for `i < k`, and `a_{i+1} → b_0` for `i ≥ k`. -/
def anonAdj (k : ℕ) : Fin (2 * k + 1) ⊕ Fin (2 * k + 1) → Fin (2 * k + 1) ⊕ Fin (2 * k + 1) → Prop
  | .inl i, .inr j => (i.val < k ∧ (j.val = 2 * i.val + 1 ∨ j.val = 2 * i.val + 2)) ∨
      (k ≤ i.val ∧ j.val = 0)
  | _, _ => False

/-- **Theorem 8.6 (first part).** `scut_1(𝒩_k) = dvd_2(𝒩_k) = k + 1` (by Proposition 6.2,
`scut_1` is the minimum number of internal vertices meeting every internal arc). -/
theorem anonymity_scut_one (k : ℕ) : dvd (anonAdj k) 2 = k + 1 := by
  classical
  apply le_antisymm
  · -- the set `{a_1, …, a_k, b_0}`
    apply Nat.sInf_le
    let e : Fin k ↪ Fin (2 * k + 1) ⊕ Fin (2 * k + 1) :=
      (Fin.castLEEmb (by omega)).trans Function.Embedding.inl
    have hnot : (Sum.inr ⟨0, by omega⟩ : Fin (2 * k + 1) ⊕ Fin (2 * k + 1)) ∉
        Finset.univ.map e := by
      simp [e]
    refine ⟨(Finset.univ.map e).cons (.inr ⟨0, by omega⟩) hnot, ?_, ?_⟩
    · rw [Finset.card_cons, Finset.card_map, Finset.card_univ, Fintype.card_fin]
    · intro p hp
      have h01 : anonAdj k (p 0) (p 1) := hp 0 (by norm_num)
      cases hx : p 0 with
      | inr i => rw [hx] at h01; cases hy : p 1 <;> rw [hy] at h01 <;> exact absurd h01 id
      | inl i =>
        cases hy : p 1 with
        | inl j => rw [hx, hy] at h01; exact absurd h01 id
        | inr j =>
          rw [hx, hy] at h01
          rcases h01 with ⟨hik, -⟩ | ⟨-, hj0⟩
          · refine ⟨0, by norm_num, ?_⟩
            rw [hx]
            apply Finset.mem_cons_of_mem
            rw [Finset.mem_map]
            exact ⟨⟨i.val, hik⟩, Finset.mem_univ _, rfl⟩
          · refine ⟨1, by norm_num, ?_⟩
            rw [hy]
            have : j = ⟨0, by omega⟩ := Fin.ext hj0
            rw [this]
            exact Finset.mem_cons_self _ _
  · -- `k + 1` pairwise disjoint internal arcs
    apply le_csInf
    · exact ⟨_, Finset.univ, rfl, fun p _ => ⟨0, by norm_num, Finset.mem_univ _⟩⟩
    rintro n ⟨S, rfl, hS⟩
    let u : Fin (k + 1) → Fin (2 * k + 1) ⊕ Fin (2 * k + 1) := fun i => .inl ⟨i.val, by omega⟩
    let w : Fin (k + 1) → Fin (2 * k + 1) ⊕ Fin (2 * k + 1) := fun i =>
      if h : i.val < k then .inr ⟨2 * i.val + 1, by omega⟩ else .inr ⟨0, by omega⟩
    have hhit : ∀ i, u i ∈ S ∨ w i ∈ S := by
      intro i
      obtain ⟨t, ht, hmem⟩ := hS (fun t => if t = 0 then u i else w i) (by
        intro t ht
        have : t = 0 := by omega
        subst this
        simp only [if_true, Nat.zero_add, one_ne_zero, if_false, u, w]
        by_cases hik : i.val < k
        · rw [dif_pos hik]
          exact Or.inl ⟨hik, Or.inl rfl⟩
        · rw [dif_neg hik]
          exact Or.inr ⟨Nat.le_of_not_lt hik, rfl⟩)
      rcases (show t = 0 ∨ t = 1 by omega) with rfl | rfl
      · exact Or.inl (by simpa using hmem)
      · exact Or.inr (by simpa using hmem)
    let g : Fin (k + 1) → Fin (2 * k + 1) ⊕ Fin (2 * k + 1) := fun i =>
      if u i ∈ S then u i else w i
    have hgS : ∀ i, g i ∈ S := by
      intro i
      simp only [g]
      split_ifs with h
      · exact h
      · exact (hhit i).resolve_left h
    have hinj : Function.Injective g := by
      intro i j hij
      simp only [g] at hij
      split_ifs at hij with h1 h2 h2
      · simp only [u, Sum.inl.injEq, Fin.mk.injEq] at hij
        exact Fin.ext hij
      · simp only [u, w] at hij
        split_ifs at hij
      · simp only [u, w] at hij
        split_ifs at hij
      · simp only [w] at hij
        apply Fin.ext
        split_ifs at hij with h3 h4 h4
        · simp only [Sum.inr.injEq, Fin.mk.injEq] at hij; omega
        · simp only [Sum.inr.injEq, Fin.mk.injEq] at hij; omega
        · simp only [Sum.inr.injEq, Fin.mk.injEq] at hij; omega
        · have := i.isLt; have := j.isLt; omega
    have := Finset.card_le_card (show Finset.univ.image g ⊆ S by
      intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
      exact hgS i)
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin] at this
    exact this

/-- The union of the classes `A = {a_i}` (if `useA`) and `B = {b_j}` (if `useB`). -/
def classUnion (k : ℕ) (useA useB : Bool) : Finset (Fin (2 * k + 1) ⊕ Fin (2 * k + 1)) :=
  (if useA then Finset.univ.map Function.Embedding.inl else ∅) ∪
    (if useB then Finset.univ.map Function.Embedding.inr else ∅)

/-- **Theorem 8.6 (second part).** For `k ≥ 1`, every set of segment depth at most one in `𝒩_k`
that is a union of the classes `A` and `B` has at least `2k + 1` vertices, while
`scut_1(𝒩_k) = k + 1`. (The identification of `A` and `B` with the rank classes is not
formalized.) -/
theorem anonymity_class_union (k : ℕ) (hk : 1 ≤ k) (useA useB : Bool)
    (hS : Feasible (anonAdj k) 2 (classUnion k useA useB)) :
    2 * k + 1 ≤ (classUnion k useA useB).card := by
  have hA : (Finset.univ.map (Function.Embedding.inl :
      Fin (2 * k + 1) ↪ Fin (2 * k + 1) ⊕ Fin (2 * k + 1))).card = 2 * k + 1 := by
    rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have hB : (Finset.univ.map (Function.Embedding.inr :
      Fin (2 * k + 1) ↪ Fin (2 * k + 1) ⊕ Fin (2 * k + 1))).card = 2 * k + 1 := by
    rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]
  cases useA <;> cases useB
  · exfalso
    obtain ⟨t, -, hmem⟩ := hS
      (fun t => if t = 0 then .inl ⟨0, by omega⟩ else .inr ⟨1, by omega⟩)
      (by
        intro t ht
        have : t = 0 := by omega
        subst this
        simp only [if_true, Nat.zero_add, one_ne_zero, if_false]
        exact Or.inl ⟨by simp only; omega, Or.inl rfl⟩)
    simp [classUnion] at hmem
  · simp only [classUnion, Bool.false_eq_true, if_false, if_true, Finset.empty_union]
    rw [hB]
  · simp only [classUnion, Bool.false_eq_true, if_false, if_true, Finset.union_empty]
    rw [hA]
  · simp only [classUnion, if_true]
    have := Finset.card_le_card (Finset.subset_union_left
      (s₁ := Finset.univ.map (Function.Embedding.inl :
        Fin (2 * k + 1) ↪ Fin (2 * k + 1) ⊕ Fin (2 * k + 1)))
      (s₂ := Finset.univ.map Function.Embedding.inr))
    omega

end GC.StructuralCompilers
