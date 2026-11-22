import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace GC.StructuralCompilers

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
  sorry

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

end GRVertex

open GRVertex

/-- **Lemma 7.4 / Theorem 7.5 (first direction).** If `S` is feasible for length `k` in `H`,
then the set of cores `{c_v : v ∈ S}` is feasible for length `K = k(2d+1)` in `R_d(H)`. -/
theorem guardRouter_feasible_lift {V : Type*} [DecidableEq V] (adj : V → V → Prop) (d : ℕ)
    (hd : 1 ≤ d) (lab : V → V → List Bool) (k : ℕ) (S : Finset V) (hS : Feasible adj k S) :
    Feasible (grAdj adj d lab) (k * (2 * d + 1)) (S.image core) := by
  sorry

/-- The gadget vertex of `v` at position `j` (`0 ≤ j ≤ 2d`), following the routing word `w`. -/
def gadgetVtx {V : Type*} (d : ℕ) (v : V) (w : List Bool) (j : ℕ) : GRVertex V d :=
  if h : j < d then .guard v ⟨j, h⟩
  else if j = d then .core v
  else if h' : j - d - 1 < d then
    .route v (w.take (j - d - 1)) (lt_of_le_of_lt (List.length_take_le _ _) h')
  else .core v

/-- **Lemma 7.4 / Theorem 7.5 (second direction).** If `S'` is feasible for length
`K = k(2d+1)` in `R_d(H)` (all arc words of length `d`), then its set of owners `π(S')` is
feasible for length `k` in `H`. -/
theorem guardRouter_feasible_project {V : Type*} [DecidableEq V] (adj : V → V → Prop) (d : ℕ)
    (hd : 1 ≤ d) (lab : V → V → List Bool) (hlab : ∀ v u, adj v u → (lab v u).length = d)
    (k : ℕ) (S' : Finset (GRVertex V d))
    (hS' : Feasible (grAdj adj d lab) (k * (2 * d + 1)) S') :
    Feasible adj k (S'.image owner) := by
  sorry

/-- **Theorem 7.5 (exact degree-two reduction).** For every digraph `H`, every `d ≥ 1`, every
assignment of words of length `d` to the arcs, and every `k`, with `K = k(2d+1)`:
`dvd_K(R_d(H)) = dvd_k(H)`. -/
theorem guardRouter_dvd {V : Type*} [DecidableEq V] (adj : V → V → Prop) (d : ℕ) (hd : 1 ≤ d)
    (lab : V → V → List Bool) (hlab : ∀ v u, adj v u → (lab v u).length = d) (k : ℕ) :
    dvd (grAdj adj d lab) (k * (2 * d + 1)) = dvd adj k := by
  sorry

/-- The internal arcs of the skeleton `𝒩_k`: vertices `a_{i+1}` (`inl i`) and `b_j` (`inr j`),
`0 ≤ i, j ≤ 2k`; `a_{i+1} → b_{2i+1}, b_{2i+2}` for `i < k`, and `a_{i+1} → b_0` for `i ≥ k`. -/
def anonAdj (k : ℕ) : Fin (2 * k + 1) ⊕ Fin (2 * k + 1) → Fin (2 * k + 1) ⊕ Fin (2 * k + 1) → Prop
  | .inl i, .inr j => (i.val < k ∧ (j.val = 2 * i.val + 1 ∨ j.val = 2 * i.val + 2)) ∨
      (k ≤ i.val ∧ j.val = 0)
  | _, _ => False

/-- **Theorem 8.6 (first part).** `scut_1(𝒩_k) = dvd_2(𝒩_k) = k + 1` (by Proposition 6.2,
`scut_1` is the minimum number of internal vertices meeting every internal arc). -/
theorem anonymity_scut_one (k : ℕ) : dvd (anonAdj k) 2 = k + 1 := by
  sorry

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
  sorry

end GC.StructuralCompilers
