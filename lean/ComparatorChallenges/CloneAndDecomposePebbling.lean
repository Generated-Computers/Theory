import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Prod
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Lattice.Nat

namespace GC.StructuralCompilers

section Pebbling

variable {V : Type*} [DecidableEq V]

/-- One legal step of a black pebbling: keep the configuration, place a pebble on a vertex all of
whose predecessors are pebbled, or remove a pebble. -/
def LegalStep (pred : V → Finset V) (S S' : Finset V) : Prop :=
  S' = S ∨ (∃ v, pred v ⊆ S ∧ S' = insert v S) ∨ (∃ v, S' = S.erase v)

/-- A black pebbling of the DAG given by `pred` with target `t`. -/
structure Pebbling (pred : V → Finset V) (t : V) where
  /-- number of steps -/
  len : ℕ
  /-- the configurations `conf 0, …, conf len` -/
  conf : ℕ → Finset V
  /-- the pebbling starts from the empty configuration -/
  start : conf 0 = ∅
  /-- every step is legal -/
  step : ∀ k, k < len → LegalStep pred (conf k) (conf (k + 1))
  /-- the target is pebbled at some step -/
  hits : ∃ k, k ≤ len ∧ t ∈ conf k

/-- The cost of a pebbling: the maximum number of pebbles at any time. -/
def Pebbling.cost {pred : V → Finset V} {t : V} (P : Pebbling pred t) : ℕ :=
  (Finset.range (P.len + 1)).sup (fun k => (P.conf k).card)

end Pebbling

/-- A gate DAG: every vertex has a gate type and an ordered list of predecessors. -/
structure GateDAG (V τ : Type*) where
  /-- ordered predecessors -/
  preds : V → List V
  /-- gate type -/
  kind : V → τ

/-- The predecessor sets used for pebbling. -/
def GateDAG.predSet {V τ : Type*} [DecidableEq V] (C : GateDAG V τ) (v : V) : Finset V :=
  (C.preds v).toFinset

/-- `(U, z_U, π)` is a predecessor-preserving partial unfolding of `(C, z)`: `π(z_U) = z`, every
vertex that is not a copy carrier is a clone (same gate type, and the labels of its ordered
predecessors are exactly the ordered predecessors of its label), and every copy carrier has a
unique predecessor with the same label. -/
def IsPPUnfolding {V W τ : Type*} (C : GateDAG V τ) (z : V) (U : GateDAG W τ) (zU : W)
    (π : W → V) (carrier : W → Bool) : Prop :=
  π zU = z ∧
  (∀ u, carrier u = false → U.kind u = C.kind (π u) ∧ (U.preds u).map π = C.preds (π u)) ∧
  (∀ u, carrier u = true → ∃ u', U.preds u = [u'] ∧ π u' = π u)

/-- Every vertex `u` of a predecessor-preserving partial unfolding computes the value of `π(u)`:
the values `valC ∘ π` satisfy the gate equations of `U` (clones evaluate their gate, copy
carriers copy their predecessor). -/
theorem unfolding_computes {V W τ : Type*} (C : GateDAG V τ) (z : V) (U : GateDAG W τ) (zU : W)
    (π : W → V) (carrier : W → Bool) (hU : IsPPUnfolding C z U zU π carrier)
    (ev : τ → List Bool → Bool) (valC : V → Bool)
    (hC : ∀ v, valC v = ev (C.kind v) ((C.preds v).map valC)) :
    (∀ u, carrier u = false →
      valC (π u) = ev (U.kind u) ((U.preds u).map (valC ∘ π))) ∧
    (∀ u, carrier u = true → ∃ u', U.preds u = [u'] ∧ valC (π u) = valC (π u')) ∧
    valC (π zU) = valC z := by
  sorry

/-- **Lemma 4.4 (pebbling projection).** If `U` is a predecessor-preserving partial unfolding of
`C`, every black pebbling of `U` projects to a black pebbling of `C` of no larger cost; hence
`Peb(C) ≤ Peb(U)`. -/
theorem pebbling_projection {V W τ : Type*} [DecidableEq V] [DecidableEq W] (C : GateDAG V τ)
    (z : V) (U : GateDAG W τ) (zU : W) (π : W → V) (carrier : W → Bool)
    (hU : IsPPUnfolding C z U zU π carrier) (P : Pebbling U.predSet zU) :
    ∃ Q : Pebbling C.predSet z, Q.cost ≤ P.cost := by
  sorry

/-- Predecessors in the quadrant grid on `ℕ × ℕ`: the north and west neighbours. -/
def quadPred (x : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  (if 1 ≤ x.1 then {(x.1 - 1, x.2)} else ∅) ∪ (if 1 ≤ x.2 then {(x.1, x.2 - 1)} else ∅)

/-- The grid gate DAG `C_g` on `x_{i,j}`, `0 ≤ i, j < g`: `x_{i,j}` reads its north neighbour
`x_{i-1,j}` and its west neighbour `x_{i,j-1}`; top-row and left-column gates read their unique
predecessor twice, and `x_{0,0}` is a source. The gate types are arbitrary. -/
def gridDAG {τ : Type*} (g : ℕ) (kind : Fin g × Fin g → τ) : GateDAG (Fin g × Fin g) τ where
  preds := fun x =>
    if h1 : 1 ≤ x.1.val then
      if h2 : 1 ≤ x.2.val then
        [(⟨x.1.val - 1, by omega⟩, x.2), (x.1, ⟨x.2.val - 1, by omega⟩)]
      else [(⟨x.1.val - 1, by omega⟩, x.2), (⟨x.1.val - 1, by omega⟩, x.2)]
    else
      if h2 : 1 ≤ x.2.val then [(x.1, ⟨x.2.val - 1, by omega⟩), (x.1, ⟨x.2.val - 1, by omega⟩)]
      else []
  kind := kind

/-- The output gate `x_{g-1,g-1}` of `C_g`. -/
def gridOut (g : ℕ) (hg : 1 ≤ g) : Fin g × Fin g := (⟨g - 1, by omega⟩, ⟨g - 1, by omega⟩)

section GridLower

variable (g : ℕ)

/-- A monotone staircase path of the pyramid `T = {i + j ≥ g - 1}` from its base to the apex,
given by its row coordinates `A ℓ` at the levels `ℓ = 0, …, g-1`; the vertex at level `ℓ` is
`(A ℓ, g - 1 + ℓ - A ℓ)`. -/
def IsStair (A : ℕ → ℕ) : Prop :=
  (∀ ℓ, ℓ < g - 1 → A (ℓ + 1) = A ℓ ∨ A (ℓ + 1) = A ℓ + 1) ∧ A (g - 1) = g - 1

/-- The vertex of a staircase at level `ℓ`. -/
def stairVtx (A : ℕ → ℕ) (ℓ : ℕ) : ℕ × ℕ := (A ℓ, g - 1 + ℓ - A ℓ)

/-- A configuration is blocking if every base-to-apex staircase carries a pebble. -/
def Blocking (S : Finset (ℕ × ℕ)) : Prop :=
  ∀ A, IsStair g A → ∃ ℓ, ℓ ≤ g - 1 ∧ stairVtx g A ℓ ∈ S

variable {g}

/-- The staircases from the other base vertices: from `(a, g - 1 - a)` go down the column until
the path `A` is met (if `a < A 0`), or along the row until it is met (if `a > A 0`). -/
def detour (A : ℕ → ℕ) (a : ℕ) : ℕ → ℕ :=
  fun ℓ => if a < A 0 then min (a + ℓ) (A ℓ) else max a (A ℓ)

end GridLower

/-- **Lemma 4.8 (lower bound).** For `g ≥ 2`, every black pebbling of the grid `Q_g` with target
`x_{g-1,g-1}` has cost at least `g + 1`. -/
theorem grid_pebbling_lower {τ : Type*} (g : ℕ) (hg : 2 ≤ g) (kind : Fin g × Fin g → τ)
    (P : Pebbling (gridDAG g kind).predSet (gridOut g (by omega))) : g + 1 ≤ P.cost := by
  sorry

/-- **Lemmas 4.4 and 4.8 combined.** For `g ≥ 2`, every black pebbling of every
predecessor-preserving partial unfolding of the grid circuit `C_g` has cost at least `g + 1`. -/
theorem grid_unfolding_pebbling_lower {τ W : Type*} [DecidableEq W] (g : ℕ) (hg : 2 ≤ g)
    (kind : Fin g × Fin g → τ) (U : GateDAG W τ) (zU : W) (π : W → Fin g × Fin g)
    (carrier : W → Bool)
    (hU : IsPPUnfolding (gridDAG g kind) (gridOut g (by omega)) U zU π carrier)
    (P : Pebbling U.predSet zU) : g + 1 ≤ P.cost := by
  sorry

/-- The configuration at time `t` of the row-by-row strategy: first row `0` is pebbled from left
to right; then, writing `t = g + 2m + ph` and `m = r g + c`, the pebbles are on
`x_{r+1,j}` (`j < c`), on `x_{r,j}` (`j ≥ c`), and on `x_{r+1,c}` if `ph = 1`. -/
def rowMem (g t i j : ℕ) : Prop :=
  if t < g then i = 0 ∧ j < t
  else (i = (t - g) / 2 / g + 1 ∧ j < (t - g) / 2 % g) ∨
    (i = (t - g) / 2 / g ∧ (t - g) / 2 % g ≤ j) ∨
    ((t - g) % 2 = 1 ∧ i = (t - g) / 2 / g + 1 ∧ j = (t - g) / 2 % g)

instance (g t i j : ℕ) : Decidable (rowMem g t i j) := by unfold rowMem; infer_instance

/-- The configurations of the row-by-row strategy. -/
def rowConf (g t : ℕ) : Finset (Fin g × Fin g) :=
  Finset.univ.filter (fun x => rowMem g t x.1.val x.2.val)

/-- **Lemma 4.8 (upper bound).** For `g ≥ 2`, the grid `Q_g` has a black pebbling of cost at
most `g + 1`. -/
theorem grid_pebbling_upper {τ : Type*} (g : ℕ) (hg : 2 ≤ g) (kind : Fin g × Fin g → τ) :
    ∃ P : Pebbling (gridDAG g kind).predSet (gridOut g (by omega)), P.cost ≤ g + 1 := by
  sorry

/-- The black pebbling price `Peb(D)`: the least cost of a black pebbling. -/
noncomputable def pebblingPrice {V : Type*} [DecidableEq V] (pred : V → Finset V) (t : V) : ℕ :=
  sInf {c | ∃ P : Pebbling pred t, P.cost = c}

/-- **Lemma 4.8 (grid pebbling price).** For `g ≥ 2`, `Peb(Q_g) = g + 1`. -/
theorem grid_pebblingPrice {τ : Type*} (g : ℕ) (hg : 2 ≤ g) (kind : Fin g × Fin g → τ) :
    pebblingPrice (gridDAG g kind).predSet (gridOut g (by omega)) = g + 1 := by
  sorry

end GC.StructuralCompilers
