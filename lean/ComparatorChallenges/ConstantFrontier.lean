import Mathlib.Data.Nat.Find
import Mathlib.Order.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.Group.Equiv.Basic

/-!
# Comparator challenge: constant-frontier computations (010c)

Self-contained copy of the definitions used by the statements, with the main theorems
stated `:= by sorry`. Solution module: `GC.Computability.Tabulation.Main`.
-/

namespace GC.Tabulation

/-- A normalized append-only machine.  `Option W` stands for `W ∪ {⊥}` (`none = ⊥`).
Stage `s ≥ 1` writes the cell `wr(s) = m + s - 1`.  The initial history is `Hin 0, …,
Hin (m-1)`; values of `Hin` at other indices are never used. -/
structure AppendMachine (Q W : Type*) where
  /-- length of the initial history -/
  m : ℕ
  /-- the initial history -/
  Hin : ℕ → W
  /-- the start configuration -/
  C0 : Q
  /-- the read-address map -/
  p : Q → ℤ
  /-- the written-word map -/
  w : Q → W
  /-- the transition maps `Φ_t` -/
  Φ : ℕ → Q → Option W → Q

namespace AppendMachine

variable {Q W : Type*} (M : AppendMachine Q W)

/-- The read result `h_Z(t, a)` at stage `t` for address `a`, answering internal reads from the
transcript `Z` (the cell `wr(s) = m + s - 1`, `1 ≤ s < t`, holds `w(Z_{s-1})`). -/
def read (Z : ℕ → Q) (t : ℕ) (a : ℤ) : Option W :=
  if 0 ≤ a ∧ a < M.m then some (M.Hin a.toNat)
  else if (M.m : ℤ) ≤ a ∧ a < M.m + t - 1 then some (M.w (Z (a - M.m).toNat))
  else none

/-- The real execution `C*`. -/
def real : ℕ → Q
  | 0 => M.C0
  | t + 1 =>
    M.Φ (t + 1) (real t)
      (if 0 ≤ M.p (real t) ∧ M.p (real t) < M.m then some (M.Hin (M.p (real t)).toNat)
       else if _h : (M.m : ℤ) ≤ M.p (real t) ∧ M.p (real t) < M.m + t then
         some (M.w (real (M.p (real t) - M.m).toNat))
       else none)
termination_by t => t
decreasing_by all_goals omega

/-- The read at stage `t ≥ 1` is internal (with writer `s = (p(C*_{t-1}) - m) + 1`). -/
def IsInternal (t : ℕ) : Prop :=
  (M.m : ℤ) ≤ M.p (M.real (t - 1)) ∧ M.p (M.real (t - 1)) < M.m + t - 1

/-- The writer `s(t)` of stage `t` when its real read is internal (`none` otherwise, and for
`t = 0`). -/
noncomputable def writer (t : ℕ) : Option ℕ :=
  open Classical in
  if t ≠ 0 ∧ M.IsInternal t then some ((M.p (M.real (t - 1)) - M.m).toNat + 1) else none

end AppendMachine

section Greedy

open Classical

/-- The largest `b ≤ N` such that `(a, b]` is an admissible piece. -/
noncomputable def reach (ok : ℕ → ℕ → Prop) (N a : ℕ) : ℕ := Nat.findGreatest (fun b => ok a b) N

/-- The greedy cover: `g_0 = 0`, `g_{k+1} = reach(g_k)` while `g_k < N`. -/
noncomputable def greedySeq (ok : ℕ → ℕ → Prop) (N : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => if greedySeq ok N k < N then reach ok N (greedySeq ok N k) else greedySeq ok N k

end Greedy

end GC.Tabulation

namespace GC.Tabulation

namespace AppendMachine

variable {Q W : Type*} (M : AppendMachine Q W)

open Classical

/-- The live set `L^{a,b}_t`: cells written at stages `s ∈ (a, t]` that are read (by an internal
real read with writer `s`) at some stage `i ∈ (t, b]`. This is the paper's
`{s : a < s ≤ t < ℓ_{a,b}(s)}`, since for `s ≤ t`, `t < ℓ_{a,b}(s)` iff such an `i` exists. -/
noncomputable def liveSet (a b t : ℕ) : Finset ℕ :=
  (Finset.Ioc a t).filter (fun s => ∃ i, t < i ∧ i ≤ b ∧ M.writer i = some s)

/-- The internal live frontier `f(a, b) = max_{a ≤ t ≤ b} |L^{a,b}_t|`. -/
noncomputable def frontier (a b : ℕ) : ℕ := (Finset.Icc a b).sup (fun t => (M.liveSet a b t).card)

/-- **Lemma 2.3 (monotonicity), first part.** `f(a, b) ≤ f(a, b')` for `b ≤ b'`. -/
theorem frontier_mono {a b b' : ℕ} (h : b ≤ b') : M.frontier a b ≤ M.frontier a b' := by
  sorry

/-- **Lemma 2.3 (monotonicity), second part.** `f(a, a + 1) = 0`. -/
theorem frontier_succ_eq_zero (a : ℕ) : M.frontier a (a + 1) = 0 := by
  sorry

/-- **Lemma 4.1 (restartability), frontier form.** `f(c, b) ≤ f(a, b)` for `a ≤ c`. -/
theorem frontier_restart {a c b : ℕ} (hac : a ≤ c) : M.frontier c b ≤ M.frontier a b := by
  sorry

/-- The end `e_f(a) = max {b ∈ [a, N] : f(a, b) ≤ f}` of the maximal `f`-frontier epoch from `a`
(Theorem 3.5); it is the `reach` of the admissibility predicate `f(a, b) ≤ f`. -/
noncomputable def epochEnd (f N a : ℕ) : ℕ := reach (fun a b => M.frontier a b ≤ f) N a

/-- **Lemma 4.1 (restartability).** If `a < c ≤ e_f(a)`, then `e_f(c) ≥ e_f(a)`. -/
theorem epochEnd_restart (f N : ℕ) {a c : ℕ} (hac : a < c) (hce : c ≤ M.epochEnd f N a)
    (hN : a < N) : M.epochEnd f N a ≤ M.epochEnd f N c := by
  sorry

/-- **Lemma 4.2 (packing).** Every maximal `f`-frontier epoch `(a, e_f(a)]` other than the last
(`e_f(a) < N`) has at least `f + 1` stages. -/
theorem epoch_packing (f N a : ℕ) (hN : a < N) (he : M.epochEnd f N a < N) :
    a + f + 1 ≤ M.epochEnd f N a := by
  sorry

/-- **Proposition 4.4 (the greedy cover is minimal).** If `0 = c_0 < c_1 < ⋯ < c_k = N` with
`f(c_j, c_{j+1}) ≤ f` for all `j`, the greedy cover by maximal epochs `a_{j+1} = e_f(a_j)` reaches
`N` after at most `k` epochs: `K_f ≤ k`. -/
theorem epoch_greedy_optimal (f N : ℕ) (c : ℕ → ℕ) (k : ℕ) (hc0 : c 0 = 0) (hck : c k = N)
    (hc : ∀ j < k, c j < c (j + 1) ∧ M.frontier (c j) (c (j + 1)) ≤ f) :
    greedySeq (fun a b => M.frontier a b ≤ f) N k = N := by
  sorry

/-- The read result `ĥ` of the compact configuration `(t, c, D)` at stage `i = a + t + 1`;
the outer `none` means *undefined* (an internal read of a cell written after `a` that is not in
the dictionary). The known history is the real history up to stage `a`. -/
noncomputable def hatRead (a t : ℕ) (c : Q) (D : ℕ → Option W) : Option (Option W) :=
  if 0 ≤ M.p c ∧ M.p c < M.m then some (some (M.Hin (M.p c).toNat))
  else if (M.m : ℤ) ≤ M.p c ∧ M.p c < M.m + a then
    some (some (M.w (M.real (M.p c - M.m).toNat)))
  else if (M.m : ℤ) + a ≤ M.p c ∧ M.p c < M.m + a + t then
    (D ((M.p c - M.m).toNat + 1)).map some
  else some none

omit M in
/-- The number of entries of a dictionary at layer `t` (entries are keyed by `s ∈ (a, a + t]`). -/
noncomputable def dictCard (a t : ℕ) (D : ℕ → Option W) : ℕ :=
  ((Finset.Ioc a (a + t)).filter (fun s => D s ≠ none)).card

/-- An edge of `𝒞_{a,h,f}` from `(t, c, D)` to `(t + 1, c', D')`: the read result is defined,
`c' = Φ_i(c, ĥ)`, `D' ⊆ D ∪ {(i, w(c))}` and `|D'| ≤ f`, where `i = a + t + 1`. -/
def Edge (a f t : ℕ) (c : Q) (D : ℕ → Option W) (c' : Q) (D' : ℕ → Option W) : Prop :=
  ∃ h, M.hatRead a t c D = some h ∧ c' = M.Φ (a + t + 1) c h ∧
    (∀ s, D' s = none ∨ D' s = Function.update D (a + t + 1) (some (M.w c)) s) ∧
    dictCard a (t + 1) D' ≤ f

/-- Layer `t` of `𝒞_{a,h,f}` (`t ≤ h`) is reachable from the start node `(0, C*_a, ∅)`. -/
def LayerReachable (a f t : ℕ) : Prop :=
  ∃ (c : ℕ → Q) (D : ℕ → ℕ → Option W), c 0 = M.real a ∧ (∀ s, D 0 s = none) ∧
    ∀ k < t, M.Edge a f k (c k) (D k) (c (k + 1)) (D (k + 1))

/-- **Lemma 3.2 (reachable nodes are exact).** Along a path from the start node, every node
carries the real configuration, every dictionary entry is the real written word, and dictionary
keys of layer `k` lie in `(a, a + k]`. -/
theorem reachable_exact (a f t : ℕ) (c : ℕ → Q) (D : ℕ → ℕ → Option W) (hc0 : c 0 = M.real a)
    (hD0 : ∀ s, D 0 s = none)
    (hpath : ∀ k < t, M.Edge a f k (c k) (D k) (c (k + 1)) (D (k + 1))) :
    ∀ k ≤ t, c k = M.real (a + k) ∧ (∀ s v, D k s = some v → v = M.w (M.real (s - 1))) ∧
      (∀ s, D k s ≠ none → a < s ∧ s ≤ a + k) := by
  sorry

/-- **Lemma 3.3 (path–frontier equivalence).** Layer `t` of the compact-configuration graph is
reachable iff the internal live frontier of `(a, a + t]` is at most `f`. -/
theorem layer_reachable_iff (a f t : ℕ) :
    M.LayerReachable a f t ↔ M.frontier a (a + t) ≤ f := by
  sorry

/-- **Theorem 3.5, exact criterion.** For `a + t ≤ N`, layer `t` of the compact-configuration
graph from the boundary `a` is reachable iff `a + t ≤ e_f(a)`: the reachable layers form the
initial interval `[0, e_f(a) - a]`. -/
theorem layer_reachable_iff_le_epochEnd (f N a t : ℕ) (ht : a + t ≤ N) :
    M.LayerReachable a f t ↔ a + t ≤ M.epochEnd f N a := by
  sorry

/-- **Corollary 3.6 (constant-frontier executions), exactness part.** If `f(0, N) ≤ f`, layer `N`
of the compact-configuration graph from the start is reachable, and along every path to it each
node carries the real configuration `C*_t`. -/
theorem constant_frontier_trace (f N : ℕ) (hf : M.frontier 0 N ≤ f) :
    M.LayerReachable 0 f N ∧
      ∀ (c : ℕ → Q) (D : ℕ → ℕ → Option W), c 0 = M.real 0 → (∀ s, D 0 s = none) →
        (∀ k < N, M.Edge 0 f k (c k) (D k) (c (k + 1)) (D (k + 1))) → ∀ k ≤ N, c k = M.real k := by
  sorry

end AppendMachine

section MovingFrame

variable {X : Type*} (G : ℕ → Equiv.Perm X) (E : ℕ → X → X)

/-- The trajectory `x_t = E_t(G_t(x_{t-1}))`. -/
def traj (x0 : X) : ℕ → X
  | 0 => x0
  | t + 1 => E (t + 1) (G (t + 1) (traj x0 t))

/-- The prefix products `P_0 = id`, `P_t = G_t ∘ P_{t-1}`. -/
def prefixPerm : ℕ → Equiv.Perm X
  | 0 => 1
  | t + 1 => G (t + 1) * prefixPerm t

/-- The conjugated exception map `Ê_t = P_t⁻¹ ∘ E_t ∘ P_t`. -/
def conjExc (t : ℕ) (y : X) : X := (prefixPerm G t)⁻¹ (E t (prefixPerm G t y))

/-- **Lemma 5.3 (moving-frame conjugation).** In the moving frame `y_t = P_t⁻¹(x_t)`, the base
motions disappear: `y_t = Ê_t(y_{t-1})`, and `x_t = P_t(y_t)`. -/
theorem moving_frame (x0 : X) (t : ℕ) :
    (prefixPerm G (t + 1))⁻¹ (traj G E x0 (t + 1)) =
      conjExc G E (t + 1) ((prefixPerm G t)⁻¹ (traj G E x0 t)) := by
  sorry

/-- **Lemma 5.3, support.** `Ê_t` moves `y` iff `E_t` moves `P_t(y)`, and then
`Ê_t(y) = P_t⁻¹(E_t(P_t y))`: the exception list of `Ê_t` is the image of that of `E_t` under
`(u, v) ↦ (P_t⁻¹ u, P_t⁻¹ v)`. -/
theorem conjExc_moves_iff (t : ℕ) (y : X) :
    conjExc G E t y ≠ y ↔ E t (prefixPerm G t y) ≠ prefixPerm G t y := by
  sorry

end MovingFrame

section EventChain

variable {X : Type*} (F : ℕ → X → X) (y : ℕ → X) (hy : ∀ t, y (t + 1) = F (t + 1) (y t))

include hy

/-- **Theorem 5.4 (exact event chain), one link.** The state stays `y_{t_0}` until the first
later time `t_1 > t_0` at which an event has source `y_{t_0}`, and then becomes its target:
if no `t' ∈ (t_0, t]` has `F_{t'}(y_{t_0}) ≠ y_{t_0}` then `y_t = y_{t_0}`. -/
theorem event_chain_stay (t0 : ℕ) :
    ∀ t, t0 ≤ t → (∀ t', t0 < t' → t' ≤ t → F t' (y t0) = y t0) → y t = y t0 := by
  sorry

/-- **Theorem 5.4, the successor event.** If `t_1 > t_0` is the least time with an event whose
source is `y_{t_0}`, then `y_t = y_{t_0}` for `t_0 ≤ t < t_1` and `y_{t_1} = F_{t_1}(y_{t_0})`. -/
theorem event_chain_next (t0 t1 : ℕ) (h01 : t0 < t1)
    (hmin : ∀ t', t0 < t' → t' < t1 → F t' (y t0) = y t0) :
    (∀ t, t0 ≤ t → t < t1 → y t = y t0) ∧ y t1 = F t1 (y t0) := by
  sorry

end EventChain

section CycleTransposition

variable {n : ℕ}

/-- The cycle `c(x) = x + 1` on `ℤ/n`. -/
def cycleZ : Equiv.Perm (ZMod n) := Equiv.addRight 1

/-- The conjugate `c^{-r} τ c^r` of the transposition `τ = (0 1)` is the transposition of
`-r` and `1 - r`. -/
theorem conj_cycle_swap (r : ℕ) :
    (cycleZ ^ r)⁻¹ * Equiv.swap (0 : ZMod n) 1 * cycleZ ^ r = Equiv.swap (-(r : ZMod n)) (1 - r) := by
  sorry

/-- **Corollary 5.9 (cycle-plus-transposition trajectories), formula.** For a word over
`{c, τ}` (`g t = true` for `c`, `false` for `τ`), let `r_t` be the number of letters `c` among
`g_1, …, g_t`. Then `x_t = y_t + r_t`, where `y` changes only at letters `τ`, by the transposition
of `-r_t` and `1 - r_t`. -/
theorem cycle_transposition_traj (g : ℕ → Bool) (x : ℕ → ZMod n)
    (hx : ∀ t, x (t + 1) = if g (t + 1) then x t + 1 else Equiv.swap (0 : ZMod n) 1 (x t))
    (r : ℕ → ℕ) (hr0 : r 0 = 0) (hr : ∀ t, r (t + 1) = if g (t + 1) then r t + 1 else r t)
    (y : ℕ → ZMod n) (hy0 : y 0 = x 0)
    (hy : ∀ t, y (t + 1) =
      if g (t + 1) then y t else Equiv.swap (-(r (t + 1) : ZMod n)) (1 - r (t + 1)) (y t)) :
    ∀ t, x t = y t + r t := by
  sorry

end CycleTransposition

end GC.Tabulation
