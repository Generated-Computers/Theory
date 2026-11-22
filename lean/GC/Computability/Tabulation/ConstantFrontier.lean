import GC.Computability.Tabulation.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.Group.Equiv.Basic

/-!
# Constant-frontier computations (manuscript 010c)

Part 1: the internal live frontier of an append-only machine, the compact-configuration graph,
exactness of reachable nodes, the path–frontier equivalence, monotonicity, restartability,
packing and the minimality of the greedy epoch cover.

Part 2: moving-frame sparse events: the moving-frame conjugation lemma, the event-chain step,
and the cycle-plus-transposition formula.

Reachability is an existential statement about paths; its NC/PRAM evaluation (Boolean matrix
squaring, Borodin's theorem) is not formalized.
-/

namespace GC.Tabulation

namespace AppendMachine

variable {Q W : Type*} (M : AppendMachine Q W)

open Classical

/-! ### The internal live frontier (Definition 2.2) -/

/-- The live set `L^{a,b}_t`: cells written at stages `s ∈ (a, t]` that are read (by an internal
real read with writer `s`) at some stage `i ∈ (t, b]`. This is the paper's
`{s : a < s ≤ t < ℓ_{a,b}(s)}`, since for `s ≤ t`, `t < ℓ_{a,b}(s)` iff such an `i` exists. -/
noncomputable def liveSet (a b t : ℕ) : Finset ℕ :=
  (Finset.Ioc a t).filter (fun s => ∃ i, t < i ∧ i ≤ b ∧ M.writer i = some s)

/-- The internal live frontier `f(a, b) = max_{a ≤ t ≤ b} |L^{a,b}_t|`. -/
noncomputable def frontier (a b : ℕ) : ℕ := (Finset.Icc a b).sup (fun t => (M.liveSet a b t).card)

lemma frontier_le_iff (a b f : ℕ) :
    M.frontier a b ≤ f ↔ ∀ t, a ≤ t → t ≤ b → (M.liveSet a b t).card ≤ f := by
  simp [frontier, Finset.sup_le_iff]

/-- **Lemma 2.3 (monotonicity), first part.** `f(a, b) ≤ f(a, b')` for `b ≤ b'`. -/
theorem frontier_mono {a b b' : ℕ} (h : b ≤ b') : M.frontier a b ≤ M.frontier a b' := by
  rw [frontier_le_iff]
  intro t ht1 ht2
  refine le_trans (Finset.card_le_card ?_) ((M.frontier_le_iff a b' _).mp le_rfl t ht1 (by omega))
  intro s hs
  simp only [liveSet, Finset.mem_filter] at hs ⊢
  obtain ⟨hs1, i, hi1, hi2, hi3⟩ := hs
  exact ⟨hs1, i, hi1, by omega, hi3⟩

/-- **Lemma 2.3 (monotonicity), second part.** `f(a, a + 1) = 0`. -/
theorem frontier_succ_eq_zero (a : ℕ) : M.frontier a (a + 1) = 0 := by
  apply Nat.eq_zero_of_le_zero
  rw [frontier_le_iff]
  intro t ht1 ht2
  simp only [Nat.le_zero, Finset.card_eq_zero]
  ext s
  simp only [liveSet, Finset.mem_filter, Finset.mem_Ioc, Finset.notMem_empty, iff_false]
  rintro ⟨⟨h1, h2⟩, i, hi1, hi2, _⟩
  omega

/-- **Lemma 4.1 (restartability), frontier form.** `f(c, b) ≤ f(a, b)` for `a ≤ c`. -/
theorem frontier_restart {a c b : ℕ} (hac : a ≤ c) : M.frontier c b ≤ M.frontier a b := by
  rw [frontier_le_iff]
  intro t ht1 ht2
  refine le_trans (Finset.card_le_card ?_) ((M.frontier_le_iff a b _).mp le_rfl t (by omega) ht2)
  intro s hs
  simp only [liveSet, Finset.mem_filter, Finset.mem_Ioc] at hs ⊢
  obtain ⟨⟨hs1, hs2⟩, rest⟩ := hs
  exact ⟨⟨by omega, hs2⟩, rest⟩

/-- The end `e_f(a) = max {b ∈ [a, N] : f(a, b) ≤ f}` of the maximal `f`-frontier epoch from `a`
(Theorem 3.5); it is the `reach` of the admissibility predicate `f(a, b) ≤ f`. -/
noncomputable def epochEnd (f N a : ℕ) : ℕ := reach (fun a b => M.frontier a b ≤ f) N a

/-- **Lemma 4.1 (restartability).** If `a < c ≤ e_f(a)`, then `e_f(c) ≥ e_f(a)`. -/
theorem epochEnd_restart (f N : ℕ) {a c : ℕ} (hac : a < c) (hce : c ≤ M.epochEnd f N a)
    (hN : a < N) : M.epochEnd f N a ≤ M.epochEnd f N c := by
  have hspec : M.frontier a (M.epochEnd f N a) ≤ f :=
    reach_spec (fun a b => M.frontier a b ≤ f) (b := a + 1) (by omega)
      (by show M.frontier a (a + 1) ≤ f; rw [M.frontier_succ_eq_zero]; omega)
  exact le_reach (fun a b => M.frontier a b ≤ f) (reach_le _ N a)
    ((M.frontier_restart hac.le).trans hspec)

/-- **Lemma 4.2 (packing).** Every maximal `f`-frontier epoch `(a, e_f(a)]` other than the last
(`e_f(a) < N`) has at least `f + 1` stages. -/
theorem epoch_packing (f N a : ℕ) (hN : a < N) (he : M.epochEnd f N a < N) :
    a + f + 1 ≤ M.epochEnd f N a := by
  set e := M.epochEnd f N a with he_def
  have hae : a + 1 ≤ e := le_reach (fun a b => M.frontier a b ≤ f) (by omega)
    (by show M.frontier a (a + 1) ≤ f; rw [M.frontier_succ_eq_zero]; omega)
  have hnot : ¬ M.frontier a (e + 1) ≤ f :=
    not_ok_of_reach_lt (fun a b => M.frontier a b ≤ f) (N := N) (b := e + 1)
      (by rw [he_def]; exact Nat.lt_succ_self _) (by omega)
  rw [frontier_le_iff] at hnot
  push_neg at hnot
  obtain ⟨t, ht1, ht2, hcard⟩ := hnot
  have hte : t ≤ e := by
    by_contra hte
    have : M.liveSet a (e + 1) t = ∅ := by
      ext s
      simp only [liveSet, Finset.mem_filter, Finset.notMem_empty, iff_false]
      rintro ⟨_, i, hi1, hi2, _⟩
      omega
    rw [this] at hcard
    simp at hcard
  have hsub : M.liveSet a (e + 1) t ⊆ Finset.Ioc a e := by
    intro s hs
    simp only [liveSet, Finset.mem_filter, Finset.mem_Ioc] at hs ⊢
    omega
  have := (Finset.card_le_card hsub).trans_lt' hcard
  simp at this
  omega

/-- **Proposition 4.4 (the greedy cover is minimal).** If `0 = c_0 < c_1 < ⋯ < c_k = N` with
`f(c_j, c_{j+1}) ≤ f` for all `j`, the greedy cover by maximal epochs `a_{j+1} = e_f(a_j)` reaches
`N` after at most `k` epochs: `K_f ≤ k`. -/
theorem epoch_greedy_optimal (f N : ℕ) (c : ℕ → ℕ) (k : ℕ) (hc0 : c 0 = 0) (hck : c k = N)
    (hc : ∀ j < k, c j < c (j + 1) ∧ M.frontier (c j) (c (j + 1)) ≤ f) :
    greedySeq (fun a b => M.frontier a b ≤ f) N k = N := by
  apply greedy_optimal _ N _ _ c k hc0 hck hc
  · intro a a' b hab haa' _
    exact (M.frontier_restart haa').trans hab
  · intro a
    rw [M.frontier_succ_eq_zero]; omega

/-! ### The compact-configuration graph (Definition 3.1) -/

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

/-- With an exact dictionary, a defined read result of the real configuration is the real read
result. -/
lemma hatRead_exact (a k : ℕ) (D : ℕ → Option W)
    (hD : ∀ s v, D s = some v → v = M.w (M.real (s - 1))) (h : Option W)
    (hh : M.hatRead a k (M.real (a + k)) D = some h) :
    h = M.read M.real (a + k + 1) (M.p (M.real (a + k))) := by
  rw [read_succ]
  simp only [hatRead] at hh
  by_cases h1 : 0 ≤ M.p (M.real (a + k)) ∧ M.p (M.real (a + k)) < M.m
  · rw [if_pos h1] at hh ⊢
    simp only [Option.some.injEq] at hh
    exact hh.symm
  · rw [if_neg h1] at hh ⊢
    by_cases h2 : (M.m : ℤ) ≤ M.p (M.real (a + k)) ∧ M.p (M.real (a + k)) < M.m + a
    · rw [if_pos h2] at hh
      rw [if_pos ⟨h2.1, by push_cast; omega⟩]
      simp only [Option.some.injEq] at hh
      exact hh.symm
    · rw [if_neg h2] at hh
      by_cases h3 : (M.m : ℤ) + a ≤ M.p (M.real (a + k)) ∧ M.p (M.real (a + k)) < M.m + a + k
      · rw [if_pos h3] at hh
        rw [if_pos ⟨by omega, by push_cast; omega⟩]
        obtain ⟨v, hv1, hv2⟩ := Option.map_eq_some_iff.mp hh
        rw [← hv2, hD _ _ hv1]
        congr 3
      · rw [if_neg h3] at hh
        rw [if_neg (by push_cast; omega)]
        simp only [Option.some.injEq] at hh
        exact hh.symm

/-- **Lemma 3.2 (reachable nodes are exact).** Along a path from the start node, every node
carries the real configuration, every dictionary entry is the real written word, and dictionary
keys of layer `k` lie in `(a, a + k]`. -/
theorem reachable_exact (a f t : ℕ) (c : ℕ → Q) (D : ℕ → ℕ → Option W) (hc0 : c 0 = M.real a)
    (hD0 : ∀ s, D 0 s = none)
    (hpath : ∀ k < t, M.Edge a f k (c k) (D k) (c (k + 1)) (D (k + 1))) :
    ∀ k ≤ t, c k = M.real (a + k) ∧ (∀ s v, D k s = some v → v = M.w (M.real (s - 1))) ∧
      (∀ s, D k s ≠ none → a < s ∧ s ≤ a + k) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨by simpa using hc0, fun s v h => by simp [hD0] at h, fun s h => absurd (hD0 s) h⟩
  | succ k ih =>
    intro hk
    obtain ⟨hck, hDk, hsupp⟩ := ih (by omega)
    obtain ⟨h, hh, hc', hD', _⟩ := hpath k (by omega)
    rw [hck] at hh hc' hD'
    have hread := M.hatRead_exact a k (D k) hDk h hh
    refine ⟨?_, ?_, ?_⟩
    · rw [hc', hread, ← add_assoc, real_succ]
    · intro s v hv
      rcases hD' s with h1 | h1
      · rw [h1] at hv; simp at hv
      · rw [h1] at hv
        by_cases hs : s = a + k + 1
        · subst hs
          simp only [Function.update_self, Option.some.injEq] at hv
          rw [← hv]; congr 2
        · rw [Function.update_of_ne hs] at hv
          exact hDk s v hv
    · intro s hs
      rcases hD' s with h1 | h1
      · exact absurd h1 hs
      · rw [h1] at hs
        by_cases hs' : s = a + k + 1
        · omega
        · rw [Function.update_of_ne hs'] at hs
          have := hsupp s hs
          omega

/-- **Lemma 3.3 (path–frontier equivalence).** Layer `t` of the compact-configuration graph is
reachable iff the internal live frontier of `(a, a + t]` is at most `f`. -/
theorem layer_reachable_iff (a f t : ℕ) :
    M.LayerReachable a f t ↔ M.frontier a (a + t) ≤ f := by
  constructor
  · rintro ⟨c, D, hc0, hD0, hpath⟩
    have hex := M.reachable_exact a f t c D hc0 hD0 hpath
    rw [frontier_le_iff]
    intro t' ht1 ht2
    obtain ⟨k, rfl⟩ : ∃ k, t' = a + k := ⟨t' - a, by omega⟩
    -- every live cell is in the dictionary of layer `k`
    have hsub : M.liveSet a (a + t) (a + k) ⊆
        (Finset.Ioc a (a + k)).filter (fun s => D k s ≠ none) := by
      intro s hs
      simp only [liveSet, Finset.mem_filter, Finset.mem_Ioc] at hs ⊢
      obtain ⟨⟨hs1, hs2⟩, i, hi1, hi2, hi3⟩ := hs
      refine ⟨⟨hs1, hs2⟩, ?_⟩
      obtain ⟨k', rfl⟩ : ∃ k', i = a + k' + 1 := ⟨i - a - 1, by omega⟩
      -- the dictionary of layer `k'` contains `s`
      have hk' : D k' s ≠ none := by
        obtain ⟨h, hh, -⟩ := hpath k' (by omega)
        rw [(hex k' (by omega)).1] at hh
        unfold writer IsInternal at hi3
        split_ifs at hi3 with hw
        simp only [Option.some.injEq] at hi3
        simp only [show a + k' + 1 - 1 = a + k' by omega] at hw hi3
        simp only [hatRead] at hh
        rw [if_neg (by omega), if_neg (by omega), if_pos (by push_cast at hw; omega)] at hh
        rw [hi3] at hh
        intro hnone
        rw [hnone] at hh
        simp at hh
      -- dictionary entries persist backwards from layer `k'` to layer `k`
      have back : ∀ n, n ≤ k' - k → D (k' - n) s ≠ none := by
        intro n
        induction n with
        | zero => intro _; simpa using hk'
        | succ n ihn =>
          intro hn
          have h1 := ihn (by omega)
          obtain ⟨_, _, _, hD', _⟩ := hpath (k' - (n + 1)) (by omega)
          rw [show k' - (n + 1) + 1 = k' - n by omega] at hD'
          rcases hD' s with h2 | h2
          · exact absurd h2 h1
          · rw [h2, Function.update_of_ne (by omega)] at h1
            exact h1
      have := back (k' - k) le_rfl
      rwa [show k' - (k' - k) = k by omega] at this
    refine (Finset.card_le_card hsub).trans ?_
    rcases k with _ | k
    · simp
    · exact (hpath k (by omega)).choose_spec.2.2.2
  · intro hf
    rw [frontier_le_iff] at hf
    refine ⟨fun k => M.real (a + k),
      fun k s => if s ∈ M.liveSet a (a + t) (a + k) then some (M.w (M.real (s - 1))) else none,
      by simp, fun s => by simp [liveSet], ?_⟩
    intro k hk
    have hdefined : ∃ h, M.hatRead a k (M.real (a + k))
        (fun s => if s ∈ M.liveSet a (a + t) (a + k) then some (M.w (M.real (s - 1)))
          else none) = some h := by
      simp only [hatRead]
      by_cases h1 : 0 ≤ M.p (M.real (a + k)) ∧ M.p (M.real (a + k)) < M.m
      · rw [if_pos h1]; exact ⟨_, rfl⟩
      rw [if_neg h1]
      by_cases h2 : (M.m : ℤ) ≤ M.p (M.real (a + k)) ∧ M.p (M.real (a + k)) < M.m + a
      · rw [if_pos h2]; exact ⟨_, rfl⟩
      rw [if_neg h2]
      by_cases h3 : (M.m : ℤ) + a ≤ M.p (M.real (a + k)) ∧ M.p (M.real (a + k)) < M.m + a + k
      · rw [if_pos h3, if_pos]
        · exact ⟨_, rfl⟩
        · simp only [liveSet, Finset.mem_filter, Finset.mem_Ioc]
          refine ⟨⟨by omega, by omega⟩, a + k + 1, by omega, by omega, ?_⟩
          unfold writer IsInternal
          rw [if_pos ⟨by omega, by
            simp only [show a + k + 1 - 1 = a + k by omega]; push_cast; omega⟩]
          simp only [show a + k + 1 - 1 = a + k by omega]
      · rw [if_neg h3]; exact ⟨_, rfl⟩
    obtain ⟨h, hh⟩ := hdefined
    refine ⟨h, hh, ?_, ?_, ?_⟩
    · rw [M.hatRead_exact a k _ (fun s v hv => by
          split_ifs at hv
          simp only [Option.some.injEq] at hv; exact hv.symm) h hh]
      show M.real (a + (k + 1)) = _
      rw [← add_assoc, real_succ]
    · intro s
      by_cases hs : s ∈ M.liveSet a (a + t) (a + (k + 1))
      · right
        simp only [if_pos hs]
        by_cases hsi : s = a + k + 1
        · subst hsi
          simp only [Function.update_self]
          congr 2
        · rw [Function.update_of_ne hsi, if_pos]
          simp only [liveSet, Finset.mem_filter, Finset.mem_Ioc] at hs ⊢
          obtain ⟨⟨hs1, hs2⟩, i, hi1, hi2, hi3⟩ := hs
          exact ⟨⟨hs1, by omega⟩, i, by omega, hi2, hi3⟩
      · left; simp [hs]
    · refine le_trans (Finset.card_le_card ?_) (hf (a + (k + 1)) (by omega) (by omega))
      intro s hs
      simp only [Finset.mem_filter, ne_eq, ite_eq_right_iff, reduceCtorEq, imp_false,
        not_not] at hs
      exact hs.2

lemma frontier_self (a : ℕ) : M.frontier a a = 0 := by
  apply Nat.eq_zero_of_le_zero
  rw [frontier_le_iff]
  intro t ht1 ht2
  have : t = a := by omega
  subst this
  simp [liveSet]

/-- **Theorem 3.5, exact criterion.** For `a + t ≤ N`, layer `t` of the compact-configuration
graph from the boundary `a` is reachable iff `a + t ≤ e_f(a)`: the reachable layers form the
initial interval `[0, e_f(a) - a]`. -/
theorem layer_reachable_iff_le_epochEnd (f N a t : ℕ) (ht : a + t ≤ N) :
    M.LayerReachable a f t ↔ a + t ≤ M.epochEnd f N a := by
  rw [layer_reachable_iff]
  constructor
  · intro h
    exact le_reach (fun a b => M.frontier a b ≤ f) ht h
  · intro h
    have hspec : M.frontier a (M.epochEnd f N a) ≤ f :=
      reach_spec (fun a b => M.frontier a b ≤ f) (b := a) (by omega)
        (by show M.frontier a a ≤ f; rw [M.frontier_self]; omega)
    exact (M.frontier_mono h).trans hspec

/-- **Corollary 3.6 (constant-frontier executions), exactness part.** If `f(0, N) ≤ f`, layer `N`
of the compact-configuration graph from the start is reachable, and along every path to it each
node carries the real configuration `C*_t`. -/
theorem constant_frontier_trace (f N : ℕ) (hf : M.frontier 0 N ≤ f) :
    M.LayerReachable 0 f N ∧
      ∀ (c : ℕ → Q) (D : ℕ → ℕ → Option W), c 0 = M.real 0 → (∀ s, D 0 s = none) →
        (∀ k < N, M.Edge 0 f k (c k) (D k) (c (k + 1)) (D (k + 1))) → ∀ k ≤ N, c k = M.real k := by
  refine ⟨(M.layer_reachable_iff 0 f N).mpr (by simpa using hf), ?_⟩
  intro c D hc0 hD0 hpath k hk
  simpa using (M.reachable_exact 0 f N c D hc0 hD0 hpath k hk).1

end AppendMachine

/-! ### Part 2: moving-frame sparse events (Section 5) -/

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
  simp only [conjExc, traj, prefixPerm, Equiv.Perm.mul_apply, Equiv.Perm.coe_inv,
    Equiv.apply_symm_apply]

/-- **Lemma 5.3, support.** `Ê_t` moves `y` iff `E_t` moves `P_t(y)`, and then
`Ê_t(y) = P_t⁻¹(E_t(P_t y))`: the exception list of `Ê_t` is the image of that of `E_t` under
`(u, v) ↦ (P_t⁻¹ u, P_t⁻¹ v)`. -/
theorem conjExc_moves_iff (t : ℕ) (y : X) :
    conjExc G E t y ≠ y ↔ E t (prefixPerm G t y) ≠ prefixPerm G t y := by
  simp only [conjExc, ne_eq]
  rw [Equiv.Perm.inv_eq_iff_eq]

end MovingFrame

section EventChain

variable {X : Type*} (F : ℕ → X → X) (y : ℕ → X) (hy : ∀ t, y (t + 1) = F (t + 1) (y t))

include hy

/-- **Theorem 5.4 (exact event chain), one link.** The state stays `y_{t_0}` until the first
later time `t_1 > t_0` at which an event has source `y_{t_0}`, and then becomes its target:
if no `t' ∈ (t_0, t]` has `F_{t'}(y_{t_0}) ≠ y_{t_0}` then `y_t = y_{t_0}`. -/
theorem event_chain_stay (t0 : ℕ) :
    ∀ t, t0 ≤ t → (∀ t', t0 < t' → t' ≤ t → F t' (y t0) = y t0) → y t = y t0 := by
  intro t ht hno
  induction t, ht using Nat.le_induction with
  | base => rfl
  | succ t ht ih =>
    rw [hy, ih (fun t' h1 h2 => hno t' h1 (by omega)), hno (t + 1) (by omega) le_rfl]

/-- **Theorem 5.4, the successor event.** If `t_1 > t_0` is the least time with an event whose
source is `y_{t_0}`, then `y_t = y_{t_0}` for `t_0 ≤ t < t_1` and `y_{t_1} = F_{t_1}(y_{t_0})`. -/
theorem event_chain_next (t0 t1 : ℕ) (h01 : t0 < t1)
    (hmin : ∀ t', t0 < t' → t' < t1 → F t' (y t0) = y t0) :
    (∀ t, t0 ≤ t → t < t1 → y t = y t0) ∧ y t1 = F t1 (y t0) := by
  have stay : ∀ t, t0 ≤ t → t < t1 → y t = y t0 := fun t h1 h2 =>
    event_chain_stay F y hy t0 t h1 (fun t' a b => hmin t' a (by omega))
  refine ⟨stay, ?_⟩
  obtain ⟨t1', rfl⟩ : ∃ t1', t1 = t1' + 1 := ⟨t1 - 1, by omega⟩
  rw [hy, stay t1' (by omega) (by omega)]

end EventChain

/-! ### The cycle and the transposition (Corollary 5.9) -/

section CycleTransposition

variable {n : ℕ}

/-- The cycle `c(x) = x + 1` on `ℤ/n`. -/
def cycleZ : Equiv.Perm (ZMod n) := Equiv.addRight 1

/-- The conjugate `c^{-r} τ c^r` of the transposition `τ = (0 1)` is the transposition of
`-r` and `1 - r`. -/
theorem conj_cycle_swap (r : ℕ) :
    (cycleZ ^ r)⁻¹ * Equiv.swap (0 : ZMod n) 1 * cycleZ ^ r = Equiv.swap (-(r : ZMod n)) (1 - r) := by
  have hpow : ∀ x : ZMod n, (cycleZ ^ r) x = x + r := by
    intro x
    induction r generalizing x with
    | zero => simp
    | succ r ih =>
      rw [pow_succ, Equiv.Perm.mul_apply, ih]
      simp [cycleZ]; ring
  have hinv : ∀ x : ZMod n, (cycleZ ^ r)⁻¹ x = x - r := by
    intro x
    rw [Equiv.Perm.inv_eq_iff_eq, hpow]; ring
  have := Equiv.swap_apply_apply ((cycleZ ^ r)⁻¹) (0 : ZMod n) 1
  rw [hinv, hinv, inv_inv] at this
  rw [← this]; congr 1; ring

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
  intro t
  induction t with
  | zero => simp [hy0, hr0]
  | succ t ih =>
    rw [hx, hy, hr]
    by_cases hg : g (t + 1)
    · simp only [hg, if_true, ih]; push_cast; ring
    · simp only [hg, Bool.false_eq_true, if_false, ih]
      rw [← conj_cycle_swap (r t)]
      have hpow : ∀ (k : ℕ) (x : ZMod n), (cycleZ ^ k) x = x + k := by
        intro k x
        induction k generalizing x with
        | zero => simp
        | succ k ihk =>
          rw [pow_succ, Equiv.Perm.mul_apply, ihk]
          simp [cycleZ]; ring
      have hinv : ∀ x : ZMod n, (cycleZ ^ r t)⁻¹ x = x - r t := by
        intro x
        rw [Equiv.Perm.inv_eq_iff_eq, hpow]; ring
      simp only [Equiv.Perm.mul_apply, hinv, hpow]
      ring

end CycleTransposition

end GC.Tabulation
