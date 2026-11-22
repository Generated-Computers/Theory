import GC.Computability.SCLadder.LogFeedback

/-!
# Manuscript 008a: an `SC^k`-complete problem with an `NC^3` fragment

We formalize the mathematical core of the paper:

* `bitMachine_run` (hardness part of Theorem `thm:complete`): a machine whose configuration is a
  control state and a bit tape, and which in each step reads the scanned bit, writes a bit and
  moves its control, is simulated step by step by a time-invariant SPAI instance whose matrices are
  diagonal and differ from the identity in at most one (diagonal) entry;
* `pair_exact` (Lemma `lem:pairs`): pair merging of two exact summaries is exact for the
  composed block;
* `recompress_exact` (Theorem `thm:recompress`): when all pair-guard rows lie in the row space of a
  full-row-rank matrix `B_u`, the `2^{ρ_u}` syndrome leaves `B_u x = σ` form an exact summary;
* `invariant_observation_run` (Proposition `prop:invariant`): an invariant observation space turns
  the run into a run on the pairs `(u, B v)`.

Complexity-theoretic claims (logspace reductions, `SC^k`, `NC^2`, `NC^3`, uniformity) are not
formalized.
-/

namespace GC.SCLadder

open Matrix

variable {Q : Type*} {d : ℕ}

/-! ## Hardness: the configuration encoding with diagonal matrices -/

/-- A machine with control states `C` and a work tape of `d` bits: in control state `c` it scans
cell `head c`, reads its bit `z`, writes `write c z` there and enters `next c z`. (In the paper `c`
is the triple of machine state, work-head and input-head positions, and the input is fixed.) -/
structure BitMachine (C : Type*) (d : ℕ) where
  head : C → Fin d
  next : C → F → C
  write : C → F → F

variable {C : Type*}

/-- One step of the machine. -/
def BitMachine.step (M : BitMachine C d) (c : C × Data d) : C × Data d :=
  (M.next c.1 (c.2 (M.head c.1)),
    Function.update c.2 (M.head c.1) (M.write c.1 (c.2 (M.head c.1))))

/-- The time-invariant SPAI stage of the reduction: `a(u) = h`, `g(u,z) = next u z`,
`A_u` = identity with its `(h,h)` entry replaced by `w₀ ⊕ w₁`, and `b_u = w₀ e_h`. -/
def BitMachine.toStage [DecidableEq C] (M : BitMachine C d) : Stage C d where
  addr := M.head
  g := M.next
  A c := diagonal (Function.update (fun _ => (1 : F)) (M.head c) (M.write c 1 - M.write c 0))
  b c := Pi.single (M.head c) (M.write c 0)

/-- Every function `𝔽₂ → 𝔽₂` is affine: `w(z) = (w₁ - w₀) z + w₀`. -/
lemma affine_bit (w : F → F) (z : F) : (w 1 - w 0) * z + w 0 = w z := by
  rcases F_cases z with rfl | rfl <;> ring

lemma BitMachine.toStage_step [DecidableEq C] (M : BitMachine C d) (c : C × Data d) :
    M.toStage.step c = M.step c := by
  rcases c with ⟨u, v⟩
  simp only [Stage.step, BitMachine.step, BitMachine.toStage, Prod.mk.injEq, true_and]
  ext i
  simp only [Pi.add_apply, mulVec_diagonal]
  by_cases hi : i = M.head u
  · subst hi
    simp only [Function.update_self, Pi.single_eq_same]
    exact affine_bit (M.write u) _
  · simp [Function.update_of_ne hi, Pi.single_eq_of_ne hi]

/-- The matrices of the reduction are diagonal and differ from the identity in at most the
scanned diagonal entry. -/
lemma BitMachine.toStage_A [DecidableEq C] (M : BitMachine C d) (c : C) :
    (∀ i j, i ≠ j → M.toStage.A c i j = 0) ∧ (∀ i, i ≠ M.head c → M.toStage.A c i i = 1) := by
  refine ⟨fun i j hij => diagonal_apply_ne _ hij, fun i hi => ?_⟩
  simp [BitMachine.toStage, Function.update_of_ne hi]

/-- **Theorem `thm:complete` (hardness, correctness of the encoding).** The time-invariant SPAI
instance with `T` copies of `M.toStage` has, after `T` stages, exactly the configuration of the
machine after `T` steps (`z_t` is the scanned bit). -/
theorem bitMachine_run [DecidableEq C] (M : BitMachine C d) (T : ℕ) (c : C × Data d) :
    run (List.replicate T M.toStage) c = M.step^[T] c := by
  induction T generalizing c with
  | zero => rfl
  | succ T ih =>
    rw [List.replicate_succ, run_cons, Function.iterate_succ_apply, M.toStage_step, ih]

/-! ## Merging two summaries (Lemma `lem:pairs`) -/

/-- The pair leaf of `(λ, μ)`: guard `L_λ x = r_λ`, `K_μ M_λ x = s_μ - K_μ c_λ`; exit `q_μ` with
map `x ↦ N_μ M_λ x + (N_μ c_λ + d_μ)`. -/
def pairLeaf (l₁ l₂ : Leaf Q d) : Leaf Q d :=
  ⟨l₁.guard ++ l₂.guard.map (fun p => (p.1 ᵥ* l₁.M, p.2 - p.1 ⬝ᵥ l₁.c)), l₂.q, l₂.M * l₁.M,
    l₂.M *ᵥ l₁.c + l₂.c⟩

lemma pairLeaf_holds (l₁ l₂ : Leaf Q d) (x : Data d) :
    (pairLeaf l₁ l₂).guard.Holds x ↔ l₁.guard.Holds x ∧ l₂.guard.Holds (l₁.exit x).2 := by
  simp only [pairLeaf, Guard.holds_append, Leaf.exit]
  apply and_congr Iff.rfl
  simp only [Guard.Holds, List.mem_map, forall_exists_index, and_imp]
  constructor
  · intro h p hp
    have := h _ p hp rfl
    simp only at this
    rw [dotProduct_add, dotProduct_mulVec, this]; ring
  · rintro h _ p hp rfl
    have := h p hp
    rw [dotProduct_add, dotProduct_mulVec] at this
    simp only
    rw [← this]; ring

lemma pairLeaf_exit (l₁ l₂ : Leaf Q d) (x : Data d) :
    (pairLeaf l₁ l₂).exit x = l₂.exit (l₁.exit x).2 := by
  simp only [pairLeaf, Leaf.exit, Prod.mk.injEq, true_and]
  rw [mulVec_add, mulVec_mulVec, add_assoc]

/-- The feasible-or-not pairs for entering state `u`. -/
def pairSet {ι₁ ι₂ : Type*} (Λ₁ : Q → Set ι₁) (Λ₂ : Q → Set ι₂) (leaf₁ : ι₁ → Leaf Q d) (u : Q) :
    Set (ι₁ × ι₂) :=
  {p | p.1 ∈ Λ₁ u ∧ p.2 ∈ Λ₂ (leaf₁ p.1).q}

/-- **Lemma `lem:pairs` (008a).** If `S¹` is an exact summary of `Φ₁` and `S²` an exact summary of
`Φ₂`, then the pair leaves form an exact summary of the composition `Φ₂ ∘ Φ₁`. -/
theorem pair_exact {ι₁ ι₂ : Type*} {Φ₁ Φ₂ : Q → Data d → Q × Data d}
    {Λ₁ : Q → Set ι₁} {Λ₂ : Q → Set ι₂} {leaf₁ : ι₁ → Leaf Q d} {leaf₂ : ι₂ → Leaf Q d}
    (h₁ : IsExactSummary Φ₁ Λ₁ leaf₁) (h₂ : IsExactSummary Φ₂ Λ₂ leaf₂) :
    IsExactSummary (fun u x => Φ₂ (Φ₁ u x).1 (Φ₁ u x).2) (pairSet Λ₁ Λ₂ leaf₁)
      (fun p => pairLeaf (leaf₁ p.1) (leaf₂ p.2)) := by
  intro u x
  obtain ⟨⟨i, ⟨hi, hix⟩, hiu⟩, hΦ₁⟩ := h₁ u x
  have e₁ := hΦ₁ i hi hix
  set y := ((leaf₁ i).exit x).2
  obtain ⟨⟨j, ⟨hj, hjy⟩, hju⟩, hΦ₂⟩ := h₂ (leaf₁ i).q y
  refine ⟨⟨(i, j), ⟨⟨hi, hj⟩, (pairLeaf_holds _ _ x).mpr ⟨hix, hjy⟩⟩, ?_⟩, ?_⟩
  · rintro ⟨i', j'⟩ ⟨⟨hi', hj'⟩, h⟩
    rw [pairLeaf_holds] at h
    obtain rfl := hiu i' ⟨hi', h.1⟩
    obtain rfl := hju j' ⟨hj', h.2⟩
    rfl
  · rintro ⟨i', j'⟩ ⟨hi', hj'⟩ h
    rw [pairLeaf_holds] at h
    obtain rfl := hiu i' ⟨hi', h.1⟩
    obtain rfl := hju j' ⟨hj', h.2⟩
    simp only [pairLeaf_exit, e₁]
    exact hΦ₂ j' hj' h.2

/-- Pair merging of exact summaries of consecutive blocks is exact for the concatenated block. -/
theorem pair_exact_run {ι₁ ι₂ : Type*} (S₁ S₂ : List (Stage Q d))
    {Λ₁ : Q → Set ι₁} {Λ₂ : Q → Set ι₂} {leaf₁ : ι₁ → Leaf Q d} {leaf₂ : ι₂ → Leaf Q d}
    (h₁ : IsExactSummary (fun u x => run S₁ (u, x)) Λ₁ leaf₁)
    (h₂ : IsExactSummary (fun u x => run S₂ (u, x)) Λ₂ leaf₂) :
    IsExactSummary (fun u x => run (S₁ ++ S₂) (u, x)) (pairSet Λ₁ Λ₂ leaf₁)
      (fun p => pairLeaf (leaf₁ p.1) (leaf₂ p.2)) := by
  have := pair_exact h₁ h₂
  simp only [Prod.mk.eta] at this
  simpa only [run_append] using this

/-! ## Exact syndrome recompression (Theorem `thm:recompress`) -/

/-- Syndrome dependence: a guard all of whose rows lie in the row space of `B` has a truth value
that depends only on `B x`. -/
lemma guard_holds_iff_of_syndrome {ρ : ℕ} (B : Matrix (Fin ρ) (Fin d) F) {G : Guard d}
    (hG : ∀ p ∈ G, p.1 ∈ Submodule.span F (Set.range B)) {x y : Data d}
    (h : B *ᵥ x = B *ᵥ y) : G.Holds x ↔ G.Holds y := by
  simp only [Guard.Holds]
  exact forall₂_congr fun p hp => by rw [dotProduct_eq_of_mem_span B (hG p hp) h]

/-- The syndrome guard `B x = σ`. -/
def syndromeGuard {ρ : ℕ} (B : Matrix (Fin ρ) (Fin d) F) (σ : Fin ρ → F) : Guard d :=
  List.ofFn fun k => (B k, σ k)

lemma syndromeGuard_holds {ρ : ℕ} (B : Matrix (Fin ρ) (Fin d) F) (σ : Fin ρ → F) (x : Data d) :
    (syndromeGuard B σ).Holds x ↔ B *ᵥ x = σ := by
  simp only [syndromeGuard, Guard.Holds, List.forall_mem_ofFn_iff]
  exact ⟨fun h => funext h, fun h k => congrFun h k⟩

/-- The new leaf for syndrome `σ`: guard `B x = σ`, with the exit of the unique old leaf satisfied
by a representative `x_σ` of the syndrome. -/
noncomputable def syndromeLeaf {ι : Type*} {ρ : ℕ} (Λu : Set ι) (leaf : ι → Leaf Q d)
    (B : Matrix (Fin ρ) (Fin d) F) (hB : Function.Surjective B.mulVec)
    (hex : ∀ x, ∃ i, i ∈ Λu ∧ (leaf i).guard.Holds x) (σ : Fin ρ → F) : Leaf Q d :=
  let i := Classical.choose (hex (Classical.choose (hB σ)))
  ⟨syndromeGuard B σ, (leaf i).q, (leaf i).M, (leaf i).c⟩

/-- **Theorem `thm:recompress` (008a), exactness.** Let a summary be exact at `u` (e.g. the pair
summary of `pair_exact`), and let `B` be a matrix of full row rank `ρ` (surjective `x ↦ B x`) whose
row space contains every guard row of every leaf of `Λu`. Then the `2^ρ` leaves with guards
`B x = σ`, `σ ∈ 𝔽₂^ρ`, form an exact summary at `u`. -/
theorem recompress_exact {ι : Type*} {ρ : ℕ} {Φ : Q → Data d → Q × Data d} {u : Q} {Λu : Set ι}
    {leaf : ι → Leaf Q d} (h : IsExactAt Φ u Λu leaf) (B : Matrix (Fin ρ) (Fin d) F)
    (hB : Function.Surjective B.mulVec)
    (hrows : ∀ i ∈ Λu, ∀ p ∈ (leaf i).guard, p.1 ∈ Submodule.span F (Set.range B)) :
    IsExactAt Φ u Set.univ (syndromeLeaf Λu leaf B hB (fun x => (h x).1.exists)) ∧
      Fintype.card (Fin ρ → F) = 2 ^ ρ := by
  refine ⟨?_, by simp [ZMod.card]⟩
  intro x
  have hguard : ∀ σ, (syndromeLeaf Λu leaf B hB (fun x => (h x).1.exists) σ).guard.Holds x ↔
      B *ᵥ x = σ := fun σ => syndromeGuard_holds B σ x
  refine ⟨⟨B *ᵥ x, ⟨trivial, (hguard _).mpr rfl⟩, fun σ hσ => ((hguard σ).mp hσ.2).symm⟩, ?_⟩
  intro σ _ hσ
  rw [hguard] at hσ
  subst hσ
  -- the representative and the selected old leaf
  set xσ := Classical.choose (hB (B *ᵥ x)) with hxσ_def
  have hxσ : B *ᵥ xσ = B *ᵥ x := Classical.choose_spec (hB (B *ᵥ x))
  set i := Classical.choose ((h xσ).1.exists) with hi_def
  have hi : i ∈ Λu ∧ (leaf i).guard.Holds xσ := Classical.choose_spec ((h xσ).1.exists)
  have hix : (leaf i).guard.Holds x :=
    (guard_holds_iff_of_syndrome B (hrows i hi.1) hxσ).mp hi.2
  rw [(h x).2 i hi.1 hix]
  rfl

/-- The global recompressed summary: one basis `B u` per entering state, leaves indexed by
`(u, σ)`. -/
theorem recompress_summary_exact {ι : Type*} {Φ : Q → Data d → Q × Data d} {Λ : Q → Set ι}
    {leaf : ι → Leaf Q d} (h : IsExactSummary Φ Λ leaf) (ρ : Q → ℕ)
    (B : (u : Q) → Matrix (Fin (ρ u)) (Fin d) F) (hB : ∀ u, Function.Surjective (B u).mulVec)
    (hrows : ∀ u, ∀ i ∈ Λ u, ∀ p ∈ (leaf i).guard, p.1 ∈ Submodule.span F (Set.range (B u))) :
    IsExactSummary Φ (fun u => {i : Σ u : Q, Fin (ρ u) → F | i.1 = u})
      (fun i => syndromeLeaf (Λ i.1) leaf (B i.1) (hB i.1) (fun x => (h i.1 x).1.exists) i.2) := by
  intro u x
  obtain ⟨⟨σ, ⟨-, hσ⟩, huniq⟩, hexit⟩ := (recompress_exact (h u) (B u) (hB u) (hrows u)).1 x
  refine ⟨⟨⟨u, σ⟩, ⟨rfl, hσ⟩, ?_⟩, ?_⟩
  · rintro ⟨u', σ'⟩ ⟨hu', hσ'⟩
    simp only at hu'
    subst hu'
    rw [huniq σ' ⟨trivial, hσ'⟩]
  · rintro ⟨u', σ'⟩ hu' hσ'
    simp only [Set.mem_ofPred_eq] at hu'
    subst hu'
    exact hexit σ' trivial hσ'

/-! ## An invariant observation space (Proposition `prop:invariant`) -/

/-- The reduced stage on pairs `(u, σ)`, `σ = B v ∈ 𝔽₂^r`:
`z = η_u ⬝ σ`, `u' = g(u, z)`, `σ' = C_u σ + B b_u`. -/
def obsStep {r : ℕ} (B : Matrix (Fin r) (Fin d) F) (η : Q → Fin r → F)
    (Cm : Q → Matrix (Fin r) (Fin r) F) (s : Stage Q d) (c : Q × (Fin r → F)) : Q × (Fin r → F) :=
  (s.g c.1 (η c.1 ⬝ᵥ c.2), Cm c.1 *ᵥ c.2 + B *ᵥ s.b c.1)

/-- The reduced run. -/
def obsRun {r : ℕ} (B : Matrix (Fin r) (Fin d) F) (η : Stage Q d → Q → Fin r → F)
    (Cm : Stage Q d → Q → Matrix (Fin r) (Fin r) F) :
    List (Stage Q d) → Q × (Fin r → F) → Q × (Fin r → F)
  | [], c => c
  | s :: S, c => obsRun B η Cm S (obsStep B (η s) (Cm s) s c)

/-- **Proposition `prop:invariant` (008a), mathematical core.** If every probe row lies in the row
space of `B` (`e_{a_t(u)}ᵀ = η_{t,u} B`) and the row space is invariant (`B A_{t,u} = C_{t,u} B`),
then the run on pairs `(u, B v)` reproduces the controller states and the syndromes `B v_t` of the
actual run. -/
theorem invariant_observation_run {r : ℕ} (B : Matrix (Fin r) (Fin d) F)
    (η : Stage Q d → Q → Fin r → F) (Cm : Stage Q d → Q → Matrix (Fin r) (Fin r) F)
    (S : List (Stage Q d)) (hη : ∀ s ∈ S, ∀ u, η s u ᵥ* B = Pi.single (s.addr u) 1)
    (hC : ∀ s ∈ S, ∀ u, B * s.A u = Cm s u * B) (c : Q × Data d) :
    obsRun B η Cm S (c.1, B *ᵥ c.2) = ((run S c).1, B *ᵥ (run S c).2) := by
  induction S generalizing c with
  | nil => rfl
  | cons s S ih =>
    have hη' := hη s (List.mem_cons_self ..)
    have hC' := hC s (List.mem_cons_self ..)
    have hstep : obsStep B (η s) (Cm s) s (c.1, B *ᵥ c.2) =
        ((s.step c).1, B *ᵥ (s.step c).2) := by
      simp only [obsStep, Stage.step, Prod.mk.injEq]
      constructor
      · rw [dotProduct_mulVec, hη', single_dotProduct, one_mul]
      · rw [mulVec_mulVec, ← hC', ← mulVec_mulVec, mulVec_add]
    simp only [obsRun, run_cons, hstep]
    exact ih (fun s' hs' => hη s' (List.mem_cons_of_mem _ hs'))
      (fun s' hs' => hC s' (List.mem_cons_of_mem _ hs')) _

end GC.SCLadder
