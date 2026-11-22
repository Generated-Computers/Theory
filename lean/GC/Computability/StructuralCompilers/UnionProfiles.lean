import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Powerset
import Mathlib.Logic.Relation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# Few union profiles (manuscript 007d)

* `absorbing_elimination` (Lemma 2.2): in a tagged absorbing system, the complemented value of
  every regular vertex is `Reach(s, v) ∨ ⋁_{q ∈ Exc} (Reach(q, v) ∧ W_q)`.
* `profile_composition` (Lemma 3.2): the composition lemma of the union-profile compiler for an
  exception-port system and a node `[l, r)` with children `[l, t)`, `[t, r)`.
* `localRun_root`, `localRun_trueProfile` : the root run on `0` is the true computation, and the
  true contribution vector at every interval is in the union closure and reproduces the true
  values.
* `unionClosure_card_le_rows`, `unionClosure_card_le_cols`, `unionClosure_card_le_zeros`
  (Proposition 4.1): bounds on the union closure.
* `matching_unionClosure_card` (Example 4.3): the identity matrix has `2^w` unions.
-/

namespace GC.StructuralCompilers

/-! ### Tagged absorbing systems and absorbing elimination (Section 2) -/

/-- A tagged absorbing system (Definition 2.1): vertices `0, 1, 2, …`, each with a finite set of
earlier predecessors, a tag (exception or regular) and a constant `Y_v`. The exception truth
tables play no role in Lemma 2.2, whose statement holds for arbitrary exception values. -/
structure TaggedSystem where
  /-- `Pred(v)` -/
  pred : ℕ → Finset ℕ
  /-- predecessors are earlier vertices -/
  pred_lt : ∀ v, ∀ u ∈ pred v, u < v
  /-- the exception tag -/
  isExc : ℕ → Prop
  /-- the constants `Y_v` of the regular vertices -/
  Y : ℕ → Bool

/-- The regular rule: `V_v = Y_v` if `Pred(v) = ∅`, and `V_v = Y_v ∨ ⋀_{u ∈ Pred(v)} V_u`
otherwise. -/
def TaggedSystem.RegularRule (T : TaggedSystem) (V : ℕ → Bool) : Prop :=
  ∀ v, ¬ T.isExc v →
    (V v = true ↔ (T.Y v = true ∨ (T.pred v ≠ ∅ ∧ ∀ u ∈ T.pred v, V u = true)))

/-- The digraph `Γ` on the vertices and a new vertex `s` (encoded as `none`). -/
def TaggedSystem.arc (T : TaggedSystem) : Option ℕ → Option ℕ → Prop
  | none, some v => ¬ T.isExc v ∧ T.pred v = ∅ ∧ T.Y v = false
  | some u, some v => ¬ T.isExc v ∧ T.pred v ≠ ∅ ∧ T.Y v = false ∧ u ∈ T.pred v
  | _, none => False

/-- `Reach(y, v)`: a directed path of `Γ` from `y` to `v`. -/
def TaggedSystem.Reach (T : TaggedSystem) (y : Option ℕ) (v : ℕ) : Prop :=
  Relation.TransGen T.arc y (some v)

lemma TaggedSystem.reach_iff (T : TaggedSystem) (y : Option ℕ) (v : ℕ) :
    T.Reach y v ↔ ∃ x, T.arc x (some v) ∧ (x = y ∨ Relation.TransGen T.arc y x) := by
  unfold TaggedSystem.Reach
  rw [Relation.TransGen.tail'_iff]
  constructor
  · rintro ⟨x, hx, ha⟩
    exact ⟨x, ha, Relation.reflTransGen_iff_eq_or_transGen.1 hx⟩
  · rintro ⟨x, ha, hx⟩
    exact ⟨x, Relation.reflTransGen_iff_eq_or_transGen.2 hx, ha⟩

lemma TaggedSystem.not_reach_exc (T : TaggedSystem) (y : Option ℕ) {v : ℕ} (hv : T.isExc v) :
    ¬ T.Reach y v := by
  rw [T.reach_iff]
  rintro ⟨x, ha, -⟩
  cases x <;> simp [TaggedSystem.arc] at ha <;> exact ha.1 hv

/-- **Lemma 2.2 (absorbing elimination).** For every regular vertex `v`,
`W_v = Reach(s, v) ∨ ⋁_{q ∈ Exc} (Reach(q, v) ∧ W_q)`, where `W = 1 - V`. -/
theorem absorbing_elimination (T : TaggedSystem) (V : ℕ → Bool) (hV : T.RegularRule V) :
    ∀ v, ¬ T.isExc v →
      (V v = false ↔ T.Reach none v ∨ ∃ q, T.isExc q ∧ T.Reach (some q) v ∧ V q = false) := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    intro hv
    have hrule := hV v hv
    -- arcs entering `v`
    have harc : ∀ x, T.arc x (some v) ↔
        (x = none ∧ T.pred v = ∅ ∧ T.Y v = false) ∨
        (∃ u, x = some u ∧ T.pred v ≠ ∅ ∧ T.Y v = false ∧ u ∈ T.pred v) := by
      intro x
      cases x with
      | none => simp [TaggedSystem.arc, hv]
      | some u => simp [TaggedSystem.arc, hv]
    by_cases hY : T.Y v = true
    · -- `V v = 1` and no arc enters `v`
      have h1 : V v = true := hrule.2 (Or.inl hY)
      have hno : ∀ y, ¬ T.Reach y v := by
        intro y hr
        rw [T.reach_iff] at hr
        obtain ⟨x, ha, -⟩ := hr
        rw [harc] at ha
        rcases ha with ⟨-, -, h⟩ | ⟨-, -, -, h, -⟩ <;> simp [h] at hY
      simp only [h1, Bool.true_eq_false, false_iff, not_or, not_exists, not_and]
      exact ⟨hno none, fun q _ hr => absurd hr (hno _)⟩
    · have hY0 : T.Y v = false := by simpa using hY
      by_cases hP : T.pred v = ∅
      · -- a root with `Y_v = 0`
        have h0 : V v = false := by
          by_contra h
          have := hrule.1 (by simpa using h)
          rcases this with h' | ⟨h', -⟩
          · exact hY h'
          · exact h' hP
        simp only [h0, true_iff]
        left
        exact Relation.TransGen.single (by simp [TaggedSystem.arc, hv, hP, hY0])
      · -- `W_v = ⋁_{u ∈ Pred(v)} W_u`
        have hW : V v = false ↔ ∃ u ∈ T.pred v, V u = false := by
          constructor
          · intro h
            by_contra hne
            push Not at hne
            have := hrule.2 (Or.inr ⟨hP, fun u hu => by simpa using hne u hu⟩)
            rw [h] at this
            exact Bool.false_ne_true this
          · rintro ⟨u, hu, hu0⟩
            by_contra h
            have := hrule.1 (by simpa using h)
            rcases this with h' | ⟨-, h'⟩
            · exact hY h'
            · rw [h' u hu] at hu0
              exact absurd hu0 (by decide)
        rw [hW]
        have hreach : ∀ y, T.Reach y v ↔
            ∃ u ∈ T.pred v, (some u = y ∨ Relation.TransGen T.arc y (some u)) := by
          intro y
          rw [T.reach_iff]
          constructor
          · rintro ⟨x, ha, hx⟩
            rw [harc] at ha
            rcases ha with ⟨-, h, -⟩ | ⟨u, rfl, -, -, hu⟩
            · exact absurd h hP
            · exact ⟨u, hu, hx⟩
          · rintro ⟨u, hu, hx⟩
            exact ⟨some u, (harc _).2 (Or.inr ⟨u, rfl, hP, hY0, hu⟩), hx⟩
        constructor
        · rintro ⟨u, hu, hu0⟩
          have hlt := T.pred_lt v u hu
          by_cases hue : T.isExc u
          · right
            exact ⟨u, hue, (hreach _).2 ⟨u, hu, Or.inl rfl⟩, hu0⟩
          · rcases (ih u hlt hue).1 hu0 with hr | ⟨q, hq, hr, hq0⟩
            · left
              exact (hreach _).2 ⟨u, hu, Or.inr hr⟩
            · right
              exact ⟨q, hq, (hreach _).2 ⟨u, hu, Or.inr hr⟩, hq0⟩
        · rintro (hr | ⟨q, hq, hr, hq0⟩)
          · obtain ⟨u, hu, hx⟩ := (hreach _).1 hr
            have hlt := T.pred_lt v u hu
            rcases hx with h | hx
            · exact absurd h (by simp)
            · by_cases hue : T.isExc u
              · exact absurd hx (T.not_reach_exc none hue)
              · exact ⟨u, hu, (ih u hlt hue).2 (Or.inl hx)⟩
          · obtain ⟨u, hu, hx⟩ := (hreach _).1 hr
            have hlt := T.pred_lt v u hu
            rcases hx with h | hx
            · have huq : u = q := Option.some_inj.1 h
              rw [huq] at hu
              exact ⟨q, hu, hq0⟩
            · by_cases hue : T.isExc u
              · exact absurd hx (T.not_reach_exc (some q) hue)
              · exact ⟨u, hu, (ih u hlt hue).2 (Or.inr ⟨q, hq, hx, hq0⟩)⟩

/-! ### Exception-port systems and the composition lemma (Section 3) -/

/-- An exception-port system (Definition 2.4) with at most `a` ports per exception (unused ports
are ignored by the truth table): port `i` of exception `e` has a constant `c e i` and a set
`B e i` of earlier exceptions; `g e` is the truth table of `e`. Here `W` (the complemented
exception value) is the computed quantity. -/
structure PortSystem (a : ℕ) where
  /-- the constants `c_p` -/
  c : ℕ → Fin a → Bool
  /-- the sets `B_p` -/
  B : ℕ → Fin a → Finset ℕ
  /-- `B_p ⊆ {0, …, e-1}` -/
  B_lt : ∀ e i, ∀ q ∈ B e i, q < e
  /-- the truth tables `g_e` -/
  g : ℕ → (Fin a → Bool) → Bool

variable {a : ℕ}

/-- The values of an exception-port system: `x_p = c_p ∨ ⋁_{q ∈ B_p} W_q`,
`W_e = g_e((x_p)_p)`, in increasing order of `e`. -/
def PortSystem.W (P : PortSystem a) (e : ℕ) : Bool :=
  P.g e (fun i => P.c e i || decide (∃ q ∈ (P.B e i).attach, P.W q.1 = true))
termination_by e
decreasing_by all_goals exact P.B_lt _ _ _ (Finset.coe_mem _)

/-- The local run of an interval starting at `l` on an input vector `α` (indexed by ports):
`x_p = c_p ∨ α_p ∨ ⋁_{q ∈ B_p ∩ [l, e)} W'_q`, `W'_e = g_e((x_p)_p)`. -/
def PortSystem.run (P : PortSystem a) (l : ℕ) (α : ℕ → Fin a → Bool) (e : ℕ) : Bool :=
  P.g e (fun i => P.c e i || α e i ||
    decide (∃ q ∈ (P.B e i).attach, l ≤ q.1 ∧ P.run l α q.1 = true))
termination_by e
decreasing_by all_goals exact P.B_lt _ _ _ (Finset.coe_mem _)

lemma exists_attach_iff {s : Finset ℕ} {p : ℕ → Prop} :
    (∃ q ∈ s.attach, p q.1) ↔ ∃ q ∈ s, p q := by
  constructor
  · rintro ⟨⟨q, hq⟩, -, h⟩
    exact ⟨q, hq, h⟩
  · rintro ⟨q, hq, h⟩
    exact ⟨⟨q, hq⟩, Finset.mem_attach _ _, h⟩

lemma PortSystem.W_eq (P : PortSystem a) (e : ℕ) :
    P.W e = P.g e (fun i => P.c e i || decide (∃ q ∈ P.B e i, P.W q = true)) := by
  rw [PortSystem.W]
  simp only [exists_attach_iff (p := fun q => P.W q = true)]

lemma PortSystem.run_eq (P : PortSystem a) (l : ℕ) (α : ℕ → Fin a → Bool) (e : ℕ) :
    P.run l α e = P.g e (fun i => P.c e i || α e i ||
      decide (∃ q ∈ P.B e i, l ≤ q ∧ P.run l α q = true)) := by
  rw [PortSystem.run]
  simp only [exists_attach_iff (p := fun q => l ≤ q ∧ P.run l α q = true)]

/-- The union of the incidence columns of a set `S` of exceptions: `p ↦ ⋁_{q ∈ S} [q ∈ B_p]`. -/
noncomputable def PortSystem.unionVec (P : PortSystem a) (S : Set ℕ) : ℕ → Fin a → Bool :=
  fun e i => by classical exact decide (∃ q ∈ P.B e i, q ∈ S)

/-- Restriction of a port vector to the ports owned by exceptions in `[l, r)` (other entries
are set to `0`). -/
def restrictTo (l r : ℕ) (α : ℕ → Fin a → Bool) : ℕ → Fin a → Bool :=
  fun e i => decide (l ≤ e ∧ e < r) && α e i

/-- Restriction to the ports owned by exceptions `e ≥ r` (the ports after `[l, r)`). -/
def restrictAfter (r : ℕ) (α : ℕ → Fin a → Bool) : ℕ → Fin a → Bool :=
  fun e i => decide (r ≤ e) && α e i

/-- The union closure `𝒰(A^in_I)` of the node `I = [l, r)`: rows are the ports of `I`, columns
the exceptions `q < l`. -/
def PortSystem.closureIn (P : PortSystem a) (l r : ℕ) : Set (ℕ → Fin a → Bool) :=
  {α | ∃ S : Set ℕ, (∀ q ∈ S, q < l) ∧ α = restrictTo l r (P.unionVec S)}

/-- The union closure `𝒰(A^out_I)`: rows are the ports after `I`, columns the exceptions in
`I`. -/
def PortSystem.closureOut (P : PortSystem a) (l r : ℕ) : Set (ℕ → Fin a → Bool) :=
  {β | ∃ S : Set ℕ, (∀ q ∈ S, l ≤ q ∧ q < r) ∧ β = restrictAfter r (P.unionVec S)}

/-- The response `ρ_I(α) = ⋁_{q ∈ I, W'_q = 1} a_q(A^out_I)`. -/
noncomputable def PortSystem.response (P : PortSystem a) (l r : ℕ) (α : ℕ → Fin a → Bool) :
    ℕ → Fin a → Bool :=
  restrictAfter r (P.unionVec {q | l ≤ q ∧ q < r ∧ P.run l α q = true})

lemma PortSystem.g_congr (P : PortSystem a) (e : ℕ) (x y : Fin a → Bool)
    (h : ∀ i, x i = true ↔ y i = true) : P.g e x = P.g e y := by
  congr 1
  funext i
  exact Bool.eq_iff_iff.2 (h i)

@[simp] lemma restrictTo_apply (l r : ℕ) (α : ℕ → Fin a → Bool) (e : ℕ) (i : Fin a) :
    restrictTo l r α e i = true ↔ (l ≤ e ∧ e < r) ∧ α e i = true := by
  simp [restrictTo]

@[simp] lemma restrictAfter_apply (r : ℕ) (α : ℕ → Fin a → Bool) (e : ℕ) (i : Fin a) :
    restrictAfter r α e i = true ↔ r ≤ e ∧ α e i = true := by
  simp [restrictAfter]

@[simp] lemma PortSystem.unionVec_apply (P : PortSystem a) (S : Set ℕ) (e : ℕ) (i : Fin a) :
    P.unionVec S e i = true ↔ ∃ q ∈ P.B e i, q ∈ S := by
  simp [PortSystem.unionVec]

lemma PortSystem.response_apply (P : PortSystem a) (l r : ℕ) (α : ℕ → Fin a → Bool) (e : ℕ)
    (i : Fin a) : P.response l r α e i = true ↔
      r ≤ e ∧ ∃ q ∈ P.B e i, l ≤ q ∧ q < r ∧ P.run l α q = true := by
  simp [PortSystem.response]

lemma PortSystem.run_port (P : PortSystem a) (l : ℕ) (α : ℕ → Fin a → Bool) (e : ℕ) :
    P.run l α e = P.g e (fun i => decide (P.c e i = true ∨ α e i = true ∨
      ∃ q ∈ P.B e i, l ≤ q ∧ P.run l α q = true)) := by
  rw [P.run_eq]
  apply P.g_congr
  intro i
  simp [or_assoc]

/-- **Lemma 3.2 (composition).** Let `I = [l, r)` have children `L = [l, t)` and `R' = [t, r)`,
let `α ∈ 𝒰(A^in_I)`, `α_L = α|_L`, `u_L = ρ_L(α_L)`, `α_{R'} = (α ∨ u_L)|_{R'}`,
`u_{R'} = ρ_{R'}(α_{R'})`. Then `α_L ∈ 𝒰(A^in_L)`, `α_{R'} ∈ 𝒰(A^in_{R'})`, the local runs of
`L` and `R'` produce the values of the local run of `I`, and
`ρ_I(α) = u_L|_{after I} ∨ u_{R'}`. -/
theorem profile_composition (P : PortSystem a) (l t r : ℕ) (hlt : l ≤ t) (htr : t ≤ r)
    (α : ℕ → Fin a → Bool) (hα : α ∈ P.closureIn l r) :
    let αL := restrictTo l t α
    let uL := P.response l t αL
    let αR := restrictTo t r (fun e i => α e i || uL e i)
    let uR := P.response t r αR
    αL ∈ P.closureIn l t ∧ αR ∈ P.closureIn t r ∧
    (∀ e, l ≤ e → e < t → P.run l α e = P.run l αL e) ∧
    (∀ e, t ≤ e → e < r → P.run l α e = P.run t αR e) ∧
    P.response l r α = fun e i => restrictAfter r uL e i || uR e i := by
  intro αL uL αR uR
  obtain ⟨S, hS, rfl⟩ := hα
  have hαL : ∀ e i, αL e i = true ↔ (l ≤ e ∧ e < t) ∧ ∃ q ∈ P.B e i, q ∈ S := by
    intro e i
    simp only [αL, restrictTo_apply, PortSystem.unionVec_apply]
    constructor
    · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨h1, ⟨h1.1, by omega⟩, h3⟩
  have huL : ∀ e i, uL e i = true ↔
      t ≤ e ∧ ∃ q ∈ P.B e i, l ≤ q ∧ q < t ∧ P.run l αL q = true := by
    intro e i
    exact P.response_apply l t αL e i
  have hαR : ∀ e i, αR e i = true ↔ (t ≤ e ∧ e < r) ∧
      ((∃ q ∈ P.B e i, q ∈ S) ∨ ∃ q ∈ P.B e i, l ≤ q ∧ q < t ∧ P.run l αL q = true) := by
    intro e i
    simp only [αR, restrictTo_apply, Bool.or_eq_true, huL, PortSystem.unionVec_apply]
    constructor
    · rintro ⟨h1, (⟨-, h⟩ | ⟨-, h⟩)⟩
      · exact ⟨h1, Or.inl h⟩
      · exact ⟨h1, Or.inr h⟩
    · rintro ⟨h1, (h | h)⟩
      · exact ⟨h1, Or.inl ⟨⟨by omega, h1.2⟩, h⟩⟩
      · exact ⟨h1, Or.inr ⟨h1.1, h⟩⟩
  -- agreement on the left child
  have hL : ∀ e, l ≤ e → e < t → P.run l (restrictTo l r (P.unionVec S)) e = P.run l αL e := by
    intro e
    induction e using Nat.strong_induction_on with
    | _ e ih =>
      intro hle het
      rw [P.run_port, P.run_port]
      apply P.g_congr
      intro i
      simp only [decide_eq_true_eq, restrictTo_apply, PortSystem.unionVec_apply, hαL]
      have h1 : l ≤ e ∧ e < t := ⟨hle, het⟩
      have h2 : l ≤ e ∧ e < r := ⟨hle, by omega⟩
      have key : (∃ q ∈ P.B e i, l ≤ q ∧ P.run l (restrictTo l r (P.unionVec S)) q = true) ↔
          (∃ q ∈ P.B e i, l ≤ q ∧ P.run l αL q = true) := by
        constructor
        · rintro ⟨q, hq, hlq, hr⟩
          exact ⟨q, hq, hlq, by rw [← ih q (P.B_lt e i q hq) hlq (by have := P.B_lt e i q hq; omega)]; exact hr⟩
        · rintro ⟨q, hq, hlq, hr⟩
          exact ⟨q, hq, hlq, by rw [ih q (P.B_lt e i q hq) hlq (by have := P.B_lt e i q hq; omega)]; exact hr⟩
      rw [key]
      simp only [h1, h2, true_and]
  -- agreement on the right child
  have hR : ∀ e, t ≤ e → e < r → P.run l (restrictTo l r (P.unionVec S)) e = P.run t αR e := by
    intro e
    induction e using Nat.strong_induction_on with
    | _ e ih =>
      intro hte her
      rw [P.run_port, P.run_port]
      apply P.g_congr
      intro i
      simp only [decide_eq_true_eq, restrictTo_apply, PortSystem.unionVec_apply, hαR]
      have h1 : t ≤ e ∧ e < r := ⟨hte, her⟩
      have h2 : l ≤ e ∧ e < r := ⟨by omega, her⟩
      have key : (∃ q ∈ P.B e i, l ≤ q ∧ P.run l (restrictTo l r (P.unionVec S)) q = true) ↔
          (∃ q ∈ P.B e i, l ≤ q ∧ q < t ∧ P.run l αL q = true) ∨
            (∃ q ∈ P.B e i, t ≤ q ∧ P.run t αR q = true) := by
        constructor
        · rintro ⟨q, hq, hlq, hr⟩
          have hqe := P.B_lt e i q hq
          by_cases hqt : q < t
          · exact Or.inl ⟨q, hq, hlq, hqt, by rw [← hL q hlq hqt]; exact hr⟩
          · exact Or.inr ⟨q, hq, by omega, by rw [← ih q hqe (by omega) (by omega)]; exact hr⟩
        · rintro (⟨q, hq, hlq, hqt, hr⟩ | ⟨q, hq, htq, hr⟩)
          · exact ⟨q, hq, hlq, by rw [hL q hlq hqt]; exact hr⟩
          · have hqe := P.B_lt e i q hq
            exact ⟨q, hq, by omega, by rw [ih q hqe htq (by omega)]; exact hr⟩
      rw [key]
      simp only [h1, h2, true_and, or_assoc]
  refine ⟨?_, ?_, hL, hR, ?_⟩
  · -- `α_L ∈ 𝒰(A^in_L)`
    refine ⟨S, hS, ?_⟩
    funext e i
    rw [Bool.eq_iff_iff, hαL, restrictTo_apply, PortSystem.unionVec_apply]
  · -- `α_{R'} ∈ 𝒰(A^in_{R'})`
    refine ⟨S ∪ {q | l ≤ q ∧ q < t ∧ P.run l αL q = true}, ?_, ?_⟩
    · rintro q (hq | ⟨-, hq, -⟩)
      · have := hS q hq; omega
      · exact hq
    · funext e i
      rw [Bool.eq_iff_iff, hαR, restrictTo_apply, PortSystem.unionVec_apply]
      simp only [Set.mem_union, Set.mem_setOf_eq]
      constructor
      · rintro ⟨h1, (⟨q, hq, hqS⟩ | ⟨q, hq, hq'⟩)⟩
        · exact ⟨h1, q, hq, Or.inl hqS⟩
        · exact ⟨h1, q, hq, Or.inr hq'⟩
      · rintro ⟨h1, q, hq, (hqS | hq')⟩
        · exact ⟨h1, Or.inl ⟨q, hq, hqS⟩⟩
        · exact ⟨h1, Or.inr ⟨q, hq, hq'⟩⟩
  · -- the response identity
    funext e i
    rw [Bool.eq_iff_iff, Bool.or_eq_true, restrictAfter_apply, PortSystem.response_apply, huL]
    simp only [uR, PortSystem.response_apply]
    constructor
    · rintro ⟨her, q, hq, hlq, hqr, hrun⟩
      by_cases hqt : q < t
      · exact Or.inl ⟨her, by omega, q, hq, hlq, hqt, by rw [← hL q hlq hqt]; exact hrun⟩
      · exact Or.inr ⟨her, q, hq, by omega, hqr, by rw [← hR q (by omega) hqr]; exact hrun⟩
    · rintro (⟨her, -, q, hq, hlq, hqt, hrun⟩ | ⟨her, q, hq, htq, hqr, hrun⟩)
      · exact ⟨her, q, hq, hlq, by omega, by rw [hL q hlq hqt]; exact hrun⟩
      · exact ⟨her, q, hq, by omega, hqr, by rw [hR q htq hqr]; exact hrun⟩

/-- At the root, the local run on the zero vector is the true computation. -/
theorem localRun_root (P : PortSystem a) (e : ℕ) : P.run 0 (fun _ _ => false) e = P.W e := by
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    rw [P.run_port, P.W_eq]
    apply P.g_congr
    intro i
    simp only [decide_eq_true_eq, Bool.or_eq_true, Bool.false_eq_true, false_or]
    constructor
    · rintro (h | ⟨q, hq, -, hr⟩)
      · exact Or.inl h
      · exact Or.inr ⟨q, hq, by rw [← ih q (P.B_lt e i q hq)]; exact hr⟩
    · rintro (h | ⟨q, hq, hr⟩)
      · exact Or.inl h
      · exact Or.inr ⟨q, hq, Nat.zero_le _, by rw [ih q (P.B_lt e i q hq)]; exact hr⟩

/-- The true contribution vector at a node `[l, r)` lies in `𝒰(A^in_{[l,r)})`, and the local
run of `[l, r)` on it produces the true values `W_e`, `l ≤ e < r`. -/
theorem localRun_trueProfile (P : PortSystem a) (l r : ℕ) :
    restrictTo l r (P.unionVec {q | q < l ∧ P.W q = true}) ∈ P.closureIn l r ∧
    ∀ e, l ≤ e → e < r →
      P.run l (restrictTo l r (P.unionVec {q | q < l ∧ P.W q = true})) e = P.W e := by
  refine ⟨⟨_, fun q hq => hq.1, rfl⟩, ?_⟩
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    intro hle her
    rw [P.run_port, P.W_eq]
    apply P.g_congr
    intro i
    have h2 : l ≤ e ∧ e < r := ⟨hle, her⟩
    simp only [decide_eq_true_eq, Bool.or_eq_true, restrictTo_apply, PortSystem.unionVec_apply,
      Set.mem_setOf_eq, h2, true_and]
    constructor
    · rintro (h | ⟨q, hq, -, hW⟩ | ⟨q, hq, hlq, hr⟩)
      · exact Or.inl h
      · exact Or.inr ⟨q, hq, hW⟩
      · have hqe := P.B_lt e i q hq
        exact Or.inr ⟨q, hq, by rw [← ih q hqe hlq (by omega)]; exact hr⟩
    · rintro (h | ⟨q, hq, hW⟩)
      · exact Or.inl h
      · by_cases hql : q < l
        · exact Or.inr (Or.inl ⟨q, hq, hql, hW⟩)
        · have hqe := P.B_lt e i q hq
          exact Or.inr (Or.inr ⟨q, hq, by omega, by rw [ih q hqe (by omega) (by omega)]; exact hW⟩)

/-! ### Bounds on the union closure (Proposition 4.1) and the matching example -/

section Closure

variable {ρ κ : Type*} [Fintype ρ] [Fintype κ] [DecidableEq κ]

/-- The union of the columns `q ∈ S` of a Boolean matrix `A` (rows `ρ`, columns `κ`). -/
def unionOf (A : ρ → κ → Bool) (S : Finset κ) : ρ → Bool :=
  fun r => decide (∃ q ∈ S, A r q = true)

/-- The union closure `𝒰(A) = {⋁_{q ∈ S} a_q : S ⊆ cols(A)}`. -/
def unionClosure (A : ρ → κ → Bool) : Finset (ρ → Bool) :=
  (Finset.univ : Finset (Finset κ)).image (unionOf A)

omit [DecidableEq κ] in
/-- **Proposition 4.1 (1).** If `A` has at most `K` distinct rows, `|𝒰(A)| ≤ 2^K`. -/
theorem unionClosure_card_le_rows (A : ρ → κ → Bool) (K : ℕ)
    (hK : ((Finset.univ : Finset ρ).image A).card ≤ K) : (unionClosure A).card ≤ 2 ^ K := by
  set D := (Finset.univ : Finset ρ).image A
  let Φ : (D → Bool) → ρ → Bool := fun ψ r => ψ ⟨A r, Finset.mem_image_of_mem A (Finset.mem_univ r)⟩
  have hsub : unionClosure A ⊆ (Finset.univ : Finset (D → Bool)).image Φ := by
    intro v hv
    simp only [unionClosure, Finset.mem_image, Finset.mem_univ, true_and] at hv
    obtain ⟨S, rfl⟩ := hv
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun d => decide (∃ q ∈ S, d.1 q = true), rfl⟩
  calc (unionClosure A).card ≤ ((Finset.univ : Finset (D → Bool)).image Φ).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (D → Bool)).card := Finset.card_image_le
    _ = 2 ^ D.card := by rw [Finset.card_univ, Fintype.card_fun]; simp
    _ ≤ 2 ^ K := Nat.pow_le_pow_right (by decide) hK

omit [DecidableEq κ] in
/-- **Proposition 4.1 (2).** If `A` has at most `K` distinct columns, `|𝒰(A)| ≤ 2^K`. -/
theorem unionClosure_card_le_cols (A : ρ → κ → Bool) (K : ℕ)
    (hK : ((Finset.univ : Finset κ).image (fun q r => A r q)).card ≤ K) :
    (unionClosure A).card ≤ 2 ^ K := by
  set Dc := (Finset.univ : Finset κ).image (fun q r => A r q)
  let Φ : Finset (ρ → Bool) → ρ → Bool := fun T r => decide (∃ col ∈ T, col r = true)
  have hsub : unionClosure A ⊆ Dc.powerset.image Φ := by
    intro v hv
    simp only [unionClosure, Finset.mem_image, Finset.mem_univ, true_and] at hv
    obtain ⟨S, rfl⟩ := hv
    simp only [Finset.mem_image, Finset.mem_powerset]
    refine ⟨S.image (fun q r => A r q), Finset.image_subset_image (Finset.subset_univ S), ?_⟩
    funext r
    simp [Φ, unionOf]
  calc (unionClosure A).card ≤ (Dc.powerset.image Φ).card := Finset.card_le_card hsub
    _ ≤ Dc.powerset.card := Finset.card_image_le
    _ = 2 ^ Dc.card := Finset.card_powerset Dc
    _ ≤ 2 ^ K := Nat.pow_le_pow_right (by decide) hK

/-- **Proposition 4.1 (3).** If every row of `A` has at most `d` zeros, then
`|𝒰(A)| ≤ 1 + ∑_{i=0}^{d} (c choose i)`, `c` the number of columns. -/
theorem unionClosure_card_le_zeros (A : ρ → κ → Bool) (d : ℕ)
    (hd : ∀ r, ((Finset.univ : Finset κ).filter (fun q => A r q = false)).card ≤ d) :
    (unionClosure A).card ≤ 1 + ∑ i ∈ Finset.range (d + 1), (Fintype.card κ).choose i := by
  set small := (Finset.range (d + 1)).biUnion
    (fun i => Finset.powersetCard i (Finset.univ : Finset κ))
  have hsub : unionClosure A ⊆ insert (fun _ => true) (small.image (unionOf A)) := by
    intro v hv
    simp only [unionClosure, Finset.mem_image, Finset.mem_univ, true_and] at hv
    obtain ⟨S, rfl⟩ := hv
    by_cases hS : S.card ≤ d
    · apply Finset.mem_insert_of_mem
      refine Finset.mem_image.2 ⟨S, ?_, rfl⟩
      simp only [small, Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard]
      exact ⟨S.card, by omega, Finset.subset_univ S, rfl⟩
    · -- a union of more than `d` columns is the all-ones vector
      have hall : unionOf A S = fun _ => true := by
        funext r
        simp only [unionOf, decide_eq_true_eq]
        by_contra hno
        push Not at hno
        have hsub : S ⊆ (Finset.univ : Finset κ).filter (fun q => A r q = false) := by
          intro q hq
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          simpa using hno q hq
        have := Finset.card_le_card hsub
        have := hd r
        omega
      rw [hall]
      exact Finset.mem_insert_self _ _
  calc (unionClosure A).card ≤ (insert (fun _ => true) (small.image (unionOf A))).card :=
        Finset.card_le_card hsub
    _ ≤ (small.image (unionOf A)).card + 1 := Finset.card_insert_le _ _
    _ ≤ small.card + 1 := by
        have := Finset.card_image_le (s := small) (f := unionOf A)
        omega
    _ ≤ (∑ i ∈ Finset.range (d + 1), (Finset.powersetCard i (Finset.univ : Finset κ)).card) + 1 :=
        Nat.add_le_add_right Finset.card_biUnion_le 1
    _ = 1 + ∑ i ∈ Finset.range (d + 1), (Fintype.card κ).choose i := by
        rw [add_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.card_powersetCard, Finset.card_univ]

end Closure

/-- **Example 4.3 (matching).** The union closure of the `w × w` identity matrix has all `2^w`
vectors. -/
theorem matching_unionClosure_card (w : ℕ) :
    (unionClosure (fun r q : Fin w => decide (r = q))).card = 2 ^ w := by
  have hinj : Function.Injective (unionOf (fun r q : Fin w => decide (r = q))) := by
    intro S T h
    ext x
    have := congrFun h x
    simp only [unionOf, decide_eq_true_eq, exists_eq_right'] at this
    simpa using this
  rw [unionClosure, Finset.card_image_of_injective _ hinj, Finset.card_univ,
    Fintype.card_finset, Fintype.card_fin]

end GC.StructuralCompilers
