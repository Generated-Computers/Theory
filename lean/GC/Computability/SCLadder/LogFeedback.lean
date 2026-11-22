import GC.Computability.SCLadder.Basic

/-!
# Manuscript 008d: logarithmic feedback — transcript-conditioned affine summaries

For a block of stages with `h` feedback-sensitive stages, and an entering controller state `u`,
the run *forced* by a transcript `τ ∈ 𝔽₂^h` has a controller path independent of the data, and
along it the data evolve by an affine map `x ↦ M x + c`. The guard of `(u, τ)` says that each
forced bit equals the actually probed bit, an affine condition on the entering data `x`.

Main results (Lemma `lem:unique` of 008d, Lemma `lem:leaf` of 008a):

* `unique_transcript`: for every `u, x` exactly one transcript has its guard satisfied, and for
  it the run of the block from `(u, x)` ends at `(q_{u,τ}, M_{u,τ} x + c_{u,τ})`;
* every successful transcript has length `h` and its guard has exactly `h` rows, so there are
  at most `2^h` leaves per entering state (`card_transcripts`);
* `transcript_summary_exact`: the transcript leaves form an exact affine decision summary;
* `feedback_free_run` (Proposition `prop:feedbackfree` of 008a): without sensitive stages the run
  is `x ↦ (q, M x + c)` with `q, M, c` independent of `x`.

The circuit construction and its depth (`NC^2`) are not formalized.
-/

namespace GC.SCLadder

open Matrix Classical

variable {Q : Type*} {d : ℕ}

/-- A forced-run record: current controller state `q`, current data as the affine map
`x ↦ M x + c` of the entering data, and the guard equations collected so far. -/
structure Rec (Q : Type*) (d : ℕ) where
  q : Q
  M : Matrix (Fin d) (Fin d) F
  c : Data d
  guard : Guard d

/-- The initial record for entering state `u`. -/
def Rec.init (u : Q) : Rec Q d := ⟨u, 1, 0, []⟩

/-- The record after a stage, with the controller moved by bit `z`. -/
def Rec.next (s : Stage Q d) (r : Rec Q d) (z : F) (G : Guard d) : Rec Q d :=
  ⟨s.g r.q z, s.A r.q * r.M, s.A r.q *ᵥ r.c + s.b r.q, G⟩

/-- The run forced by a transcript `τ`: at a feedback-sensitive stage the next transcript bit is
used in place of the probe bit, and the guard equation `(M x + c)_a = τ_k` is recorded (as
`M_a ⬝ x = τ_k - c_a`); at a feedback-free stage the controller moves by `g(·,0)`. Returns `none`
if the transcript does not have exactly one bit per sensitive stage. -/
noncomputable def forced : List (Stage Q d) → Rec Q d → List F → Option (Rec Q d)
  | [], r, [] => some r
  | [], _, _ :: _ => none
  | s :: S, r, τ =>
    if s.Sensitive then
      match τ with
      | [] => none
      | z :: τ' => forced S
          (r.next s z (r.guard ++ [(r.M (s.addr r.q), z - r.c (s.addr r.q))])) τ'
    else forced S (r.next s 0 r.guard) τ

/-- The bits actually probed at the sensitive stages of the run from `c`. -/
noncomputable def probedBits : List (Stage Q d) → Q × Data d → List F
  | [], _ => []
  | s :: S, c =>
    if s.Sensitive then c.2 (s.addr c.1) :: probedBits S (s.step c) else probedBits S (s.step c)

/-- Number of feedback-sensitive stages. -/
noncomputable def numSensitive : List (Stage Q d) → ℕ
  | [] => 0
  | s :: S => (if s.Sensitive then 1 else 0) + numSensitive S

/-- Invariant: the record describes the actual state `(q, v)` reached from the data `x`. -/
def Rec.Describes (r : Rec Q d) (x : Data d) (c : Q × Data d) : Prop :=
  r.q = c.1 ∧ r.M *ᵥ x + r.c = c.2 ∧ r.guard.Holds x

lemma Rec.describes_init (u : Q) (x : Data d) : (Rec.init u : Rec Q d).Describes x (u, x) := by
  refine ⟨rfl, by simp [Rec.init], ?_⟩
  intro p hp
  simp [Rec.init] at hp

lemma Rec.describes_next' {s : Stage Q d} {r : Rec Q d} {x : Data d} {c : Q × Data d}
    (h : r.Describes x c) {z : F} (hz : s.g c.1 z = s.g c.1 (c.2 (s.addr c.1)))
    {G : Guard d} (hG : G.Holds x) :
    (r.next s z G).Describes x (s.step c) := by
  obtain ⟨h1, h2, -⟩ := h
  refine ⟨by simp [Rec.next, Stage.step, h1, hz], ?_, hG⟩
  simp only [Rec.next, Stage.step, h1]
  rw [← mulVec_mulVec, ← h2, mulVec_add, add_assoc]

lemma Rec.describes_next {s : Stage Q d} {r : Rec Q d} {x : Data d} {c : Q × Data d}
    (h : r.Describes x c) {G : Guard d} (hG : G.Holds x) :
    (r.next s (c.2 (s.addr c.1)) G).Describes x (s.step c) :=
  Rec.describes_next' h rfl hG

lemma Rec.describes_next_free {s : Stage Q d} (hs : ¬ s.Sensitive) {r : Rec Q d} {x : Data d}
    {c : Q × Data d} (h : r.Describes x c) {G : Guard d} (hG : G.Holds x) :
    (r.next s 0 G).Describes x (s.step c) :=
  Rec.describes_next' h (s.g_eq_of_not_sensitive hs _ _).symm hG

lemma row_eq (r : Rec Q d) (x : Data d) (a : Fin d) :
    r.M a ⬝ᵥ x = (r.M *ᵥ x) a := rfl

/-- Existence half: the actually probed transcript succeeds, and the final record describes
the actual final state. -/
lemma forced_probedBits (S : List (Stage Q d)) :
    ∀ (r : Rec Q d) (x : Data d) (c : Q × Data d), r.Describes x c →
      ∃ r', forced S r (probedBits S c) = some r' ∧ r'.Describes x (run S c) := by
  induction S with
  | nil => intro r x c h; exact ⟨r, by simp [forced, probedBits], h⟩
  | cons s S ih =>
    intro r x c h
    by_cases hs : s.Sensitive
    · simp only [probedBits, hs, ite_true, forced, run_cons]
      apply ih
      have hG : (r.guard ++ [(r.M (s.addr r.q), c.2 (s.addr c.1) - r.c (s.addr r.q))]).Holds x := by
        refine Guard.holds_append.mpr ⟨h.2.2, ?_⟩
        intro p hp
        simp only [List.mem_singleton] at hp
        subst hp
        simp only
        rw [row_eq, h.1, ← h.2.1]; simp
      exact Rec.describes_next h hG
    · simp only [probedBits, hs, ite_false, forced, run_cons]
      exact ih _ x _ (Rec.describes_next_free hs h h.2.2)

/-- The guard only grows along a forced run. -/
lemma forced_guard_holds (S : List (Stage Q d)) :
    ∀ (r r' : Rec Q d) (τ : List F) (x : Data d), forced S r τ = some r' →
      r'.guard.Holds x → r.guard.Holds x := by
  induction S with
  | nil =>
    intro r r' τ x h hx
    cases τ with
    | nil => simp [forced] at h; subst h; exact hx
    | cons _ _ => simp [forced] at h
  | cons s S ih =>
    intro r r' τ x h hx
    by_cases hs : s.Sensitive
    · simp only [forced, hs, ite_true] at h
      cases τ with
      | nil => simp at h
      | cons z τ' =>
        simp only at h
        exact (Guard.holds_append.mp (ih _ _ _ _ h hx)).1
    · simp only [forced, hs, ite_false] at h
      exact ih (r.next s 0 r.guard) _ _ _ h hx

/-- Uniqueness half: a transcript whose guard holds is the probed transcript. -/
lemma eq_probedBits_of_forced (S : List (Stage Q d)) :
    ∀ (r r' : Rec Q d) (τ : List F) (x : Data d) (c : Q × Data d), r.Describes x c →
      forced S r τ = some r' → r'.guard.Holds x → τ = probedBits S c := by
  induction S with
  | nil =>
    intro r r' τ x c _ h _
    cases τ with
    | nil => rfl
    | cons _ _ => simp [forced] at h
  | cons s S ih =>
    intro r r' τ x c hr h hx
    by_cases hs : s.Sensitive
    · simp only [forced, hs, ite_true] at h
      cases τ with
      | nil => simp at h
      | cons z τ' =>
        simp only at h
        have hg := forced_guard_holds S _ _ _ x h hx
        have hrow := (Guard.holds_append.mp hg).2 _ (List.mem_singleton_self _)
        simp only at hrow
        have hz : z = c.2 (s.addr c.1) := by
          have e1 := hr.1
          have e2 := hr.2.1
          rw [row_eq] at hrow
          rw [← e2, ← e1]
          simp only [Pi.add_apply]
          linear_combination -hrow
        subst hz
        simp only [probedBits, hs, ite_true]
        congr 1
        exact ih _ r' τ' x _ (Rec.describes_next hr hg) h hx
    · simp only [forced, hs, ite_false] at h
      simp only [probedBits, hs, ite_false]
      exact ih _ r' τ x _ (Rec.describes_next_free hs hr hr.2.2) h hx

/-- Any successful forced record from a record describing `c` describes the final state as soon
as its guard holds. -/
lemma forced_describes (S : List (Stage Q d)) (r r' : Rec Q d) (τ : List F) (x : Data d)
    (c : Q × Data d) (hr : r.Describes x c) (h : forced S r τ = some r')
    (hx : r'.guard.Holds x) : r'.Describes x (run S c) := by
  have hτ := eq_probedBits_of_forced S r r' τ x c hr h hx
  subst hτ
  obtain ⟨r'', h'', hd⟩ := forced_probedBits S r x c hr
  rw [h] at h''
  cases h''
  exact hd

/-- **Lemma `lem:unique` (008d) / Lemma `lem:leaf` (008a), exactness.** For every entering
state `u` and data `x`, exactly one transcript `τ` has a successful forced run whose guard holds
at `x`; for it, the run of the block from `(u, x)` ends at `(q_{u,τ}, M_{u,τ} x + c_{u,τ})`. -/
theorem unique_transcript (S : List (Stage Q d)) (u : Q) (x : Data d) :
    (∃! τ : List F, ∃ r, forced S (Rec.init u) τ = some r ∧ r.guard.Holds x) ∧
    ∀ τ r, forced S (Rec.init u) τ = some r → r.guard.Holds x →
      run S (u, x) = (r.q, r.M *ᵥ x + r.c) := by
  have hi := Rec.describes_init (d := d) u x
  refine ⟨?_, ?_⟩
  · obtain ⟨r, hr, hd⟩ := forced_probedBits S _ x _ hi
    refine ⟨probedBits S (u, x), ⟨r, hr, hd.2.2⟩, ?_⟩
    rintro τ ⟨r', h', hx'⟩
    exact eq_probedBits_of_forced S _ r' τ x _ hi h' hx'
  · intro τ r h hx
    have hd := forced_describes S _ r τ x _ hi h hx
    exact Prod.ext hd.1.symm hd.2.1.symm

/-- Successful transcripts have one bit per sensitive stage, and their guards one row per
sensitive stage. -/
lemma forced_length (S : List (Stage Q d)) :
    ∀ (r r' : Rec Q d) (τ : List F), forced S r τ = some r' →
      τ.length = numSensitive S ∧ r'.guard.length = r.guard.length + numSensitive S := by
  induction S with
  | nil =>
    intro r r' τ h
    cases τ with
    | nil => simp [forced] at h; subst h; simp [numSensitive]
    | cons _ _ => simp [forced] at h
  | cons s S ih =>
    intro r r' τ h
    by_cases hs : s.Sensitive
    · simp only [forced, hs, ite_true] at h
      cases τ with
      | nil => simp at h
      | cons z τ' =>
        simp only at h
        obtain ⟨h1, h2⟩ := ih _ _ _ h
        simp only [numSensitive, hs, ite_true, List.length_cons, h1, Rec.next] at h2 ⊢
        simp only [List.length_append, List.length_singleton] at h2
        omega
    · simp only [forced, hs, ite_false] at h
      obtain ⟨h1, h2⟩ := ih _ _ _ h
      simp only [numSensitive, hs, ite_false, Rec.next] at h2 ⊢
      omega

/-- At most `2^h` leaves per entering state: the successful transcripts form a subset of
`𝔽₂^h`, `h` the number of sensitive stages, and each guard has `h` rows. -/
theorem card_transcripts (S : List (Stage Q d)) (u : Q) :
    {τ : List F | ∃ r, forced S (Rec.init u) τ = some r}.ncard ≤ 2 ^ numSensitive S ∧
    ∀ τ r, forced S (Rec.init u) τ = some r → r.guard.length = numSensitive S := by
  refine ⟨?_, fun τ r h => by simpa [Rec.init] using (forced_length S _ r τ h).2⟩
  have hsub : {τ : List F | ∃ r, forced S (Rec.init u) τ = some r} ⊆
      {τ : List F | τ.length = numSensitive S} := by
    rintro τ ⟨r, h⟩
    exact (forced_length S _ r τ h).1
  have hfin : {τ : List F | τ.length = numSensitive S}.ncard = 2 ^ numSensitive S := by
    have e : {τ : List F | τ.length = numSensitive S} ≃ (Fin (numSensitive S) → F) :=
      { toFun := fun τ i => τ.1.get (i.cast τ.2.symm)
        invFun := fun f => ⟨List.ofFn f, by simp⟩
        left_inv := fun τ => by
          ext1
          simp only
          apply List.ext_get (by simpa using τ.2.symm)
          intro n h1 h2
          simp
        right_inv := fun f => by ext i; simp }
    rw [← Nat.card_coe_set_eq, Nat.card_congr e, Nat.card_fun]
    simp
  calc _ ≤ _ := Set.ncard_le_ncard hsub (Set.finite_of_ncard_pos (by rw [hfin]; positivity))
    _ = _ := hfin

/-- The transcript leaf `(u, τ)` (guard, exit state and exit map of the forced run). -/
noncomputable def transcriptLeaf (S : List (Stage Q d)) (i : Q × List F) : Leaf Q d :=
  let r := (forced S (Rec.init i.1) i.2).getD (Rec.init i.1)
  ⟨r.guard, r.q, r.M, r.c⟩

/-- The transcript leaves of entering state `u`: the transcripts with a successful forced run. -/
def transcriptLeaves (S : List (Stage Q d)) (u : Q) : Set (Q × List F) :=
  {i | i.1 = u ∧ ∃ r, forced S (Rec.init u) i.2 = some r}

/-- **Lemma `lem:leaf` (008a) / Lemma `lem:unique` (008d).** The transcript leaves form an exact
affine decision summary of the block. -/
theorem transcript_summary_exact (S : List (Stage Q d)) :
    IsExactSummary (fun u x => run S (u, x)) (transcriptLeaves S) (transcriptLeaf S) := by
  intro u x
  have key : ∀ i ∈ transcriptLeaves S u, ∃ r, forced S (Rec.init u) i.2 = some r ∧
      transcriptLeaf S i = ⟨r.guard, r.q, r.M, r.c⟩ := by
    rintro ⟨u', τ⟩ ⟨rfl, r, hr⟩
    exact ⟨r, hr, by simp [transcriptLeaf, hr]⟩
  obtain ⟨⟨τ0, ⟨r0, h0, hx0⟩, huniq⟩, hexit⟩ := unique_transcript S u x
  refine ⟨⟨(u, τ0), ⟨⟨rfl, r0, h0⟩, by simpa [transcriptLeaf, h0] using hx0⟩, ?_⟩, ?_⟩
  · rintro ⟨u', τ⟩ ⟨hmem, hx⟩
    obtain ⟨r, hr, hl⟩ := key _ hmem
    obtain ⟨rfl, -⟩ := hmem
    rw [hl] at hx
    rw [huniq τ ⟨r, hr, hx⟩]
  · intro i hi hx
    obtain ⟨r, hr, hl⟩ := key i hi
    rw [hl] at hx ⊢
    exact hexit _ r hr hx

/-- **Proposition `prop:feedbackfree` (008a), mathematical core.** If no stage is
feedback-sensitive, the forced run with the empty transcript succeeds and the whole block acts
as `x ↦ (q, M x + c)`, where `q, M, c` depend only on the entering state. -/
theorem feedback_free_run (S : List (Stage Q d)) (hS : ∀ s ∈ S, ¬ s.Sensitive) (u : Q) :
    ∃ r : Rec Q d, forced S (Rec.init u) [] = some r ∧
      ∀ x, run S (u, x) = (r.q, r.M *ᵥ x + r.c) := by
  have hnum : numSensitive S = 0 := by
    induction S with
    | nil => rfl
    | cons s S ih =>
      simp only [numSensitive, hS s (List.mem_cons_self ..), ite_false, zero_add]
      exact ih fun s' hs' => hS s' (List.mem_cons_of_mem _ hs')
  obtain ⟨r, hr, hd⟩ := forced_probedBits S (Rec.init u) 0 (u, 0) (Rec.describes_init u 0)
  have hpb : probedBits S ((u, 0) : Q × Data d) = [] := by
    have := (forced_length S _ r _ hr).1
    rw [hnum] at this
    exact List.eq_nil_of_length_eq_zero this
  rw [hpb] at hr
  refine ⟨r, hr, fun x => (unique_transcript S u x).2 [] r hr ?_⟩
  have := (forced_length S _ r _ hr).2
  rw [hnum] at this
  simp only [Rec.init, List.length_nil, add_zero] at this
  rw [List.eq_nil_of_length_eq_zero this]
  intro p hp; simp at hp

end GC.SCLadder
