import GC.Computability.SeqNORNormalForms.Basic

/-!
# 006f: Sequential NOR is circuit evaluation on its binary core

Resets `j_i = 0`, chronological negations `j_i = i - 1`, anchors `1 ≤ j_i ≤ i - 2`; an anchor
is guarded if `j_{i-1} = 0`. The binary core `B(j)` is the set of unguarded anchors. Core
variables are indexed here by the core position `b ∈ B(j)` itself instead of its rank `k`
(the rank is an order-preserving renaming).
-/

namespace GC.SeqNORNormalForms

/-- `i` is an unguarded anchor: `1 ≤ j_i ≤ i - 2` and `j_{i-1} ≠ 0`. -/
def IsCore (j : ℕ → ℕ) (i : ℕ) : Prop := 1 ≤ j i ∧ j i + 2 ≤ i ∧ j (i - 1) ≠ 0

instance (j : ℕ → ℕ) (i : ℕ) : Decidable (IsCore j i) := by unfold IsCore; infer_instance

/-- Predecessor of a non-root: `q - 1` for a chronological negation, `j_q` for a guarded
anchor. -/
def corePred (j : ℕ → ℕ) (q : ℕ) : ℕ := if j q = q - 1 then q - 1 else j q

/-- Descriptors: a constant or a signed reference `(b, σ)` to a core variable. -/
inductive Desc
  | const (c : Bool)
  | ref (b : ℕ) (σ : Bool)
  deriving DecidableEq, Repr

/-- Negation of a descriptor. -/
def Desc.neg : Desc → Desc
  | Desc.const c => Desc.const (!c)
  | Desc.ref b σ => Desc.ref b (!σ)

/-- Value `⟦d⟧(w)` of a descriptor. -/
def Desc.sem (w : ℕ → Bool) : Desc → Bool
  | Desc.const c => c
  | Desc.ref b σ => xor (w b) σ

/-- The descriptor `δ(q)`: `1` at `0`, `0` at resets, `(q, 0)` at core positions, and the
negated descriptor of the predecessor otherwise. -/
def desc (j : ℕ → ℕ) : ℕ → Desc
  | 0 => Desc.const true
  | q + 1 =>
      if j (q + 1) = 0 then Desc.const false
      else if IsCore j (q + 1) then Desc.ref (q + 1) false
      else if h : corePred j (q + 1) < q + 1 then (desc j (corePred j (q + 1))).neg
      else Desc.const false
termination_by q => q

/-- The variables mentioned by a descriptor. -/
def Desc.Mentions : Desc → ℕ → Prop
  | Desc.const _, _ => False
  | Desc.ref b _, b' => b = b'

theorem Desc.sem_neg (w : ℕ → Bool) (d : Desc) : d.neg.sem w = !(d.sem w) := by
  cases d <;> simp [Desc.neg, Desc.sem]

theorem Desc.neg_neg (d : Desc) : d.neg.neg = d := by cases d <;> simp [Desc.neg]

theorem Desc.sem_congr {w w' : ℕ → Bool} (d : Desc) (h : ∀ b, d.Mentions b → w b = w' b) :
    d.sem w = d.sem w' := by
  cases d with
  | const c => rfl
  | ref b σ => simp [Desc.sem, h b rfl]

section

variable (j : ℕ → ℕ)

/-- **Lemma 2.2 of 006f (root classification).** A coordinate `1 ≤ q ≤ n` that is neither a
reset nor a core position has a predecessor `p(q) < q` with `x_q = ¬ x_{p(q)}`. -/
theorem root_classification (n : ℕ) (hj : IsParentArray n j) (q : ℕ) (hq : 1 ≤ q) (hqn : q ≤ n)
    (h0 : j q ≠ 0) (hc : ¬ IsCore j q) :
    corePred j q < q ∧ trace j q = !trace j (corePred j q) := by
  have hjq := hj q hq hqn
  have ht := trace_at j q hq hjq
  unfold corePred
  split
  · next he => rw [he] at ht; refine ⟨by omega, ?_⟩; rw [ht]; cases trace j (q - 1) <;> rfl
  · next he =>
    -- guarded anchor: the shield `q - 1` is a reset
    have hsh : j (q - 1) = 0 := by unfold IsCore at hc; omega
    have hx : trace j (q - 1) = false := by
      have hq1 : 1 ≤ q - 1 := by omega
      rw [trace_at j (q - 1) hq1 (by rw [hsh]; omega), hsh, trace_zero]; simp [nor]
    refine ⟨hjq, ?_⟩
    rw [ht, hx]; simp [nor]

theorem desc_succ (q : ℕ) :
    desc j (q + 1) = if j (q + 1) = 0 then Desc.const false
      else if IsCore j (q + 1) then Desc.ref (q + 1) false
      else if h : corePred j (q + 1) < q + 1 then (desc j (corePred j (q + 1))).neg
      else Desc.const false := by
  rw [desc]

/-- **Section 3 of 006f (descriptor equation).** `x_q = ⟦δ(q)⟧(z)` for the true core vector `z` (`z_b = x_b`),
and `δ(q)` mentions only core positions `b ≤ q`. -/
theorem desc_correct (n : ℕ) (hj : IsParentArray n j) :
    ∀ q, q ≤ n → trace j q = (desc j q).sem (trace j) ∧
      ∀ b, (desc j q).Mentions b → IsCore j b ∧ 1 ≤ b ∧ b ≤ q := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro hqn
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · simp [desc, Desc.sem, trace_zero, Desc.Mentions]
    obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    rw [desc_succ]
    split
    · next h0 =>
      refine ⟨?_, by simp [Desc.Mentions]⟩
      rw [trace_at j (q + 1) (by omega) (by rw [h0]; omega), h0, trace_zero]
      simp [nor, Desc.sem]
    · next h0 =>
      split
      · next hc =>
        refine ⟨by simp [Desc.sem], ?_⟩
        intro b hb
        simp only [Desc.Mentions] at hb
        subst hb
        exact ⟨hc, by omega, le_rfl⟩
      · next hc =>
        obtain ⟨hlt, hx⟩ := root_classification j n hj (q + 1) (by omega) hqn h0 hc
        rw [dif_pos hlt]
        obtain ⟨ih1, ih2⟩ := ih _ hlt (by omega)
        refine ⟨by rw [hx, ih1, Desc.sem_neg], ?_⟩
        intro b hb
        have : (desc j (corePred j (q + 1))).Mentions b := by
          cases hd : desc j (corePred j (q + 1)) <;> rw [hd] at hb <;>
            simpa [Desc.neg, Desc.Mentions] using hb
        obtain ⟨h1, h2, h3⟩ := ih2 b this
        exact ⟨h1, h2, by omega⟩

/-- The core system (Definition 3.1 of 006f): `w_b = NOR(⟦L_b⟧ w, ⟦R_b⟧ w)` for every core position
`b ≤ n`, with `L_b = δ(b-1)` and `R_b = δ(j_b)`. -/
def CoreSystemHolds (n : ℕ) (w : ℕ → Bool) : Prop :=
  ∀ b, 1 ≤ b → b ≤ n → IsCore j b →
    w b = nor ((desc j (b - 1)).sem w) ((desc j (j b)).sem w)

/-- **Lemma 3.2 of 006f (triangularity).** The descriptors `L_b`, `R_b` of the equation of a
core position `b` mention only core positions `< b`. -/
theorem core_triangular (n : ℕ) (hj : IsParentArray n j) (b : ℕ) (hb : 1 ≤ b) (hbn : b ≤ n)
    (hc : IsCore j b) :
    (∀ b', (desc j (b - 1)).Mentions b' → IsCore j b' ∧ b' < b) ∧
    (∀ b', (desc j (j b)).Mentions b' → IsCore j b' ∧ b' < b) := by
  have hjb := hj b hb hbn
  constructor
  · intro b' h; have := (desc_correct j n hj (b - 1) (by omega)).2 b' h; exact ⟨this.1, by omega⟩
  · intro b' h; have := (desc_correct j n hj (j b) (by omega)).2 b' h; exact ⟨this.1, by omega⟩

/-- **Lemma 3.2 of 006f (unique solution).** The true core vector solves the core system, and
every solution agrees with it on all core positions `≤ n`. -/
theorem core_system_unique (n : ℕ) (hj : IsParentArray n j) :
    CoreSystemHolds j n (trace j) ∧
    ∀ w, CoreSystemHolds j n w → ∀ b, 1 ≤ b → b ≤ n → IsCore j b → w b = trace j b := by
  constructor
  · intro b hb hbn hc
    have hjb := hj b hb hbn
    rw [trace_at j b hb hjb, ← (desc_correct j n hj (b - 1) (by omega)).1,
      ← (desc_correct j n hj (j b) (by omega)).1]
  · intro w hw b
    induction b using Nat.strong_induction_on with
    | _ b ih =>
      intro hb hbn hc
      have hjb := hj b hb hbn
      obtain ⟨hL, hR⟩ := core_triangular j n hj b hb hbn hc
      rw [hw b hb hbn hc, trace_at j b hb hjb, (desc_correct j n hj (b - 1) (by omega)).1,
        (desc_correct j n hj (j b) (by omega)).1]
      congr 1
      · apply Desc.sem_congr; intro b' hm
        have h1 := (desc_correct j n hj (b - 1) (by omega)).2 b' hm
        exact ih b' (hL b' hm).2 h1.2.1 (by omega) h1.1
      · apply Desc.sem_congr; intro b' hm
        have h1 := (desc_correct j n hj (j b) (by omega)).2 b' hm
        exact ih b' (hR b' hm).2 h1.2.1 (by omega) h1.1

/-- **Theorem 3.4 of 006f (retraction), mathematical content.** Substituting any solution of
the core system into the descriptors gives the whole trace. -/
theorem retraction (n : ℕ) (hj : IsParentArray n j) (w : ℕ → Bool)
    (hw : CoreSystemHolds j n w) : ∀ q, q ≤ n → (desc j q).sem w = trace j q := by
  intro q hq
  obtain ⟨h1, h2⟩ := desc_correct j n hj q hq
  rw [h1]
  apply Desc.sem_congr
  intro b hb
  obtain ⟨hc, hb1, hbq⟩ := h2 b hb
  exact (core_system_unique j n hj).2 w hw b hb1 (by omega) hc

end

/-! ### Four-coordinate universality (Section 5) -/

/-- A source of a gate of an ordered NOR circuit: an input `a_ℓ` (`1 ≤ ℓ ≤ t`) or an earlier
gate `w_ℓ`. -/
inductive CSrc
  | inp (ℓ : ℕ)
  | gate (ℓ : ℕ)
  deriving DecidableEq, Repr

/-- An ordered NOR circuit with `t` assigned inputs `a_1, …, a_t` and gates
`w_i = NOR(u_i, v_i)`, `1 ≤ i ≤ G`. -/
structure OrderedNorCircuit where
  t : ℕ
  G : ℕ
  a : ℕ → Bool
  u : ℕ → CSrc
  v : ℕ → CSrc

/-- A source is legal for gate `i`. -/
def OrderedNorCircuit.SrcOK (C : OrderedNorCircuit) (i : ℕ) : CSrc → Prop
  | CSrc.inp ℓ => 1 ≤ ℓ ∧ ℓ ≤ C.t
  | CSrc.gate ℓ => 1 ≤ ℓ ∧ ℓ < i

/-- Well-formedness. -/
def OrderedNorCircuit.Valid (C : OrderedNorCircuit) : Prop :=
  ∀ i, 1 ≤ i → i ≤ C.G → C.SrcOK i (C.u i) ∧ C.SrcOK i (C.v i)

/-- Gate values. -/
def OrderedNorCircuit.gateVal (C : OrderedNorCircuit) : ℕ → Bool
  | 0 => false
  | i + 1 =>
      nor (match C.u (i + 1) with
            | CSrc.inp ℓ => C.a ℓ
            | CSrc.gate ℓ => if h : ℓ < i + 1 then C.gateVal ℓ else false)
          (match C.v (i + 1) with
            | CSrc.inp ℓ => C.a ℓ
            | CSrc.gate ℓ => if h : ℓ < i + 1 then C.gateVal ℓ else false)
termination_by i => i

/-- Value of a source. -/
def OrderedNorCircuit.srcVal (C : OrderedNorCircuit) : CSrc → Bool
  | CSrc.inp ℓ => C.a ℓ
  | CSrc.gate ℓ => C.gateVal ℓ

/-- Representative coordinate: `Rep(a_ℓ) = 2ℓ + 1`, `Rep(w_i) = 2t + 4i + 1`. -/
def OrderedNorCircuit.rep (C : OrderedNorCircuit) : CSrc → ℕ
  | CSrc.inp ℓ => 2 * ℓ + 1
  | CSrc.gate i => 2 * C.t + 4 * i + 1

/-- **Definition 5.1 of 006f.** `Embed(C)`: the permanent zero `j_1 = 0`, the input gadget
`j_{2ℓ} = 0`, `j_{2ℓ+1} = a_ℓ` at `(2ℓ, 2ℓ+1)`, and the NOR gadget
`j_s = 0, j_{s+1} = Rep(u_i), j_{s+2} = s + 1, j_{s+3} = Rep(v_i)` at `s = 2t + 4i - 2`. -/
def OrderedNorCircuit.embed (C : OrderedNorCircuit) (q : ℕ) : ℕ :=
  if q ≤ 1 then 0
  else if q ≤ 2 * C.t + 1 then
    (if q % 2 = 0 then 0 else if C.a (q / 2) then 1 else 0)
  else
    let i := (q - (2 * C.t + 2)) / 4 + 1
    let r := (q - (2 * C.t + 2)) % 4
    if r = 0 then 0
    else if r = 1 then C.rep (C.u i)
    else if r = 2 then q - 1
    else C.rep (C.v i)

/-- Length `n = 1 + 2t + 4G` of the embedding. -/
def OrderedNorCircuit.len (C : OrderedNorCircuit) : ℕ := 1 + 2 * C.t + 4 * C.G

section Embed

variable (C : OrderedNorCircuit)

theorem rep_ge (C : OrderedNorCircuit) {i : ℕ} {s : CSrc} (h : C.SrcOK i s) : 3 ≤ C.rep s := by
  cases s <;> simp [OrderedNorCircuit.SrcOK, OrderedNorCircuit.rep] at h ⊢ <;> omega

theorem rep_lt (C : OrderedNorCircuit) {i : ℕ} {s : CSrc} (hi : 1 ≤ i) (h : C.SrcOK i s) :
    C.rep s + 1 ≤ 2 * C.t + 4 * i - 2 := by
  cases s <;> simp [OrderedNorCircuit.SrcOK, OrderedNorCircuit.rep] at h ⊢ <;> omega

theorem embed_one : C.embed 1 = 0 := by simp [OrderedNorCircuit.embed]

theorem embed_inp {ℓ : ℕ} (h1 : 1 ≤ ℓ) (ht : ℓ ≤ C.t) :
    C.embed (2 * ℓ) = 0 ∧ C.embed (2 * ℓ + 1) = if C.a ℓ then 1 else 0 := by
  unfold OrderedNorCircuit.embed
  constructor
  · rw [if_neg (by omega), if_pos (by omega), if_pos (by omega)]
  · rw [if_neg (by omega), if_pos (by omega), if_neg (by omega),
      show (2 * ℓ + 1) / 2 = ℓ by omega]

theorem embed_gate {i : ℕ} (h1 : 1 ≤ i) :
    let s := 2 * C.t + 4 * i - 2
    C.embed s = 0 ∧ C.embed (s + 1) = C.rep (C.u i) ∧ C.embed (s + 2) = s + 1 ∧
      C.embed (s + 3) = C.rep (C.v i) := by
  intro s
  have key : ∀ r, r < 4 → C.embed (s + r) =
      if r = 0 then 0 else if r = 1 then C.rep (C.u i) else if r = 2 then s + r - 1
      else C.rep (C.v i) := by
    intro r hr
    unfold OrderedNorCircuit.embed
    rw [if_neg (by omega), if_neg (by omega)]
    simp only []
    rw [show (s + r - (2 * C.t + 2)) / 4 + 1 = i by omega,
      show (s + r - (2 * C.t + 2)) % 4 = r by omega]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using key 0 (by omega)
  · simpa using key 1 (by omega)
  · have := key 2 (by omega); simp at this; rw [this]; try omega
  · simpa using key 3 (by omega)

/-- Every position of the embedding is position `1`, in an input gadget, or in a NOR
gadget. -/
theorem embed_pos_cases (q : ℕ) (h1 : 1 ≤ q) (hn : q ≤ C.len) :
    q = 1 ∨ (∃ ℓ, 1 ≤ ℓ ∧ ℓ ≤ C.t ∧ (q = 2 * ℓ ∨ q = 2 * ℓ + 1)) ∨
      (∃ i r, 1 ≤ i ∧ i ≤ C.G ∧ r < 4 ∧ q = 2 * C.t + 4 * i - 2 + r) := by
  unfold OrderedNorCircuit.len at hn
  by_cases hq1 : q = 1
  · exact Or.inl hq1
  by_cases hq2 : q ≤ 2 * C.t + 1
  · exact Or.inr (Or.inl ⟨q / 2, by omega, by omega, by omega⟩)
  · exact Or.inr (Or.inr ⟨(q - (2 * C.t + 2)) / 4 + 1, (q - (2 * C.t + 2)) % 4, by omega,
      by omega, by omega, by omega⟩)

/-- **Theorem 5.2 of 006f (four-coordinate universality).** For every ordered NOR circuit
with `t` inputs and `G` gates, `j = Embed(C)` is a parent array of length `1 + 2t + 4G` with
`x_{Rep(y)} = y` for every input and gate `y` (so `x_n = w_G`); its binary core is exactly
`{Rep(w_1) < … < Rep(w_G)}`; the descriptors are `δ(Rep(a_ℓ)) = a_ℓ` and
`δ(Rep(w_i)) = (Rep(w_i), 0)`; and the core equation of `Rep(w_i)` is
`L = δ(Rep(u_i))`, `R = δ(Rep(v_i))`, i.e. exactly the gate equation of `C`. -/
theorem embed_universal (hC : C.Valid) :
    IsParentArray C.len C.embed ∧
    (∀ ℓ, 1 ≤ ℓ → ℓ ≤ C.t → trace C.embed (C.rep (CSrc.inp ℓ)) = C.a ℓ ∧
      desc C.embed (C.rep (CSrc.inp ℓ)) = Desc.const (C.a ℓ)) ∧
    (∀ i, 1 ≤ i → i ≤ C.G → trace C.embed (C.rep (CSrc.gate i)) = C.gateVal i ∧
      desc C.embed (C.rep (CSrc.gate i)) = Desc.ref (C.rep (CSrc.gate i)) false ∧
      desc C.embed (C.rep (CSrc.gate i) - 1) = desc C.embed (C.rep (C.u i)) ∧
      desc C.embed (C.embed (C.rep (CSrc.gate i))) = desc C.embed (C.rep (C.v i))) ∧
    (∀ q, 1 ≤ q → q ≤ C.len → (IsCore C.embed q ↔ ∃ i, 1 ≤ i ∧ i ≤ C.G ∧ q = C.rep (CSrc.gate i)))
    ∧ (1 ≤ C.G → trace C.embed C.len = C.gateVal C.G) := by
  have hj1 : C.embed 1 = 0 := embed_one C
  -- parent array
  have hpa : IsParentArray C.len C.embed := by
    intro q h1 hn
    rcases embed_pos_cases C q h1 hn with rfl | ⟨ℓ, hl1, hlt, rfl | rfl⟩ | ⟨i, r, hi1, hiG, hr, rfl⟩
    · rw [hj1]; omega
    · rw [(embed_inp C hl1 hlt).1]; omega
    · rw [(embed_inp C hl1 hlt).2]; split <;> omega
    · obtain ⟨g0, g1, g2, g3⟩ := embed_gate C hi1
      obtain ⟨hu, hv⟩ := hC i hi1 hiG
      have hu' := rep_lt C hi1 hu
      have hv' := rep_lt C hi1 hv
      interval_cases r
      · simp only [Nat.add_zero]; rw [g0]; omega
      · rw [g1]; omega
      · rw [g2]; omega
      · rw [g3]; omega
  have hx1 : trace C.embed 1 = false := by
    rw [trace_step C.embed 1 0 le_rfl hj1 (by omega)]; simp [trace_zero, nor]
  have hd1 : desc C.embed 1 = Desc.const false := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, desc_succ]; simp [hj1]
  -- inputs
  have hinp : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ C.t → trace C.embed (2 * ℓ) = false ∧ desc C.embed (2 * ℓ) = Desc.const false ∧
      trace C.embed (C.rep (CSrc.inp ℓ)) = C.a ℓ ∧ desc C.embed (C.rep (CSrc.inp ℓ)) = Desc.const (C.a ℓ) := by
    intro ℓ hl1 hlt
    obtain ⟨e0, e1⟩ := embed_inp C hl1 hlt
    have hs : trace C.embed (2 * ℓ) = false := by
      rw [trace_step C.embed (2 * ℓ) 0 (by omega) e0 (by omega), trace_zero]; simp [nor]
    have hds : desc C.embed (2 * ℓ) = Desc.const false := by
      obtain ⟨m, hm⟩ : ∃ m, 2 * ℓ = m + 1 := ⟨2 * ℓ - 1, by omega⟩
      rw [hm, desc_succ, if_pos (by rw [← hm]; exact e0)]
    refine ⟨hs, hds, ?_, ?_⟩
    · simp only [OrderedNorCircuit.rep]
      cases ha : C.a ℓ
      · rw [ha] at e1; simp at e1
        rw [trace_step C.embed _ 0 (by omega) e1 (by omega), trace_zero]; simp [nor]
      · rw [ha] at e1; simp at e1
        rw [trace_step C.embed _ 1 (by omega) e1 (by omega), hx1, show 2 * ℓ + 1 - 1 = 2 * ℓ by omega,
          hs]; rfl
    · simp only [OrderedNorCircuit.rep]
      rw [desc_succ]
      cases ha : C.a ℓ
      · rw [ha] at e1; simp at e1; simp [e1]
      · rw [ha] at e1; simp at e1
        have hnc : ¬ IsCore C.embed (2 * ℓ + 1) := by
          unfold IsCore; rw [show 2 * ℓ + 1 - 1 = 2 * ℓ by omega, e0]; omega
        have hp : corePred C.embed (2 * ℓ + 1) = 1 := by unfold corePred; rw [e1]; split <;> omega
        rw [if_neg (by omega), if_neg hnc, dif_pos (by omega), hp, hd1]; rfl
  -- gates
  have hgate : ∀ i, 1 ≤ i → i ≤ C.G →
      trace C.embed (C.rep (CSrc.gate i)) = C.gateVal i ∧
      desc C.embed (C.rep (CSrc.gate i)) = Desc.ref (C.rep (CSrc.gate i)) false ∧
      desc C.embed (C.rep (CSrc.gate i) - 1) = desc C.embed (C.rep (C.u i)) ∧
      desc C.embed (C.embed (C.rep (CSrc.gate i))) = desc C.embed (C.rep (C.v i)) ∧
      trace C.embed (C.rep (CSrc.gate i) + 1 - 1) = C.gateVal i := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi1 hiG
      obtain ⟨hu, hv⟩ := hC i hi1 hiG
      have hu3 := rep_ge C hu
      have hv3 := rep_ge C hv
      have hu' := rep_lt C hi1 hu
      have hv' := rep_lt C hi1 hv
      obtain ⟨g0, g1, g2, g3⟩ := embed_gate C hi1
      set s := 2 * C.t + 4 * i - 2 with hs
      have hrep : C.rep (CSrc.gate i) = s + 3 := by simp [OrderedNorCircuit.rep]; omega
      -- values of the sources
      have hsrc : ∀ y, C.SrcOK i y → trace C.embed (C.rep y) = C.srcVal y ∧
          desc C.embed (C.rep y) = match y with
            | CSrc.inp ℓ => Desc.const (C.a ℓ)
            | CSrc.gate ℓ => Desc.ref (C.rep (CSrc.gate ℓ)) false := by
        intro y hy
        cases y with
        | inp ℓ =>
          simp only [OrderedNorCircuit.SrcOK] at hy
          obtain ⟨-, -, h1, h2⟩ := hinp ℓ hy.1 hy.2
          exact ⟨h1, h2⟩
        | gate ℓ =>
          simp only [OrderedNorCircuit.SrcOK] at hy
          obtain ⟨h1, h2, -⟩ := ih ℓ hy.2 hy.1 (by omega)
          exact ⟨h1, h2⟩
      have xs : trace C.embed s = false := by
        rw [trace_step C.embed s 0 (by omega) g0 (by omega), trace_zero]; simp [nor]
      have x1 : trace C.embed (s + 1) = !C.srcVal (C.u i) := by
        rw [trace_step C.embed (s + 1) _ (by omega) g1 (by omega), Nat.add_sub_cancel, xs,
          (hsrc _ hu).1]; simp [nor]
      have x2 : trace C.embed (s + 2) = C.srcVal (C.u i) := by
        rw [trace_step C.embed (s + 2) _ (by omega) g2 (by omega), show s + 2 - 1 = s + 1 by omega, x1]
        cases C.srcVal (C.u i) <;> rfl
      have x3 : trace C.embed (s + 3) = C.gateVal i := by
        rw [trace_step C.embed (s + 3) _ (by omega) g3 (by omega), show s + 3 - 1 = s + 2 by omega, x2,
          (hsrc _ hv).1]
        obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        rw [OrderedNorCircuit.gateVal]
        cases hU : C.u (i' + 1) <;> cases hV : C.v (i' + 1) <;> rw [hU] at hu <;> rw [hV] at hv <;>
          simp only [OrderedNorCircuit.SrcOK] at hu hv <;>
          simp [OrderedNorCircuit.srcVal, show ∀ ℓ, ℓ < i' + 1 → (ℓ < i' + 1) = True from
            fun ℓ h => by simp [h], hu.2, hv.2]
      -- descriptors
      have ds1 : desc C.embed (s + 1) = (desc C.embed (C.rep (C.u i))).neg := by
        rw [desc_succ, g1, if_neg (by omega)]
        have hnc : ¬ IsCore C.embed (s + 1) := by
          unfold IsCore; rw [Nat.add_sub_cancel, g0]; omega
        have hp : corePred C.embed (s + 1) = C.rep (C.u i) := by
          unfold corePred; rw [g1]; split <;> omega
        rw [if_neg hnc, hp, dif_pos (by omega)]
      have ds2 : desc C.embed (s + 2) = desc C.embed (C.rep (C.u i)) := by
        rw [show s + 2 = (s + 1) + 1 from rfl, desc_succ, g2, if_neg (by omega)]
        have hnc : ¬ IsCore C.embed (s + 1 + 1) := by unfold IsCore; rw [g2]; omega
        have hp : corePred C.embed (s + 1 + 1) = s + 1 := by unfold corePred; rw [g2]; simp
        rw [if_neg hnc, hp, dif_pos (by omega), ds1, Desc.neg_neg]
      have hcore : IsCore C.embed (s + 3) := by
        unfold IsCore; rw [g3, show s + 3 - 1 = s + 2 by omega, g2]; omega
      have ds3 : desc C.embed (s + 3) = Desc.ref (s + 3) false := by
        rw [show s + 3 = (s + 2) + 1 from rfl, desc_succ, g3, if_neg (by omega), if_pos hcore]
      rw [hrep]
      exact ⟨x3, ds3, by rw [show s + 3 - 1 = s + 2 by omega, ds2], by rw [g3],
        by rw [Nat.add_sub_cancel]; exact x3⟩
  refine ⟨hpa, fun ℓ h1 h2 => (hinp ℓ h1 h2).2.2, fun i h1 h2 => ?_, ?_, ?_⟩
  · obtain ⟨a, b, c, d, -⟩ := hgate i h1 h2; exact ⟨a, b, c, d⟩
  · intro q h1 hn
    constructor
    · intro hc
      rcases embed_pos_cases C q h1 hn with rfl | ⟨ℓ, hl1, hlt, rfl | rfl⟩ | ⟨i, r, hi1, hiG, hr, rfl⟩
      · unfold IsCore at hc; rw [hj1] at hc; omega
      · unfold IsCore at hc; rw [(embed_inp C hl1 hlt).1] at hc; omega
      · unfold IsCore at hc
        rw [show 2 * ℓ + 1 - 1 = 2 * ℓ by omega, (embed_inp C hl1 hlt).1] at hc; omega
      · obtain ⟨g0, g1, g2, g3⟩ := embed_gate C hi1
        obtain ⟨hu, hv⟩ := hC i hi1 hiG
        have hu3 := rep_ge C hu
        interval_cases r
        · unfold IsCore at hc; simp only [Nat.add_zero] at hc; rw [g0] at hc; omega
        · unfold IsCore at hc; rw [Nat.add_sub_cancel, g0] at hc; omega
        · unfold IsCore at hc; rw [g2] at hc; omega
        · exact ⟨i, hi1, hiG, by simp [OrderedNorCircuit.rep]; omega⟩
    · rintro ⟨i, hi1, hiG, rfl⟩
      obtain ⟨g0, g1, g2, g3⟩ := embed_gate C hi1
      obtain ⟨hu, hv⟩ := hC i hi1 hiG
      have hv3 := rep_ge C hv
      have hv' := rep_lt C hi1 hv
      have hrep : C.rep (CSrc.gate i) = 2 * C.t + 4 * i - 2 + 3 := by
        simp [OrderedNorCircuit.rep]; omega
      rw [hrep]; unfold IsCore
      rw [g3, show 2 * C.t + 4 * i - 2 + 3 - 1 = 2 * C.t + 4 * i - 2 + 2 by omega, g2]
      omega
  · intro hG
    have := (hgate C.G hG le_rfl).1
    rw [show C.len = C.rep (CSrc.gate C.G) by simp [OrderedNorCircuit.len, OrderedNorCircuit.rep]; omega]
    exact this

end Embed

end GC.SeqNORNormalForms
