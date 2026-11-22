import GC.Computability.Portals.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Data.ZMod.Basic

/-!
# Control observability erases payload in trace generation (manuscript 005f)

* `AffineMachine`: the affine history machine of Section 2 over `ℚ`. The configuration after
  step `t` is `(q_t, x_t, H)`; step `t + 1` reads the address `p = c_p x_t`, the branch bit
  `b = [c_z x_t > 0]`, the cell `H[p]`, appends `H[m + t + 1] = c_w x_t`, and updates
  `x_{t+1} = A(q_t, b) x_t + u H[p] + a(q_t, b)`, `q_{t+1} = δ(q_t, b)`. An address that is not a
  natural number below `m + t + 1` reads `0` (a fixed convention; normalized executions never
  use it).
* `control_observable_sufficiency`: Theorem "Control-observable state suffices", in its precise
  two-execution form: a second execution started at a cut `τ` that agrees with the first on the
  control state, on the functionals of `L_τ`, on the external history and on the control-live
  cells, has the same addresses, branch bits and control states on the rest of the interval.
  (Steps are indexed by the configuration they start from: "step `t + 1`" starts from time `t`.)
* `ladder_rank`, `ladder_pred_ne`, `card_ladderEdges`: Theorem "Linear-incidence balanced
  ladders": in the ladder `D_{r,w}` every vertex of layer `k` has Strahler rank `k`, the two
  predecessors are distinct, and there are exactly `2 r w` edges.
* The linear separator budget and the counting part of the separator transfer are
  `separator_budget`, `heavy_mul_lt` and `online_transfer_calls` (file `SeparatorSpeedups`).

Not formalized: the least-closure lemma (existence of the least closure by backward
recursion), the asymptotic corollary on `N / log² N`, and the complexity statements.
-/

namespace GC.Portals

open Matrix

/-- An affine history machine with `d` rational registers and control set `Q`. -/
structure AffineMachine (d : ℕ) (Q : Type*) where
  cp : Fin d → ℚ
  cz : Fin d → ℚ
  cw : Fin d → ℚ
  u : Fin d → ℚ
  A : Q → Bool → Matrix (Fin d) (Fin d) ℚ
  a : Q → Bool → Fin d → ℚ
  δ : Q → Bool → Q

/-- A configuration: control state, register vector and history (cells beyond the current
length are irrelevant). -/
structure Cfg (d : ℕ) (Q : Type*) where
  q : Q
  x : Fin d → ℚ
  H : ℕ → ℚ

/-- `r` is a valid address of a history of length `len`: a natural number below `len`. -/
def ValidAddr (len : ℕ) (r : ℚ) : Prop := ((⌊r⌋₊ : ℕ) : ℚ) = r ∧ ⌊r⌋₊ < len

instance (len : ℕ) (r : ℚ) : Decidable (ValidAddr len r) := by
  unfold ValidAddr; infer_instance

/-- Reading the history at a rational address (`0` for an invalid address). -/
def readAt (H : ℕ → ℚ) (len : ℕ) (r : ℚ) : ℚ := if ValidAddr len r then H ⌊r⌋₊ else 0

namespace AffineMachine

variable {d : ℕ} {Q : Type*} (M : AffineMachine d Q) (m : ℕ)

/-- The address computed from a configuration. -/
def addr (c : Cfg d Q) : ℚ := M.cp ⬝ᵥ c.x

/-- The branch bit computed from a configuration. -/
def branch (c : Cfg d Q) : Bool := decide (0 < M.cz ⬝ᵥ c.x)

/-- Step `t` of the machine (with initial history `H[0..m]`), applied to the configuration
after step `t - 1`. -/
def step (t : ℕ) (c : Cfg d Q) : Cfg d Q where
  q := M.δ c.q (M.branch c)
  x := M.A c.q (M.branch c) *ᵥ c.x + readAt c.H (m + t) (M.addr c) • M.u + M.a c.q (M.branch c)
  H := Function.update c.H (m + t) (M.cw ⬝ᵥ c.x)

/-- The address read at step `t + 1` of the execution `X`, as a natural number. -/
def readAddr (X : ℕ → Cfg d Q) (t : ℕ) : ℕ := ⌊M.addr (X t)⌋₊

/-- A closure for the (exact) trace of `X` on the interval `I = {a + 1, …, b}`
(conditions (C1)–(C3); the condition for step `t + 1 ∈ I` is stated for `a ≤ t < b`). -/
structure IsClosure (X : ℕ → Cfg d Q) (a b : ℕ) (L : ℕ → Submodule ℚ (Fin d → ℚ)) : Prop where
  c1p : ∀ t, a ≤ t → t < b → M.cp ∈ L t
  c1z : ∀ t, a ≤ t → t < b → M.cz ∈ L t
  c2 : ∀ t, a ≤ t → t < b → ∀ ℓ ∈ L (t + 1), ℓ ᵥ* M.A (X t).q (M.branch (X t)) ∈ L t
  c3 : ∀ t, a ≤ t → t < b → m + a < M.readAddr X t → (∃ ℓ ∈ L (t + 1), ℓ ⬝ᵥ M.u ≠ 0) →
    M.cw ∈ L (M.readAddr X t - m - 1)

/-- The read at step `t + 1` is demanded: it lies in `I`, it is internal to `I`, and some
`ℓ ∈ L_{t+1}` has `ℓ u ≠ 0`. -/
def Demanded (X : ℕ → Cfg d Q) (a b : ℕ) (L : ℕ → Submodule ℚ (Fin d → ℚ)) (t : ℕ) : Prop :=
  a ≤ t ∧ t < b ∧ m + a < M.readAddr X t ∧ ∃ ℓ ∈ L (t + 1), ℓ ⬝ᵥ M.u ≠ 0

/-- The cell written at step `s ∈ I` is control-live at the cut `τ`: `s ≤ τ` and some demanded
read at a step after `τ` reads it. -/
def Live (X : ℕ → Cfg d Q) (a b : ℕ) (L : ℕ → Submodule ℚ (Fin d → ℚ)) (s τ : ℕ) : Prop :=
  a < s ∧ s ≤ τ ∧ ∃ t, τ ≤ t ∧ M.Demanded m X a b L t ∧ M.readAddr X t = m + s

/-- Theorem (control-observable state suffices). Let `X` be an execution, normalized on
`I = {a+1, …, b}`, let `L` be a closure for its trace on `I`, and let `a ≤ τ ≤ b`. Let `X'` be an
execution started at time `τ` such that (a) its control state, (b) the values of all
functionals of `L_τ` on its registers, (c) its history cells `H[j]`, `j ≤ m + a`, and (d) its
history cells written at control-live steps agree with those of `X` at time `τ`. Then at every
step of `{τ+1, …, b}` the two executions have the same addresses, branch bits and control
states (in particular `X'` is normalized there). -/
theorem control_observable_sufficiency (X X' : ℕ → Cfg d Q) (a b τ : ℕ)
    (hX : ∀ t, X (t + 1) = M.step m (t + 1) (X t))
    (hnorm : ∀ t, a ≤ t → t < b → ValidAddr (m + (t + 1)) (M.addr (X t)))
    (L : ℕ → Submodule ℚ (Fin d → ℚ)) (hL : M.IsClosure m X a b L)
    (haτ : a ≤ τ) (hτb : τ ≤ b)
    (hX' : ∀ t, τ ≤ t → X' (t + 1) = M.step m (t + 1) (X' t))
    (hqa : (X' τ).q = (X τ).q)
    (hxb : ∀ ℓ ∈ L τ, ℓ ⬝ᵥ (X' τ).x = ℓ ⬝ᵥ (X τ).x)
    (hHc : ∀ j ≤ m + a, (X' τ).H j = (X τ).H j)
    (hHd : ∀ s, M.Live m X a b L s τ → (X' τ).H (m + s) = (X τ).H (m + s)) :
    ∀ t, τ ≤ t → t < b →
      M.addr (X' t) = M.addr (X t) ∧ M.branch (X' t) = M.branch (X t) ∧
        (X' (t + 1)).q = (X (t + 1)).q := by
  -- the invariant (a)–(d) at time `τ + n`
  have inv : ∀ n, τ + n ≤ b →
      (X' (τ + n)).q = (X (τ + n)).q ∧
      (∀ ℓ ∈ L (τ + n), ℓ ⬝ᵥ (X' (τ + n)).x = ℓ ⬝ᵥ (X (τ + n)).x) ∧
      (∀ j ≤ m + a, (X' (τ + n)).H j = (X (τ + n)).H j) ∧
      (∀ s, M.Live m X a b L s (τ + n) → (X' (τ + n)).H (m + s) = (X (τ + n)).H (m + s)) := by
    intro n
    induction n with
    | zero => intro _; exact ⟨hqa, hxb, hHc, hHd⟩
    | succ n ih =>
      intro hn
      obtain ⟨iq, ix, iH, iL⟩ := ih (by omega)
      set t := τ + n with ht
      have hat : a ≤ t := by omega
      have htb : t < b := by omega
      have haddr : M.addr (X' t) = M.addr (X t) := ix _ (hL.c1p t hat htb)
      have hbr : M.branch (X' t) = M.branch (X t) := by
        unfold branch; rw [ix _ (hL.c1z t hat htb)]
      rw [show τ + (n + 1) = t + 1 by omega, hX t, hX' t (by omega)]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [step, iq, hbr]
      · intro ℓ hℓ
        have hread : ℓ ⬝ᵥ M.u = 0 ∨ readAt (X' t).H (m + (t + 1)) (M.addr (X' t)) =
            readAt (X t).H (m + (t + 1)) (M.addr (X t)) := by
          by_cases hu : ℓ ⬝ᵥ M.u = 0
          · exact Or.inl hu
          right
          have hv := hnorm t hat htb
          have hv2 : ⌊M.addr (X t)⌋₊ < m + (t + 1) := hv.2
          rw [haddr]
          unfold readAt
          rw [if_pos hv, if_pos hv]
          by_cases hext : ⌊M.addr (X t)⌋₊ ≤ m + a
          · exact iH _ hext
          · replace hext := Nat.lt_of_not_le hext
            have hs := iL (⌊M.addr (X t)⌋₊ - m) ⟨by omega, by omega,
              t, le_rfl, ⟨hat, htb, hext, ℓ, hℓ, hu⟩, by unfold readAddr; omega⟩
            rwa [show m + (⌊M.addr (X t)⌋₊ - m) = ⌊M.addr (X t)⌋₊ by omega] at hs
        simp only [step, iq, hbr, dotProduct_add, dotProduct_smul, smul_eq_mul,
          Matrix.dotProduct_mulVec]
        rw [ix _ (hL.c2 t hat htb ℓ hℓ)]
        rcases hread with hu | hr
        · rw [hu, mul_zero, mul_zero]
        · rw [hr]
      · intro j hj
        simp only [step]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact iH j hj
      · intro s hs
        simp only [step]
        obtain ⟨has, hst, t', ht', hdem, hrd⟩ := hs
        by_cases hst1 : s = t + 1
        · subst hst1
          rw [show m + (t + 1) = m + (t + 1) from rfl, Function.update_self,
            Function.update_self]
          obtain ⟨hat', ht'b, hint, hex⟩ := hdem
          have := hL.c3 t' hat' ht'b hint hex
          rw [hrd, show m + (t + 1) - m - 1 = t by omega] at this
          exact ix _ this
        · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact iL s ⟨has, by omega, t', by omega, hdem, hrd⟩
  intro t hτt htb
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hτt
  obtain ⟨iq, ix, -, -⟩ := inv n (by omega)
  have hat : a ≤ τ + n := by omega
  have haddr : M.addr (X' (τ + n)) = M.addr (X (τ + n)) := ix _ (hL.c1p _ hat htb)
  have hbr : M.branch (X' (τ + n)) = M.branch (X (τ + n)) := by
    unfold branch; rw [ix _ (hL.c1z _ hat htb)]
  refine ⟨haddr, hbr, ?_⟩
  rw [hX, hX' _ (by omega)]
  simp only [step, iq, hbr]

end AffineMachine

/-! ## Balanced ladders -/

/-- The Strahler rank of the ladder vertex `v_{k,j}`: sources have rank `0`, and `v_{k+1,j}` has
the predecessors `v_{k,j}` and `v_{k,j+1}`. -/
def ladderRank (w : ℕ) : ℕ → ZMod w → ℕ
  | 0, _ => 0
  | k + 1, j => strahler (ladderRank w k j) (ladderRank w k (j + 1))

/-- Theorem (balanced ladders) (iii): every vertex of layer `k` has rank exactly `k`. -/
theorem ladder_rank (w k : ℕ) (j : ZMod w) : ladderRank w k j = k := by
  induction k generalizing j with
  | zero => rfl
  | succ k ih => simp [ladderRank, ih, strahler]

/-- Theorem (balanced ladders) (ii): for `w ≥ 2` the two predecessors are distinct. -/
theorem ladder_pred_ne (w : ℕ) (hw : 2 ≤ w) (j : ZMod w) : j ≠ j + 1 := by
  intro h
  have h1 : (1 : ZMod w) = 0 := by
    have := congrArg (· - j) h
    simpa using this.symm
  have : Fact (1 < w) := ⟨by omega⟩
  exact one_ne_zero h1

/-- The edges of the ladder `D_{r,w}`: from `v_{k,j+e}` to `v_{k+1,j}` for `k < r`, `e ∈ {0,1}`. -/
def ladderEdges (r w : ℕ) [NeZero w] : Finset ((ℕ × ZMod w) × (ℕ × ZMod w)) :=
  ((Finset.range r) ×ˢ (Finset.univ : Finset (ZMod w)) ×ˢ (Finset.univ : Finset Bool)).image
    (fun p => ((p.1, p.2.1 + if p.2.2 then 1 else 0), (p.1 + 1, p.2.1)))

/-- Theorem (balanced ladders) (i): the ladder has exactly `2 r w` edges. -/
theorem card_ladderEdges (r w : ℕ) [NeZero w] (hw : 2 ≤ w) :
    (ladderEdges r w).card = 2 * r * w := by
  unfold ladderEdges
  rw [Finset.card_image_of_injective]
  · simp only [Finset.card_product, Finset.card_range, Finset.card_univ, ZMod.card,
      Fintype.card_bool]
    ring
  · rintro ⟨k, j, e⟩ ⟨k', j', e'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨⟨hk, hj⟩, -, hj'⟩ := h
    subst hk hj'
    simp only [add_right_inj] at hj
    have h10 : (1 : ZMod w) ≠ 0 := by
      have : Fact (1 < w) := ⟨by omega⟩
      exact one_ne_zero
    cases e <;> cases e' <;> simp_all [eq_comm]

end GC.Portals
