import Mathlib.Data.Nat.Find
import Mathlib.Order.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Logic.Function.Iterate
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Perm.Closure
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Comparator challenge: four barriers to speeding up circuit evaluation (010e)

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

/-- The table `F^Z_t : 𝒬 → 𝒬`, `F^Z_t(c) = Φ_t(c, h_Z(t, p(c)))` (Definition 3.1). -/
def table (Z : ℕ → Q) (t : ℕ) (c : Q) : Q := M.Φ t c (M.read Z t (M.p c))

/-- The global table operator `ℋ` (Definition 3.1): `ℋ(Z)_0 = C_0`,
`ℋ(Z)_t = F^Z_t(ℋ(Z)_{t-1})`. -/
def globalOp (Z : ℕ → Q) : ℕ → Q
  | 0 => M.C0
  | t + 1 => M.table Z (t + 1) (globalOp Z t)

/-- Prefix compositions `P_t = F^Z_t ∘ ⋯ ∘ F^Z_1`. -/
def prefixComp (Z : ℕ → Q) : ℕ → Q → Q
  | 0 => id
  | t + 1 => M.table Z (t + 1) ∘ prefixComp Z t

/-- Segment compositions `F^Z_{t+k} ∘ ⋯ ∘ F^Z_{t+1}`. -/
def segComp (Z : ℕ → Q) (t : ℕ) : ℕ → Q → Q
  | 0 => id
  | k + 1 => M.table Z (t + k + 1) ∘ segComp Z t k

/-- The read-adaptivity rank `a(t)` (Definition 4.1): `a(0) = 0`; `a(t) = a(t-1)` if the real
read at stage `t` is not internal, and `max(a(t-1), 1 + a(s(t)-1))` if it is internal with
writer `s(t)`. Here `s(t) - 1 = p(C*_{t-1}) - m`. -/
def rank : ℕ → ℕ
  | 0 => 0
  | t + 1 =>
    if _h : (M.m : ℤ) ≤ M.p (M.real t) ∧ M.p (M.real t) < M.m + t then
      max (rank t) (1 + rank (M.p (M.real t) - M.m).toNat)
    else rank t
termination_by t => t
decreasing_by all_goals omega

end AppendMachine

/-- The copy program `v_t = v_{t-d}` as a normalized append-only machine (Section 5.1):
`m = d`, configurations `(t, v)`, `C_0 = (0, v_0)` with `v_0 = H_in[d-1]`, `w(t, v) = v`,
read address `t - 1` at stages `t ≤ d` and `t` at stages `t > d`, and `Φ_t((t-1, v), h) = (t, h)`. -/
def copyMachine {W : Type*} (d : ℕ) (Hin : ℕ → W) : AppendMachine (ℕ × W) W where
  m := d
  Hin := Hin
  C0 := (0, Hin (d - 1))
  p := fun c => if c.1 + 1 ≤ d then (c.1 : ℤ) else (c.1 : ℤ) + 1
  w := fun c => c.2
  Φ := fun t _ h => (t, h.getD (Hin (d - 1)))

section Copy

variable {W : Type*} {d : ℕ} (hd : 2 ≤ d) (Hin : ℕ → W)

include hd

end Copy

/-- The all-zero candidate `Z^{(0)}_t = (t, 0)` for `t ≥ 1`, `Z^{(0)}_0 = C_0 = (0, 1)`. -/
def copyZ0 : ℕ → ℕ × Bool := fun t => if t = 0 then (0, true) else (t, false)

section CopyBool

variable {d : ℕ} (hd : 2 ≤ d)

include hd

end CopyBool

end GC.Tabulation

namespace GC.Tabulation

open Module Matrix

/-- **Proposition 5.1 (independent-interface injectivity).** If a summary `E : {0,1}^q → Σ` has
a decoder `D` with `D(E(u)) = u` for all `u`, then `|Σ| ≥ 2^q`. -/
theorem summary_card_ge {q : ℕ} {S : Type*} [Fintype S] (E : (Fin q → Bool) → S)
    (D : S → (Fin q → Bool)) (hDE : ∀ u, D (E u) = u) : 2 ^ q ≤ Fintype.card S := by
  sorry

/-- The cycle `c(x) = x + 1 mod m` on `Fin (n + 2)`. -/
def cyc (n : ℕ) : Equiv.Perm (Fin (n + 2)) := finRotate (n + 2)

/-- The transposition `τ` of `0` and `1`. -/
def tau (n : ℕ) : Equiv.Perm (Fin (n + 2)) := Equiv.swap 0 1

/-- **Lemma 4.2 (generation).** `c` and `τ` generate the symmetric group. -/
theorem cyc_tau_generate (n : ℕ) :
    Subgroup.closure ({cyc n, tau n} : Set (Equiv.Perm (Fin (n + 2)))) = ⊤ := by
  sorry

section Observable

variable {K : Type*} [Field K] {n : ℕ}

/-- Indicator vectors `e_a`. -/
def ind (a : Fin (n + 2)) : Fin (n + 2) → K := fun x => if x = a then 1 else 0

variable (K n) in

/-- The sum functional `f ↦ ∑_x f(x)`. -/
def sumFun : (Fin (n + 2) → K) →ₗ[K] K where
  toFun f := ∑ i, f i
  map_add' f g := by simp [Finset.sum_add_distrib]
  map_smul' c f := by simp [Finset.mul_sum]

/-- **Theorem 4.4 (observable features).** Let `V ⊆ K^X` be invariant under `f ↦ f ∘ c` and
`f ↦ f ∘ τ`. If `V` contains a nonconstant function, then `dim V ≥ m - 1`. -/
theorem observable_dim (V : Submodule K (Fin (n + 2) → K))
    (hc : ∀ f ∈ V, (fun x => f (cyc n x)) ∈ V) (hτ : ∀ f ∈ V, (fun x => f (tau n x)) ∈ V)
    (hnc : ∃ f ∈ V, ∃ i j, f i ≠ f j) : n + 1 ≤ finrank K V := by
  sorry

/-- **Theorem 4.3 (injective features), linear case.** If `Φ : X → K^r` is injective and there
are matrices `M_c, M_τ` with `Φ(c x) = M_c Φ(x)` and `Φ(τ x) = M_τ Φ(x)`, then `r ≥ m - 1`. -/
theorem features_dim_linear {r : ℕ} (Φ : Fin (n + 2) → Fin r → K) (hΦ : Function.Injective Φ)
    (Mc Mτ : Matrix (Fin r) (Fin r) K) (hc : ∀ x, Φ (cyc n x) = Mc *ᵥ Φ x)
    (hτ : ∀ x, Φ (tau n x) = Mτ *ᵥ Φ x) : n + 1 ≤ r := by
  sorry

/-- **Theorem 4.3 (injective features), affine case.** With affine updates
`Φ(c x) = M_c Φ(x) + u_c` and `Φ(τ x) = M_τ Φ(x) + u_τ`, `r ≥ m - 2`. -/
theorem features_dim_affine {r : ℕ} (Φ : Fin (n + 2) → Fin r → K) (hΦ : Function.Injective Φ)
    (Mc Mτ : Matrix (Fin r) (Fin r) K) (uc uτ : Fin r → K)
    (hc : ∀ x, Φ (cyc n x) = Mc *ᵥ Φ x + uc) (hτ : ∀ x, Φ (tau n x) = Mτ *ᵥ Φ x + uτ) :
    n ≤ r := by
  sorry

end Observable

end GC.Tabulation

namespace GC.Tabulation

namespace AppendMachine

variable {Q W : Type*} (M : AppendMachine Q W)

/-- The candidate `C^g` of synchronous correction with radius `L` on a block with exact boundary
`a`, for the guess vector `g` (Definition 2.1). `C^g_t = C*_t` for `t ≤ a`; for `t > a`,
`C^g_t = Φ_t(C^g_{t-1}, ĥ_t)` where `ĥ_t` is the real read result for an initial or invalid address
or a cell written at a stage `s ≤ a + 1`, is `w(C^g_{s-1})` for a cell written at `s ∈ (a+1, t)` with
gap `t - s + 1 ≤ L`, and is the guess `g_t` for such a cell with gap `> L`. -/
def cand (a L : ℕ) (g : ℕ → W) : ℕ → Q
  | 0 => M.real 0
  | t + 1 =>
    if t + 1 ≤ a then M.real (t + 1) else
    M.Φ (t + 1) (cand a L g t)
      (if 0 ≤ M.p (cand a L g t) ∧ M.p (cand a L g t) < M.m then
        some (M.Hin (M.p (cand a L g t)).toNat)
       else if _h : (M.m : ℤ) ≤ M.p (cand a L g t) ∧ M.p (cand a L g t) < M.m + t then
         if (M.p (cand a L g t) - M.m).toNat + 1 ≤ a + 1 then
           some (M.w (M.real (M.p (cand a L g t) - M.m).toNat))
         else if t + 1 - ((M.p (cand a L g t) - M.m).toNat + 1) + 1 ≤ L then
           some (M.w (cand a L g (M.p (cand a L g t) - M.m).toNat))
         else some (g (t + 1))
       else none)
termination_by t => t
decreasing_by all_goals omega

/-- Stage `t` of the block makes a *long* read under the candidate: an internal read of a cell
written at a stage `s ∈ (a + 1, t)` with gap `t - s + 1 > L`. -/
def IsLong (a L : ℕ) (g : ℕ → W) (t : ℕ) : Prop :=
  a < t ∧ (M.m : ℤ) ≤ M.p (M.cand a L g (t - 1)) ∧ M.p (M.cand a L g (t - 1)) < M.m + t - 1 ∧
    a + 1 < (M.p (M.cand a L g (t - 1)) - M.m).toNat + 1 ∧
    L < t - ((M.p (M.cand a L g (t - 1)) - M.m).toNat + 1) + 1

open Classical in
/-- The correction of `g`: at every stage with a long read, the guess is replaced by the word
`w(C^g_{s-1})` written by the candidate. -/
noncomputable def correct (a L : ℕ) (g : ℕ → W) : ℕ → W := fun t =>
  if M.IsLong a L g t then M.w (M.cand a L g (M.p (M.cand a L g (t - 1)) - M.m).toNat) else g t

/-- The guess vectors `g^{(r)}`, starting from the constant default word `ω`. -/
noncomputable def guesses (a L : ℕ) (ω : W) (r : ℕ) : ℕ → W :=
  (M.correct a L)^[r] (fun _ => ω)

end AppendMachine

section CopyCorrection

variable {L : ℕ} (hL : 1 ≤ L)

include hL

local notation "Mc" => copyMachine (L + 1) (fun _ : ℕ => true)

/-- **Theorem 2.2(a).** For the copy program with lag `d = L + 1 ≥ 2`, all initial words `1` and
default guess `0`: in a block with boundary `a`, the value coordinate of `C^{g^{(r)}}_{a+t}`
(`t ≥ 1`) is `1` exactly when `t ≤ (r + 1) d`. -/
theorem copy_correction_value (a r : ℕ) (t : ℕ) (ht : 1 ≤ t) :
    ((Mc).cand a L ((Mc).guesses a L false r) (a + t)).2 = decide (t ≤ (r + 1) * (L + 1)) := by
  sorry

/-- **Theorem 2.2(a), correction rank.** The block `J = (a, a + m]` is exact after `r` correction
rounds iff `m ≤ (r + 1) d`; hence `χ_L(J) = ⌈m/d⌉ - 1`. -/
theorem copy_block_exact_iff (a mlen r : ℕ) :
    (∀ t, a < t → t ≤ a + mlen → (Mc).cand a L ((Mc).guesses a L false r) t = (Mc).real t) ↔
      mlen ≤ (r + 1) * (L + 1) := by
  sorry

end CopyCorrection

/-- **Theorem 2.2(b), lower bound.** For every partition of `(0, N]` into blocks
`0 = c_0 < c_1 < ⋯ < c_k = N`, the total number of correction rounds
`∑_j (χ_L(J_j) + 1) = ∑_j ⌈(c_{j+1} - c_j)/d⌉` (Theorem 2.2(a)) is at least `⌈N/d⌉`. The
partition into blocks of length `d` attains it, each block having `χ_L = 0`
(`copy_block_exact_iff` with `r = 0`). -/
theorem copy_multiscale_lower (d N : ℕ) (hd : 0 < d) (c : ℕ → ℕ) (k : ℕ) (hc0 : c 0 = 0)
    (hck : c k = N) (hmono : ∀ j < k, c j ≤ c (j + 1)) :
    (N + d - 1) / d ≤ ∑ j ∈ Finset.range k, ((c (j + 1) - c j) + d - 1) / d := by
  sorry

end GC.Tabulation

namespace GC.Tabulation

/-- A gate of an affine–product circuit over `𝔽₂`: a constant `x_i = c`, an affine gate
`x_i = c + ∑_{j ∈ S} x_j` (the list `S` records the coefficients `a_{ij}` with multiplicity), or a
product gate `x_i = x_p x_q`. Parents have smaller indices (only parents `< i` are used). -/
inductive APGate
  | const (c : ZMod 2)
  | affine (c : ZMod 2) (S : List ℕ)
  | prod (p q : ℕ)

/-- An affine–product circuit: gate `i` for every `i : ℕ` (a finite circuit is a prefix). -/
abbrev APCircuit := ℕ → APGate

/-- The right-hand side `f_i(x)` of a gate. -/
def gateRHS (g : APGate) (x : ℕ → ZMod 2) : ZMod 2 :=
  match g with
  | .const c => c
  | .affine c S => c + (S.map x).sum
  | .prod p q => x p * x q

/-- The exact values of the circuit. -/
def evalC (C : APCircuit) : ℕ → ZMod 2
  | i =>
    match C i with
    | .const c => c
    | .affine c S => c + (S.map (fun j => if _h : j < i then evalC C j else 0)).sum
    | .prod p q => (if _h : p < i then evalC C p else 0) * (if _h : q < i then evalC C q else 0)
termination_by i => i

/-- The Newton correction `δ`, the solution of `J(x) δ = F(x)` by forward substitution, where
`F_i(x) = x_i + f_i(x)` and `J(x)` is the formal Jacobian of `F` (unit lower triangular):
`δ_i = F_i(x) - ∑_{j < i} ∂f_i/∂x_j · δ_j`. -/
def newtonDelta (C : APCircuit) (x : ℕ → ZMod 2) : ℕ → ZMod 2
  | i =>
    match C i with
    | .const c => x i + c
    | .affine c S =>
      (x i + (c + (S.map x).sum)) -
        (S.map (fun j => if _h : j < i then newtonDelta C x j else 0)).sum
    | .prod p q =>
      (x i + x p * x q) -
        ((if _h : p < i then x q * newtonDelta C x p else 0) +
          (if _h : q < i then x p * newtonDelta C x q else 0))
termination_by i => i

/-- The Newton step `N(x) = x + δ`. -/
def newtonStep (C : APCircuit) (x : ℕ → ZMod 2) : ℕ → ZMod 2 := fun i => x i + newtonDelta C x i

/-- The multiplicative Strahler rank: `0` for constants, the maximum over parents for affine
gates, and `max(r₁, r₂ + 1)` (`r₁ ≥ r₂` the parent ranks) for products. -/
def srank (C : APCircuit) : ℕ → ℕ
  | i =>
    match C i with
    | .const _ => 0
    | .affine _ S => (S.map (fun j => if _h : j < i then srank C j else 0)).foldr max 0
    | .prod p q =>
      if (if _h : p < i then srank C p else 0) = (if _h : q < i then srank C q else 0) then
        (if _h : p < i then srank C p else 0) + 1
      else max (if _h : p < i then srank C p else 0) (if _h : q < i then srank C q else 0)
termination_by i => i

/-- **Lemma 3.1 (a balanced identity), value part.** Over `𝔽₂`, `z · z = z`. -/
theorem zmod2_mul_self (z : ZMod 2) : z * z = z := by
  sorry

/-- The ladder: `z_0 = 1` (gate `0`) and, for `ℓ ≥ 0`, the copies `s_{ℓ+1} = z_ℓ` (gate `3ℓ+1`),
`d_{ℓ+1} = z_ℓ` (gate `3ℓ+2`) and the product `z_{ℓ+1} = s_{ℓ+1} d_{ℓ+1}` (gate `3ℓ+3`). The
ladder of length `k` is the prefix of gates `0, …, 3k`. -/
def ladder : APCircuit := fun i =>
  if i = 0 then .const 1
  else if i % 3 = 1 then .affine 0 [i - 1]
  else if i % 3 = 2 then .affine 0 [i - 2]
  else .prod (i - 2) (i - 1)

/-- The exact values of the ladder are all `1`. -/
theorem ladder_eval (l : ℕ) :
    evalC ladder (3 * l) = 1 ∧ evalC ladder (3 * l + 1) = 1 ∧ evalC ladder (3 * l + 2) = 1 := by
  sorry

/-- The ranks along the ladder: `ρ(z_ℓ) = ℓ` and `ρ(s_{ℓ+1}) = ρ(d_{ℓ+1}) = ℓ`. -/
theorem ladder_rank (l : ℕ) :
    srank ladder (3 * l) = l ∧ srank ladder (3 * l + 1) = l ∧ srank ladder (3 * l + 2) = l := by
  sorry

section Newton

variable (x : ℕ → ZMod 2)

end Newton

/-- The standard start: `z_0 = 1` and all other gates `0`. -/
def ladderStart : ℕ → ZMod 2 := fun i => if i = 0 then 1 else 0

/-- **Theorem 3.2 (exact Newton delay).** Newton iteration on the ladder from the standard start:
after `t` steps, `z_0 = 1`, `s_{ℓ+1} = d_{ℓ+1} = 1` iff `ℓ + 1 ≤ t`, and `z_{ℓ+1} = 1` iff
`ℓ + 1 < t`. -/
theorem ladder_newton (t : ℕ) :
    (newtonStep ladder)^[t] ladderStart 0 = 1 ∧
    ∀ l, (newtonStep ladder)^[t] ladderStart (3 * l + 1) = (if l + 1 ≤ t then 1 else 0) ∧
      (newtonStep ladder)^[t] ladderStart (3 * l + 2) = (if l + 1 ≤ t then 1 else 0) ∧
      (newtonStep ladder)^[t] ladderStart (3 * l + 3) = (if l + 1 < t then 1 else 0) := by
  sorry

/-- **Theorem 3.2, consequence.** On the ladder, the gate `z_k` (`k ≥ 1`, exact value `1`, rank
`ρ(z_k) = k`) is exact after `t` Newton steps iff `t ≥ k + 1 = ρ(z_k) + 1`. -/
theorem ladder_first_exact (k t : ℕ) (hk : 1 ≤ k) :
    (newtonStep ladder)^[t] ladderStart (3 * k) = evalC ladder (3 * k) ↔
      srank ladder (3 * k) + 1 ≤ t := by
  sorry

end GC.Tabulation
