import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Comparator challenge for manuscript 001a (A P-Complete Problem in Average-Case NC). Definitions are copied verbatim from
the solution files; theorems are stated with `sorry`. -/

namespace GC.RandomSeqNOR

/-- A Sequential NOR instance (infinite pointer sequence): gate `i ≥ 1` reads `i - 1` and `j i`,
with `j i < i`. The value `j 0` is irrelevant. -/
structure Inst where
  /-- The pointer of gate `i`. -/
  j : ℕ → ℕ
  /-- Pointers go strictly backwards. -/
  j_lt : ∀ i, 0 < i → j i < i

/-- The trace `x*` of an instance: `x*₀ = 1`, `x*ᵢ = (1 + x*ᵢ₋₁)(1 + x*_{jᵢ})`. -/
def trace (P : Inst) : ℕ → ZMod 2
  | 0 => 1
  | i + 1 => (1 + trace P i) * (1 + trace P (P.j (i + 1)))
termination_by i => i
decreasing_by
  · omega
  · exact P.j_lt (i + 1) (Nat.succ_pos i)

/-- Gate `i ≥ 1` is a NOT gate when `jᵢ = i - 1`. -/
def IsNot (P : Inst) (i : ℕ) : Prop := P.j i + 1 = i

/-- One Newton round over `GF(2)`: the forward-substitution solution `x⁺` of the linearised
system at `x`. -/
def newton (P : Inst) (x : ℕ → ZMod 2) : ℕ → ZMod 2
  | 0 => 1
  | i + 1 =>
    if P.j (i + 1) = i then
      (1 + x i) + (newton P x i + x i)
    else
      (1 + x i) * (1 + x (P.j (i + 1)))
        + (1 + x (P.j (i + 1))) * (newton P x i + x i)
        + (1 + x i) * (newton P x (P.j (i + 1)) + x (P.j (i + 1)))
termination_by i => i
decreasing_by
  all_goals first
    | omega
    | exact P.j_lt (i + 1) (Nat.succ_pos i)

/-- The `t`-th Newton iterate from the start `x0`. -/
def newtonIter (P : Inst) (x0 : ℕ → ZMod 2) (t : ℕ) : ℕ → ZMod 2 := (newton P)^[t] x0

/-- The error vector `e = x ⊕ x*`. -/
def err (P : Inst) (x : ℕ → ZMod 2) (i : ℕ) : ZMod 2 := x i + trace P i

/-- The standard start `x⁽⁰⁾ = (1, 0, 0, …)`. -/
def stdStart (i : ℕ) : ZMod 2 := if i = 0 then 1 else 0

/-- A source of round `t` (for the iterate `x`): a binary gate both of whose inputs are wrong. -/
def IsSource (P : Inst) (x : ℕ → ZMod 2) (i : ℕ) : Prop :=
  0 < i ∧ ¬ IsNot P i ∧ err P x (i - 1) = 1 ∧ err P x (P.j i) = 1

/-- The number of rounds `T_n` until the iterate is exact on `[0, n]`. -/
noncomputable def exactRounds (P : Inst) (x0 : ℕ → ZMod 2) (n : ℕ) : ℕ :=
  sInf {t | ∀ i ≤ n, newtonIter P x0 t i = trace P i}

/-- The Horton–Strahler rank: `ρ(0) = 0`, `ρ(i) = ρ(i-1)` at a NOT gate, and at a binary gate
with parent ranks `r₁ ≥ r₂`, `ρ(i) = r₁` if `r₁ > r₂` and `r₁ + 1` if `r₁ = r₂`. -/
def strahler (P : Inst) : ℕ → ℕ
  | 0 => 0
  | i + 1 =>
    if P.j (i + 1) = i then strahler P i
    else if strahler P i = strahler P (P.j (i + 1)) then strahler P i + 1
    else max (strahler P i) (strahler P (P.j (i + 1)))
termination_by i => i
decreasing_by
  all_goals first
    | omega
    | exact P.j_lt (i + 1) (Nat.succ_pos i)

/-- The pointers of the worst-case family `W`: `(j₁, …, j₅) = (0, 1, 0, 1, 2)`, `jᵢ = 1` for even
`i ≥ 6`, and `jᵢ = i - 2` for odd `i ≥ 7`. (`W_n` is its restriction to `1, …, n`.) -/
def worstPtr (i : ℕ) : ℕ :=
  if i ≤ 1 then 0 else if i = 3 then 0 else if i = 5 then 2
  else if i % 2 = 0 then 1 else i - 2

theorem worstPtr_lt : ∀ i, 0 < i → worstPtr i < i := by
  sorry

/-- The worst-case instance `W_∞`. -/
def worstInst : Inst := ⟨worstPtr, worstPtr_lt⟩

/-- The graph `G` on `ℕ` with edges `{i-1, i}` and `{jᵢ, i}` (a Hamiltonian path plus the
recursive tree of the pointers). -/
def norGraph (P : Inst) : SimpleGraph ℕ :=
  SimpleGraph.fromRel fun a b => a + 1 = b ∨ (0 < b ∧ a = P.j b)

/-- Lemma 4.2, position `0`: every Newton iterate is exact at position `0`. -/
theorem err_newton_zero (P : Inst) (x : ℕ → ZMod 2) : err P (newton P x) 0 = 0 := by
  sorry

/-- Lemma 4.2, NOT gates: `e⁺ᵢ = e⁺ᵢ₋₁`. -/
theorem err_newton_of_isNot (P : Inst) (x : ℕ → ZMod 2) (i : ℕ) (h : IsNot P (i + 1)) :
    err P (newton P x) (i + 1) = err P (newton P x) i := by
  sorry

/-- Lemma 4.2, binary gates:
`e⁺ᵢ = (1 + x_{jᵢ}) e⁺ᵢ₋₁ + (1 + xᵢ₋₁) e⁺_{jᵢ} + eᵢ₋₁ e_{jᵢ}`. -/
theorem err_newton_of_not_isNot (P : Inst) (x : ℕ → ZMod 2) (i : ℕ) (h : ¬ IsNot P (i + 1)) :
    err P (newton P x) (i + 1) =
      (1 + x (P.j (i + 1))) * err P (newton P x) i
        + (1 + x i) * err P (newton P x) (P.j (i + 1))
        + err P x i * err P x (P.j (i + 1)) := by
  sorry

/-- The truth `x*` is a fixed point of the Newton map. -/
theorem newton_trace (P : Inst) : newton P (trace P) = trace P := by
  sorry

/-- Lemma 4.3, first half: the error of the next round vanishes up to `i` when no gate `≤ i`
is a source. -/
theorem err_newton_eq_zero_of_no_source (P : Inst) (x : ℕ → ZMod 2) :
    ∀ i, (∀ k ≤ i, ¬ IsSource P x k) → err P (newton P x) i = 0 := by
  sorry

/-- Lemma 4.3, second half: at the first source `s`, the next error is `1`.
Together with `err_newton_eq_zero_of_no_source` this is `f_{t+1} = min S_t`. -/
theorem err_newton_eq_one_of_first_source (P : Inst) (x : ℕ → ZMod 2) (s : ℕ)
    (hs : IsSource P x s) (hmin : ∀ k < s, ¬ IsSource P x k) :
    err P (newton P x) s = 1 := by
  sorry

/-- Lemma 4.3, front growth `f_{t+1} ≥ f_t + 2`: if the error vanishes below `f`, the next error
vanishes below `f + 2`. -/
theorem front_growth (P : Inst) (x : ℕ → ZMod 2) (f : ℕ) (hf : ∀ k < f, err P x k = 0) :
    ∀ k < f + 2, err P (newton P x) k = 0 := by
  sorry

/-- Iterating `front_growth`: `f_t ≥ f_0 + 2t`. -/
theorem front_growth_iter (P : Inst) (x0 : ℕ → ZMod 2) (f : ℕ) (hf : ∀ k < f, err P x0 k = 0) :
    ∀ t, ∀ k < f + 2 * t, err P (newtonIter P x0 t) k = 0 := by
  sorry

theorem newtonIter_congr {P Q : Inst} {n : ℕ} (hj : ∀ i, 0 < i → i ≤ n → P.j i = Q.j i)
    {x y : ℕ → ZMod 2} (hxy : ∀ i ≤ n, x i = y i) (t : ℕ) :
    ∀ i ≤ n, newtonIter P x t i = newtonIter Q y t i := by
  sorry

/-- **Lemma 5.2 (i) (pathwise witnesses).** Every source `s` of round `r - 1` satisfies `s ∈ E_r`,
or `s - 1 ∈ E_r`, or `j_s ∈ E_r`. -/
theorem source_witness (P : Inst) (x : ℕ → ZMod 2) {s : ℕ} (hs : IsSource P x s) :
    err P (newton P x) s = 1 ∨ err P (newton P x) (s - 1) = 1 ∨
      err P (newton P x) (P.j s) = 1 := by
  sorry

/-- **Proposition 3.1 (Newton–Strahler bound).** For any start, after `t` Newton rounds every gate
`i` with `ρ(i) < t` is exact. -/
theorem newton_strahler (P : Inst) (x0 : ℕ → ZMod 2) :
    ∀ t i, strahler P i < t → newtonIter P x0 t i = trace P i := by
  sorry

/-- **Proposition 3.1, consequence:** `T_n ≤ ρ(n) + 1`, for every start. -/
theorem exactRounds_le_strahler (P : Inst) (x0 : ℕ → ZMod 2) (n : ℕ) :
    exactRounds P x0 n ≤ strahler P n + 1 := by
  sorry

/-- **Proposition 8.1 (a).** From the standard start, `T_n ≤ ⌊(n-1)/2⌋` for every `n ≥ 3`. -/
theorem worst_case_upper (P : Inst) (n : ℕ) (hn : 3 ≤ n) :
    exactRounds P stdStart n ≤ (n - 1) / 2 := by
  sorry

/-- **Proposition 8.1 (b), front of `W`.** From the standard start, the front of `W` is exactly
`f_t = 2t + 3` for every `t ≥ 1`. -/
theorem worstInst_front (t : ℕ) (ht : 1 ≤ t) :
    (∀ k < 2 * t + 3, err worstInst (newtonIter worstInst stdStart t) k = 0) ∧
      err worstInst (newtonIter worstInst stdStart t) (2 * t + 3) = 1 := by
  sorry

/-- **Proposition 8.1 (b).** `T_n(W_n) = ⌊(n-1)/2⌋` from the standard start, for `n ≥ 3`
(the paper states it for `n ≥ 5` and uses an instance with `j₂ = 1`, such as `W`, for
`n ∈ {3, 4}`). -/
theorem exactRounds_worstInst (n : ℕ) (hn : 3 ≤ n) :
    exactRounds worstInst stdStart n = (n - 1) / 2 := by
  sorry

/-- **Proposition 8.1 (c).** For every `n ≥ 3`, the maximum of `T_n` over all instances, from the
standard start, is exactly `⌊(n-1)/2⌋`. (Instances are infinite pointer sequences; by
`newtonIter_congr` and `trace_congr` only `j₁, …, jₙ` matter.) -/
theorem newton_worst_case (n : ℕ) (hn : 3 ≤ n) :
    (∀ P : Inst, exactRounds P stdStart n ≤ (n - 1) / 2) ∧
      ∃ P : Inst, exactRounds P stdStart n = (n - 1) / 2 := by
  sorry

/-- **Corollary 8.5.** A set `S ⊆ ℕ` is the lexicographically first maximal independent set of
`G` in the natural order, i.e. `i ∈ S` iff no earlier neighbour of `i` lies in `S`, if and only if
`S` is the set of ones of the trace. -/
theorem lexFirstMIS_eq_ones (P : Inst) (S : Set ℕ) :
    (∀ i, i ∈ S ↔ ∀ k < i, (norGraph P).Adj k i → k ∉ S) ↔ S = {i | trace P i = 1} := by
  sorry

/-- **Theorem 8.3, final step.** With `g(u) = (1-u)/(2-u)`, if `L = liminf σ_m` and
`U = limsup σ_m` lie in `[0, 1/2]` and satisfy `L ≥ g(U)` and `U ≤ g(L)`, then
`L = U = (3 - √5)/2 = φ⁻²`. -/
theorem golden_density_fixed_point {L U : ℝ} (hLU : L ≤ U) (hU : U ≤ 1 / 2)
    (h1 : (1 - U) / (2 - U) ≤ L) (h2 : U ≤ (1 - L) / (2 - L)) :
    L = U ∧ U = (3 - Real.sqrt 5) / 2 := by
  sorry

end GC.RandomSeqNOR
