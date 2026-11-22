import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Comparator challenge: Exact Cut Contraction for P-Complete Sequential Circuits (manuscript 011b)

Theorem 4.1 (exact cut externalization with reconstruction), the enumeration of internal
gates, Lemma 5.2 (crossing-area identity and its consequence), Proposition 5.3 (padding
counterexample to the source's quadratic-span claim), Proposition 3.1 (Sequential NOR is the
lexicographically-first greedy maximal independent set) and Lemma 3.3 (jump rule).
-/

namespace GC.Semisort

section
open Finset

/-- The values of a binary-table sequential circuit (Definition 2.2): `x_0` is given and
`x_{i+1} = G_{i+1}(x_i, x_{π_{i+1}})`. (Under `IsShape` the parent is always earlier; an
out-of-range parent, which `IsShape` excludes, would be read as `false`.) -/
def circuitValue (x0 : Bool) (π : ℕ → ℕ) (G : ℕ → Bool → Bool → Bool) : ℕ → Bool
  | 0 => x0
  | i + 1 => G (i + 1) (circuitValue x0 π G i)
      (if h : π (i + 1) ≤ i then circuitValue x0 π G (π (i + 1)) else false)
termination_by i => i
decreasing_by all_goals omega

/-- `π` is the shape of a circuit with `n` gates: `π_i < i` for `1 ≤ i ≤ n`. -/
def IsShape (n : ℕ) (π : ℕ → ℕ) : Prop := ∀ i, 1 ≤ i → i ≤ n → π i < i

end

section
open Finset

variable (π : ℕ → ℕ) (b : ℕ)

/-- `ρ(i)`: the number of internal gates `h` with `b < h ≤ i` (`π_h > b`). -/
def cutRank : ℕ → ℕ
  | 0 => 0
  | i + 1 => cutRank i + if b < i + 1 ∧ b < π (i + 1) then 1 else 0

/-- `h_r`: the `r`-th internal gate (`h_0 = b`), found as the internal gate `i ≤ n` with
`ρ(i) = r`. -/
def internalGate (n r : ℕ) : ℕ :=
  ((List.range (n + 1)).find? fun i => decide (b < i ∧ b < π i ∧ cutRank π b i = r)).getD b

/-- The maps `Φ_i` (unary Boolean maps): `Φ_i = ψ_i ∘ ⋯ ∘ ψ_{h_{ρ(i)}+1}`, where
`ψ_j(z) = G_j(z, x_{π_j})` for an external gate `j`. It uses only the prefix values `xp`, and
only at positions `π_j ≤ b`. -/
def suffixMap (G : ℕ → Bool → Bool → Bool) (xp : ℕ → Bool) : ℕ → Bool → Bool
  | 0 => id
  | i + 1 =>
    if b < i + 1 ∧ π (i + 1) ≤ b then fun z => G (i + 1) (suffixMap G xp i z) (xp (π (i + 1)))
    else id

/-- Parent array of the contracted circuit: `π'_r = ρ(π_{h_r})` (Theorem 4.1(c)). -/
def residualParent (n r : ℕ) : ℕ := cutRank π b (π (internalGate π b n r))

/-- Tables of the contracted circuit: `G'_r(u,v) = G_{h_r}(Φ_{h_r - 1}(u), Φ_{π_{h_r}}(v))`. -/
def residualGate (G : ℕ → Bool → Bool → Bool) (xp : ℕ → Bool) (n r : ℕ) (u v : Bool) : Bool :=
  G (internalGate π b n r) (suffixMap π b G xp (internalGate π b n r - 1) u)
    (suffixMap π b G xp (π (internalGate π b n r)) v)

/-- The values `y_0 = x_b, y_1, …, y_q` of the contracted circuit `C/b`. -/
def residualValue (G : ℕ → Bool → Bool → Bool) (xp : ℕ → Bool) (n : ℕ) : ℕ → Bool :=
  circuitValue (xp b) (residualParent π b n) (residualGate π b G xp n)

end

section
open Finset

variable {π : ℕ → ℕ} {b : ℕ}

/-- **The internal gates.** For `1 ≤ r ≤ q = ρ(n)`, `h_r` is an internal gate `≤ n` of rank
`r`. (Also `h_0 = b`, `internalGate_zero`, and `r ↦ h_r` is strictly increasing,
`internalGate_strictMono`.) -/
theorem internalGate_spec {n r : ℕ} (hr1 : 1 ≤ r) (hr : r ≤ cutRank π b n) :
    b < internalGate π b n r ∧ internalGate π b n r ≤ n ∧ b < π (internalGate π b n r) ∧
      cutRank π b (internalGate π b n r) = r := by
  sorry

/-- The internal gates are enumerated in increasing order. -/
theorem internalGate_strictMono {n r s : ℕ} (hr1 : 1 ≤ r) (hrs : r < s)
    (hs : s ≤ cutRank π b n) : internalGate π b n r < internalGate π b n s := by
  sorry

/-- The number `q(b)` of gates of `C/b` is `|{i ∈ (b, n] : π_i > b}|`. -/
theorem cutRank_eq_card (n : ℕ) :
    cutRank π b n = #((Ioc b n).filter fun i => b < π i) := by
  sorry

end

section
open Finset

variable {x0 : Bool} {π : ℕ → ℕ} {G : ℕ → Bool → Bool → Bool} {n b : ℕ} {xp : ℕ → Bool}

/-- **Theorem 4.1 (exact cut externalization).** Let `C` be a binary-table sequential circuit
with `n` gates (shape `π`, tables `G`, values `x`), let `b` be a cut (the paper takes
`b ∈ [0, n-1]`; the statement holds for every `b`) and let `xp` agree with
`x` on `[0, b]` (the given prefix values). Let `q = ρ(n)` be the number of internal gates. Then
the contracted circuit `C/b` (start value `x_b`, parents `π'`, tables `G'`, values `y`) has a
valid shape on `q` gates and
* (a) `y_r = x_{h_r}` for `r = 0, …, q`;
* (b) `x_i = Φ_i(y_{ρ(i)})` for every `i ∈ [b, n]` (reconstruction of the suffix values);
* (c) `π'_r = ρ(π_{h_r})` for `r = 1, …, q`.
The circuit `C/b` and the maps `Φ_i` are built from `π`, `G`, `b` and `xp` only. -/
theorem exact_cut_externalization (hπ : IsShape n π)
    (hxp : ∀ j ≤ b, xp j = circuitValue x0 π G j) :
    IsShape (cutRank π b n) (residualParent π b n) ∧
    (∀ r ≤ cutRank π b n,
      residualValue π b G xp n r = circuitValue x0 π G (internalGate π b n r)) ∧
    (∀ i, b ≤ i → i ≤ n →
      circuitValue x0 π G i = suffixMap π b G xp i (residualValue π b G xp n (cutRank π b i))) ∧
    (∀ r, 1 ≤ r → r ≤ cutRank π b n →
      residualParent π b n r = cutRank π b (π (internalGate π b n r))) := by
  sorry

end

section
open Finset

/-- `c(b) = |{i > b : π_i ≤ b}|`, the number of edges `(π_i, i)` crossing the cut `b`. -/
def crossCount (π : ℕ → ℕ) (n b : ℕ) : ℕ := #((Ioc b n).filter fun i => π i ≤ b)

/-- **Lemma 5.2 (crossing-area identity).** `∑_{b=0}^{n-1} c(b) = ∑_{i=1}^{n} (i - π_i)`.
(It holds for every parent array; for a shape, `i - π_i` is the true span of edge `i`.) -/
theorem crossing_area_identity (π : ℕ → ℕ) (n : ℕ) :
    ∑ b ∈ range n, crossCount π n b = ∑ i ∈ Icc 1 n, (i - π i) := by
  sorry

/-- Lemma 5.2, consequences: if `∑_i (i - π_i) ≥ λ n²` then some cut `b` has `c(b) ≥ λ n`, and
then `b + q(b) ≤ (1 - λ) n`. -/
theorem exists_heavy_cut {π : ℕ → ℕ} {n : ℕ} (hn : 1 ≤ n) (lam : ℝ)
    (h : lam * (n : ℝ) ^ 2 ≤ ((∑ i ∈ Icc 1 n, (i - π i) : ℕ) : ℝ)) :
    ∃ b < n, lam * n ≤ crossCount π n b ∧
      (b : ℝ) + cutRank π b n ≤ (1 - lam) * n := by
  sorry

/-- Parent array of the padded circuit: the gates of `C'` (`i ≤ m`), then gates with `π_i = 0`. -/
def padParent (π : ℕ → ℕ) (m i : ℕ) : ℕ := if i ≤ m then π i else 0

/-- Tables of the padded circuit: those of `C'`, then arbitrary tables `H`. -/
def padGate (G H : ℕ → Bool → Bool → Bool) (m i : ℕ) : Bool → Bool → Bool :=
  if i ≤ m then G i else H i

/-- The NOR table. -/
def norGate : ℕ → Bool → Bool → Bool := fun _ u v => !(u || v)

/-- **Proposition 5.3 (padding counterexample).** Let `C'` be any binary-table sequential
circuit with `m ≥ 1` gates, and let `C` have `n = 2m` gates: those of `C'`, followed by `m`
gates with parent `0` and arbitrary tables `H`. Then `C` has a valid shape and
* (a) `∑_{i=1}^{n} (i - π_i) ≥ n²/4`;
* (b) the cut `b = m` has `q(m) = 0`, so `(b/n)^γ + (q(b)/n)^γ = 2^{-γ} < 1` for every `γ > 0`;
* (c) the values of `C'` are the first `m + 1` values of `C`. -/
theorem padding_counterexample (x0 : Bool) {π : ℕ → ℕ} (G H : ℕ → Bool → Bool → Bool)
    {m : ℕ} (hπ : IsShape m π) (hm : 1 ≤ m) :
    IsShape (2 * m) (padParent π m) ∧
    (2 * m) ^ 2 ≤ 4 * ∑ i ∈ Icc 1 (2 * m), (i - padParent π m i) ∧
    cutRank (padParent π m) m (2 * m) = 0 ∧
    (∀ γ : ℝ, 0 < γ →
      ((m : ℝ) / ((2 * m : ℕ) : ℝ)) ^ γ +
          ((cutRank (padParent π m) m (2 * m) : ℝ) / ((2 * m : ℕ) : ℝ)) ^ γ = (2 : ℝ) ^ (-γ) ∧
        (2 : ℝ) ^ (-γ) < 1) ∧
    ∀ j ≤ m, circuitValue x0 (padParent π m) (padGate G H m) j = circuitValue x0 π G j := by
  sorry

/-- Proposition 5.3, last claim: if `C'` is a Sequential NOR circuit (`x_0 = 1`, all tables NOR),
so is `C` when the appended tables are NOR, and the appended gates all have value `0`. -/
theorem padding_counterexample_nor {π : ℕ → ℕ} {m : ℕ} :
    padGate norGate norGate m = norGate ∧
    ∀ j, m < j → circuitValue true (padParent π m) (padGate norGate norGate m) j = false := by
  sorry

end

section

/-- Adjacency in `H_π`: `u` and `v` are joined by an edge `{i-1, i}` or `{π_i, i}`,
`1 ≤ i ≤ n`. -/
def misAdj (π : ℕ → ℕ) (n u v : ℕ) : Prop :=
  (1 ≤ v ∧ v ≤ n ∧ (u + 1 = v ∨ u = π v)) ∨ (1 ≤ u ∧ u ≤ n ∧ (v + 1 = u ∨ v = π u))

/-- `S` is the lexicographically-first greedy maximal independent set of `H_π`: vertex
`i ≤ n` is selected iff none of its neighbours `j < i` is selected. -/
def IsLexFirstGreedyMIS (π : ℕ → ℕ) (n : ℕ) (S : ℕ → Prop) : Prop :=
  ∀ i ≤ n, (S i ↔ ∀ j < i, misAdj π n j i → ¬ S j)

/-- **Proposition 3.1.** For Sequential NOR (`x_0 = 1`, all tables NOR) with shape `π`, the set
`{i : x_i = 1}` is the lexicographically-first greedy maximal independent set of `H_π`, and it
is the only set satisfying the greedy recursion. -/
theorem seqNOR_eq_greedyMIS {π : ℕ → ℕ} {n : ℕ} (hπ : IsShape n π) :
    IsLexFirstGreedyMIS π n (fun i => circuitValue true π norGate i = true) ∧
      ∀ S : ℕ → Prop, IsLexFirstGreedyMIS π n S →
        ∀ i ≤ n, (S i ↔ circuitValue true π norGate i = true) := by
  sorry

/-- **Lemma 3.3 (jump rule).** Let `x_s = 1` in Sequential NOR, let `S` be the set of positions
`≤ s` with value `1`, and `T = {t : s + 2 ≤ t ≤ n, π_t ∉ S}`. If no element of `T` lies below
`t ≤ n` (`t > s`), then every position strictly between `s` and `t` has value `0`, and `x_t = 1`
iff `t ∈ T`. Taking `t = min T` gives `s_{r+1} = min T_r`; taking `t = n` with `T = ∅` shows that
`s` is the last position with value `1`. -/
theorem jump_rule {π : ℕ → ℕ} {n s t : ℕ} (hπ : IsShape n π)
    (hxs : circuitValue true π norGate s = true) (hst : s < t) (htn : t ≤ n)
    (hmin : ∀ u, s + 2 ≤ u → u < t →
      (π u ≤ s ∧ circuitValue true π norGate (π u) = true)) :
    (∀ u, s < u → u < t → circuitValue true π norGate u = false) ∧
      (circuitValue true π norGate t = true ↔
        (s + 2 ≤ t ∧ ¬ (π t ≤ s ∧ circuitValue true π norGate (π t) = true))) := by
  sorry

end

end GC.Semisort
