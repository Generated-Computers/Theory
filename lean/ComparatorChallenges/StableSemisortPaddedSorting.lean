import Mathlib.Data.List.ReduceOption
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Comparator challenge: Stable Semisort Is Exactly as Hard as Padded Sorting (manuscript 011a)

Theorem 3.1 (stable semisort from an unstable semisort and one padded sort), its converse
(padded sorting from stable semisort, Theorem 4.1(a),(b) with Lemma 2.4), Lemma 6.2
(prediction-alignment error equals collision energy) and Theorem 7.3 (density barrier).
-/

namespace GC.Semisort

section

variable {K : Type*}

/-- In `out`, records with equal keys form one contiguous interval. -/
def KeysContiguous (key : ℕ → K) (out : List ℕ) : Prop :=
  ∀ (p q r : ℕ) (hp : p < out.length) (hq : q < out.length) (hr : r < out.length),
    p < q → q < r → key out[p] = key out[r] → key out[q] = key out[p]

/-- In `out`, records with equal keys appear in increasing order of original index. -/
def KeysStable (key : ℕ → K) (out : List ℕ) : Prop :=
  ∀ (p q : ℕ) (hp : p < out.length) (hq : q < out.length),
    p < q → key out[p] = key out[q] → out[p] < out[q]

/-- Output specification of `USemi` (unstable semisort, Definition 2.1(a)): a rearrangement of
the records `0, …, n-1` in which records with equal keys are contiguous. -/
def IsSemisort (key : ℕ → K) (n : ℕ) (out : List ℕ) : Prop :=
  out.Perm (List.range n) ∧ KeysContiguous key out

/-- Output specification of `SS` (stable semisort, Definition 2.2(a)): a semisort in which
records with equal keys keep their input order. -/
def IsStableSemisort (key : ℕ → K) (n : ℕ) (out : List ℕ) : Prop :=
  IsSemisort key n out ∧ KeysStable key out

/-- Output specification of `IS` (stable integer sort, Definition 2.2(b)): the records sorted
by key, ties broken by position. (The key range `[0,n]` is a precondition on the instance.) -/
def IsStableIntSort (a : ℕ → ℕ) (n : ℕ) (out : List ℕ) : Prop :=
  out.Perm (List.range n) ∧ out.Pairwise (fun i j => a i < a j ∨ (a i = a j ∧ i < j))

/-- Output specification of `DS` (sorting distinct integer keys, Definition 2.2(c)). -/
def IsDistinctSort (z : ℕ → ℕ) (n : ℕ) (out : List ℕ) : Prop :=
  out.Perm (List.range n) ∧ out.Pairwise (fun i j => z i < z j)

/-- A valid instance of `PaddedSort(n,U)` and of `DS`: the keys of the records `0, …, n-1` are
distinct and lie in `[0,U)`. -/
def IsDistinctKeyInstance (z : ℕ → ℕ) (n U : ℕ) : Prop :=
  (∀ i < n, z i < U) ∧ ∀ i < n, ∀ j < n, z i = z j → i = j

/-- Output specification of `PaddedSort` (Definition 2.1(b)): an array of `c n` slots
(`c ≥ 1`), a slot being empty (`none`) or holding one record (`some i`), in which every record
occupies exactly one slot and the occupied slots appear in increasing key order. -/
def IsPaddedSort (z : ℕ → ℕ) (n : ℕ) (P : List (Option ℕ)) : Prop :=
  (∃ c : ℕ, 1 ≤ c ∧ P.length = c * n) ∧ P.reduceOption.Perm (List.range n) ∧
    P.reduceOption.Pairwise (fun i j => z i < z j)

/-- Compaction of a padded array (Lemma 2.4): keep the occupied slots, in order. -/
def compact (P : List (Option ℕ)) : List ℕ := P.reduceOption

end

section
open Finset

variable {K : Type*} [DecidableEq K]

/-- Run mark `s[j]` (stage S2): `1` at the first position of each run of equal keys in `T`. -/
def runStart (key : ℕ → K) (T : List ℕ) (j : ℕ) : ℕ :=
  if j = 0 ∨ key (T.getD j 0) ≠ key (T.getD (j - 1) 0) then 1 else 0

/-- Run number `g[j] = ∑_{j' ≤ j} s[j'] - 1` (stage S2). -/
def runIndex (key : ℕ → K) (T : List ℕ) (j : ℕ) : ℕ :=
  (∑ j' ∈ range (j + 1), runStart key T j') - 1

/-- Group identifier `gid[i]` (stage S3): the run number of the position of record `i` in `T`. -/
def groupId (key : ℕ → K) (T : List ℕ) (i : ℕ) : ℕ :=
  runIndex key T (T.idxOf i)

/-- Composite key `z_i = (n+1) gid[i] + i` (stage S4). -/
def compositeKey (key : ℕ → K) (T : List ℕ) (n i : ℕ) : ℕ :=
  (n + 1) * groupId key T i + i

/-- The output of the closure reduction: the compacted padded-sort output (stage S5). -/
def closureOutput (P : List (Option ℕ)) : List ℕ := compact P

/-- The closure reduction as an algorithm with two oracles: `usemi` (unstable semisort) and
`psort` (padded sorting on `n` records with keys below `(n+1)^2`). -/
def stableSemisortViaPadded (usemi : (ℕ → K) → List ℕ) (psort : (ℕ → ℕ) → List (Option ℕ))
    (n : ℕ) (key : ℕ → K) : List ℕ :=
  closureOutput (psort (compositeKey key (usemi key) n))

/-- **Theorem 3.1 (closure reduction), correctness.** Let `T` be any valid output of an
unstable semisort of the records `0, …, n-1` (stages S1–S2), and let `P` be any valid output of
`PaddedSort(n,(n+1)^2)` on the composite keys `z_i = (n+1) gid[i] + i` built from `T` (stages
S3–S4). Then the composite keys form a valid instance (distinct, below `(n+1)^2`), and the
compaction of `P` (stage S5) is a stable semisort. -/
theorem closure_correct (key : ℕ → K) (n : ℕ) (T : List ℕ) (hT : IsSemisort key n T)
    (P : List (Option ℕ)) (hP : IsPaddedSort (compositeKey key T n) n P) :
    IsDistinctKeyInstance (compositeKey key T n) n ((n + 1) ^ 2) ∧
      IsStableSemisort key n (closureOutput P) := by
  sorry

/-- **Theorem 3.1, oracle form: `SS ⪯ PaddedSort + USemi`.** If `usemi` returns a valid
unstable semisort and `psort` solves every valid instance of `PaddedSort(n,(n+1)^2)`, then the
closure reduction returns a stable semisort. -/
theorem stableSemisort_of_paddedSort (usemi : (ℕ → K) → List ℕ)
    (psort : (ℕ → ℕ) → List (Option ℕ)) (n : ℕ) (key : ℕ → K)
    (hU : IsSemisort key n (usemi key))
    (hP : ∀ z : ℕ → ℕ, IsDistinctKeyInstance z n ((n + 1) ^ 2) → IsPaddedSort z n (psort z)) :
    IsStableSemisort key n (stableSemisortViaPadded usemi psort n key) := by
  sorry

end

section
open Finset

/-- Segmented scan: offset of position `p` inside its run of equal values of `f`. -/
def segOffset {K : Type*} [DecidableEq K] (f : ℕ → K) : ℕ → ℕ
  | 0 => 0
  | p + 1 => if f (p + 1) = f p then segOffset f p + 1 else 0

/-- The group length `L[k]`: the number of records with key `k` in the semisorted list `out`. -/
def groupLen (a : ℕ → ℕ) (out : List ℕ) (k : ℕ) : ℕ :=
  out.countP (fun i => a i = k)

/-- Exclusive prefix sum `B[k] = ∑_{k' < k} L[k']`. -/
def groupBase (a : ℕ → ℕ) (out : List ℕ) (k : ℕ) : ℕ :=
  ∑ k' ∈ range k, groupLen a out k'

/-- Target position `B[a(out[p])] + offset(p)` of the record at position `p` of `out`. -/
def intSortTarget (a : ℕ → ℕ) (out : List ℕ) (p : ℕ) : ℕ :=
  groupBase a out (a (out.getD p 0)) + segOffset (fun p => a (out.getD p 0)) p

/-- Exclusive scatter: cell `t < m` receives the entry of `src` at the position `p` with
`pos p = t` (the first one, if several; in our use there is exactly one). -/
def scatter (m : ℕ) (pos : ℕ → ℕ) (src : List ℕ) : List ℕ :=
  (List.range m).map fun t =>
    src.getD (((List.range src.length).find? fun p => pos p = t).getD 0) 0

/-- Theorem 4.1(b), `IS ⪯ SS`: the stable integer sort computed from a stable semisort. -/
def intSortViaSS (a : ℕ → ℕ) (n : ℕ) (out : List ℕ) : List ℕ :=
  scatter n (intSortTarget a out) out

/-- Theorem 4.1(a), `DS ⪯ IS`: two-digit least-significant-digit radix sort with an `IS`
oracle. The second pass sorts the records in the order produced by the first pass. -/
def distinctSortViaIS (n : ℕ) (isort : (ℕ → ℕ) → List ℕ) (z : ℕ → ℕ) : List ℕ :=
  let O1 := isort (fun i => z i % (n + 1))
  let O2 := isort (fun t => z (O1.getD t 0) / (n + 1))
  O2.map (fun t => O1.getD t 0)

/-- `PaddedSort(n,(n+1)^2) ⪯ SS`: the composition of `DS ⪯ IS`, `IS ⪯ SS` and Lemma 2.4. -/
def paddedSortViaSS (n : ℕ) (ssort : (ℕ → ℕ) → List ℕ) (z : ℕ → ℕ) : List (Option ℕ) :=
  (distinctSortViaIS n (fun a => intSortViaSS a n (ssort a)) z).map some

/-- **Converse reduction: `PaddedSort(n,(n+1)^2) ⪯ SS`** (Theorem 4.1(a),(b) with Lemma 2.4;
no unstable semisort is used). If `ssort` returns a stable semisort for every integer-keyed
instance with keys in `[0,n]`, then `paddedSortViaSS` (two `IS` calls, each made of one `SS`
call plus scans and a scatter, then padding with `c = 1`) solves every valid instance of
`PaddedSort(n,(n+1)^2)`. -/
theorem paddedSort_of_stableSemisort (n : ℕ) (ssort : (ℕ → ℕ) → List ℕ)
    (hss : ∀ a : ℕ → ℕ, (∀ i < n, a i ≤ n) → IsStableSemisort a n (ssort a))
    (z : ℕ → ℕ) (hz : IsDistinctKeyInstance z n ((n + 1) ^ 2)) :
    IsPaddedSort z n (paddedSortViaSS n ssort z) := by
  sorry

end

section
open Finset

/-- Group size `f_h = |{i : g_i = h}|`. -/
def groupFreq (g : ℕ → ℕ) (n h : ℕ) : ℕ := #((range n).filter fun i => g i = h)

/-- Group offset `B_h = ∑_{h' < h} f_{h'}`. -/
def groupOffset (g : ℕ → ℕ) (n h : ℕ) : ℕ := ∑ h' ∈ range h, groupFreq g n h'

/-- Prediction `p_i = B_{g_i} + q_i`. -/
def prediction (g q : ℕ → ℕ) (n i : ℕ) : ℕ := groupOffset g n (g i) + q i

/-- Definition 6.1: the prediction-alignment error
`PAE(y,p) = ∑_i |{j : y_j > y_i, p_j ≤ p_i}|` for the keys `y_i = (g_i, i)`. -/
def predictionAlignmentError (g q : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ i ∈ range n, #((range n).filter fun j =>
    (g i < g j ∨ (g i = g j ∧ i < j)) ∧ prediction g q n j ≤ prediction g q n i)

/-- Cell size `c_{h,r} = |{i : g_i = h, q_i = r}|`. -/
def cellSize (g q : ℕ → ℕ) (n : ℕ) (c : ℕ × ℕ) : ℕ :=
  #((range n).filter fun i => (g i, q i) = c)

/-- Collision energy `E_coll(q) = ∑_{h,r} C(c_{h,r}, 2)` (the sum over nonempty cells; empty
cells contribute `0`). -/
def collisionEnergy (g q : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ c ∈ (range n).image (fun i => (g i, q i)), (cellSize g q n c).choose 2

/-- **Lemma 6.2 (collision-energy identity).** For labels `q_i ≤ f_{g_i} - 1` that are
nondecreasing in `i` inside each group, the prediction-alignment error of the predictions
`p_i = B_{g_i} + q_i` equals the collision energy. -/
theorem predictionAlignmentError_eq_collisionEnergy (g q : ℕ → ℕ) (n : ℕ)
    (hq : ∀ i < n, q i < groupFreq g n (g i))
    (hmono : ∀ i < n, ∀ j < n, i < j → g i = g j → q i ≤ q j) :
    predictionAlignmentError g q n = collisionEnergy g q n := by
  sorry

/-- The collision energy of one group `s` under labels `q`: `∑_r C(c_r, 2)` over the labels `r`
that occur, `c_r = |{i ∈ s : q_i = r}|`. -/
def groupCollisionEnergy (s : Finset ℕ) (q : ℕ → ℕ) : ℕ :=
  ∑ r ∈ s.image q, (#(s.filter fun i => q i = r)).choose 2

/-- **Theorem 7.3 (density barrier).** If a group of size `f` is labeled with at most `k + 1`
distinct values, its collision energy is at least `(f²/(k+1) - f)/2`. (Monotonicity of the
labels is not needed.) -/
theorem density_barrier (s : Finset ℕ) (q : ℕ → ℕ) (k : ℕ) (hk : #(s.image q) ≤ k + 1) :
    ((#s : ℝ) ^ 2 / (k + 1) - #s) / 2 ≤ groupCollisionEnergy s q := by
  sorry

end

end GC.Semisort
