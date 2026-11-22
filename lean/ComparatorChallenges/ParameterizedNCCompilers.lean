import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Logic.Function.Iterate
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card
import Mathlib.Tactic.IntervalCases

namespace GC.StructuralCompilers

/-- A legal parent array: `j i < i` for every positive coordinate `i`. -/
structure ParentArray where
  /-- the parent pointers `j₁, j₂, …` (the value at `0` is unused) -/
  j : ℕ → ℕ
  /-- legality: `0 ≤ jᵢ < i` -/
  lt : ∀ i, 1 ≤ i → j i < i

/-- The Sequential NOR trace: `x₀ = 1`, `x_{i} = NOR(x_{i-1}, x_{j_i})`. -/
def ParentArray.x (J : ParentArray) : ℕ → Bool
  | 0 => true
  | i + 1 =>
    have : J.j (i + 1) < i + 1 := J.lt (i + 1) (Nat.succ_pos i)
    !(J.x i || J.x (J.j (i + 1)))

/-- `maskVal R q = x_q(R)`: it is `1` at `q = 0`, `0` at a reset `R q = 1`, and alternates
between resets (Definition 3.1). -/
def maskVal (R : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | q + 1 => if R (q + 1) then false else !(maskVal R q)

/-- `Φ_j(R)ᵢ = x_{jᵢ}(R)`. -/
def phiMap (J : ParentArray) (R : ℕ → Bool) : ℕ → Bool := fun i => maskVal R (J.j i)

/-- The true mask `R⋆ᵢ = x_{jᵢ}`. -/
def trueMask (J : ParentArray) : ℕ → Bool := fun i => J.x (J.j i)

/-- Agreement of two masks on the positions `1, …, n`. -/
def AgreeUpTo (n : ℕ) (Q R : ℕ → Bool) : Prop := ∀ i, 1 ≤ i → i ≤ n → Q i = R i

/-- The defect `dᵢ(Q) = Qᵢ ⊕ Φ_j(Q)ᵢ`. -/
def defect (J : ParentArray) (Q : ℕ → Bool) (i : ℕ) : Bool := xor (Q i) (phiMap J Q i)

/-- The prefix OR `bᵢ(Q) = ⋁_{1 ≤ h ≤ i} d_h(Q)`. -/
def prefixDefect (J : ParentArray) (Q : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | i + 1 => prefixDefect J Q i || defect J Q (i + 1)

/-- One greedy repair round `T_j(Q)ᵢ = Qᵢ ⊕ bᵢ(Q)` (equation (3.1)). -/
def repairStep (J : ParentArray) (Q : ℕ → Bool) : ℕ → Bool :=
  fun i => xor (Q i) (prefixDefect J Q i)

/-- The number of switches `|{i ∈ {2, …, n} : eᵢ ≠ eᵢ₋₁}|` of an error vector. -/
def switchCount (n : ℕ) (e : ℕ → Bool) : ℕ :=
  ((Finset.Icc 2 n).filter (fun i => e i ≠ e (i - 1))).card

/-- **Lemma 3.2 (existence).** `R⋆` is a fixed point of `Φ_j`, and `x_q(R⋆) = x_q`. -/
theorem trueMask_fixed (J : ParentArray) :
    phiMap J (trueMask J) = trueMask J ∧ ∀ q, maskVal (trueMask J) q = J.x q := by
  sorry

/-- **Lemma 3.2 (uniqueness).** A mask that is a fixed point of `Φ_j` on `1, …, n` agrees with
`R⋆` on `1, …, n`. -/
theorem fixedPoint_unique (J : ParentArray) (n : ℕ) (R : ℕ → Bool)
    (hR : AgreeUpTo n (phiMap J R) R) : AgreeUpTo n R (trueMask J) := by
  sorry

/-- The error of `Q` relative to `R⋆`. -/
def errVec (J : ParentArray) (Q : ℕ → Bool) : ℕ → Bool := fun i => xor (Q i) (trueMask J i)

/-- **Theorem 3.6 (greedy phase repair).** Let `Q⁽⁰⁾ = P` if `P₁ = 1` and `Q⁽⁰⁾ = ¬P` otherwise.
If the error `P ⊕ R⋆` has `k` switches on `1, …, n`, then `Q⁽ᵏ⁾ = T_j^k(Q⁽⁰⁾)` equals `R⋆` on
`1, …, n`, and `Q⁽ᵗ⁾` differs from `R⋆` on `1, …, n` for every `t < k`. -/
theorem greedy_phase_repair (J : ParentArray) (n : ℕ) (P : ℕ → Bool) :
    AgreeUpTo n ((repairStep J)^[switchCount n (fun i => xor (P i) (trueMask J i))]
        (if P 1 then P else fun i => !P i)) (trueMask J) ∧
      ∀ t < switchCount n (fun i => xor (P i) (trueMask J i)),
        ¬ AgreeUpTo n ((repairStep J)^[t] (if P 1 then P else fun i => !P i)) (trueMask J) := by
  sorry

/-- A normalized record of a core gate (Section 2.3). -/
inductive CoreRecord
  /-- `z_k = c` -/
  | const (c : Bool)
  /-- `z_k = z_a ⊕ σ` -/
  | copy (a : ℕ) (σ : Bool)
  /-- `z_k = NOR(z_a ⊕ σ, z_c ⊕ τ)`; `a` is the left and `c` the right source -/
  | bin (a : ℕ) (σ : Bool) (c : ℕ) (τ : Bool)

/-- Evaluation of a record on an assignment `z`. -/
def CoreRecord.eval : CoreRecord → (ℕ → Bool) → Bool
  | const c, _ => c
  | copy a σ, z => xor (z a) σ
  | bin a σ c τ, z => !(xor (z a) σ || xor (z c) τ)

/-- A record of gate `k` is well formed if it mentions only core variables `1 ≤ a < k`, and the
two sources of a binary record are distinct. -/
def CoreRecord.WF (k : ℕ) : CoreRecord → Prop
  | const _ => True
  | copy a _ => 1 ≤ a ∧ a < k
  | bin a _ c _ => 1 ≤ a ∧ a < k ∧ 1 ≤ c ∧ c < k ∧ a ≠ c

/-- A normalized core of size `m`: records for the gates `1, …, m`. -/
structure CoreSystem where
  /-- number of core gates -/
  m : ℕ
  /-- the record of gate `k` (only `1 ≤ k ≤ m` matters) -/
  record : ℕ → CoreRecord
  /-- well-formedness -/
  wf : ∀ k, 1 ≤ k → k ≤ m → (record k).WF k

/-- `a` and `c` are the left and right sources of a binary record of the core. -/
def CoreSystem.BinEdge (S : CoreSystem) (a c : ℕ) : Prop :=
  ∃ k, 1 ≤ k ∧ k ≤ S.m ∧ ∃ σ τ, S.record k = CoreRecord.bin a σ c τ

/-- The interaction graph `G_int(j)`: an edge `{a, c}` for every binary record. -/
def CoreSystem.intGraph (S : CoreSystem) : SimpleGraph ℕ := SimpleGraph.fromRel S.BinEdge

/-- Left sources. -/
def CoreSystem.leftSources (S : CoreSystem) : Set ℕ := {a | ∃ c, S.BinEdge a c}

/-- Right sources. -/
def CoreSystem.rightSources (S : CoreSystem) : Set ℕ := {c | ∃ a, S.BinEdge a c}

/-- The cover obtained from a choice of side (`true` = left sources, `false` = right sources) in
every connected component of the interaction graph. -/
def CoreSystem.sideCover (S : CoreSystem) (side : S.intGraph.ConnectedComponent → Bool) :
    Set ℕ :=
  {v | (side (S.intGraph.connectedComponentMk v) = true ∧ v ∈ S.leftSources) ∨
       (side (S.intGraph.connectedComponentMk v) = false ∧ v ∈ S.rightSources)}

open Classical in
/-- The side rule of Definition 4.4: in each component take the smaller of `L ∩ K` and `R ∩ K`,
the left one on ties. -/
noncomputable def CoreSystem.paperSide (S : CoreSystem) (K : S.intGraph.ConnectedComponent) :
    Bool :=
    decide ({v | v ∈ S.leftSources ∧ S.intGraph.connectedComponentMk v = K}.ncard ≤
      {v | v ∈ S.rightSources ∧ S.intGraph.connectedComponentMk v = K}.ncard)

/-- The interaction cover `C(j)` of Definition 4.4. -/
def CoreSystem.interactionCover (S : CoreSystem) : Set ℕ := S.sideCover S.paperSide

/-- **Lemma 4.5 (first part).** `C(j)` is a vertex cover of the interaction graph: every binary
record has a source in `C(j)`. -/
theorem interactionCover_isVertexCover (S : CoreSystem) {a c : ℕ} (h : S.BinEdge a c) :
    a ∈ S.interactionCover ∨ c ∈ S.interactionCover := by
  sorry

/-- A set `C` meets every binary record of the core. -/
def CoreSystem.IsCover (S : CoreSystem) (C : Set ℕ) : Prop :=
  ∀ a c, S.BinEdge a c → a ∈ C ∨ c ∈ C

/-- **Lemma 4.5 (second part).** Let `C` meet every binary record. Every gate `k ∉ C` has a
pointer `p < k`, either the virtual root `0` or a variable outside `C`, and a unary map
`f z : Bool → Bool`, determined by the values of `z` on the cover variables below `k`, such that
the record of `k` evaluates to `f z (z p)` whenever `z 0 = 1`. -/
theorem record_unary_outside_cover (S : CoreSystem) (C : Set ℕ) (hC : S.IsCover C)
    (k : ℕ) (hk1 : 1 ≤ k) (hkm : k ≤ S.m) :
    ∃ p, p < k ∧ (p = 0 ∨ p ∉ C) ∧
      ∃ f : (ℕ → Bool) → Bool → Bool,
        (∀ z z', (∀ i, 1 ≤ i → i < k → i ∈ C → z i = z' i) → f z = f z') ∧
        ∀ z, z 0 = true → (S.record k).eval z = f z (z p) := by
  sorry

open Classical in
/-- The residual semantics `y(X)`: the exceptional variables `k ∈ E` take the values `X k`, the
other gates are evaluated from their records in increasing order; index `0` is a virtual node of
value `1`. -/
noncomputable def CoreSystem.residual (S : CoreSystem) (E : Set ℕ) (X : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | k + 1 =>
      if k + 1 ∈ E then X (k + 1)
      else (S.record (k + 1)).eval (fun i => if _h : i < k + 1 then S.residual E X i else false)

/-- `i` lies on the pointer chain `k, p k, p (p k), …`. -/
def OnChain (p : ℕ → ℕ) (k i : ℕ) : Prop := ∃ t, p^[t] k = i

open Classical in
/-- The ordered ancestry product `h_{k,n} ∘ ⋯ ∘ h_{k,1}` with `h_{k,i} = F i` if `i` lies on the
chain of `k` and `i ∉ C`, and `h_{k,i} = id` otherwise (proof of Theorem 4.6). -/
noncomputable def ancestryProduct (p : ℕ → ℕ) (C : Set ℕ) (F : ℕ → Bool → Bool) (k : ℕ) :
    ℕ → Bool → Bool
  | 0 => id
  | n + 1 =>
      (if OnChain p k (n + 1) ∧ n + 1 ∉ C then F (n + 1) else id) ∘
        ancestryProduct p C F k n

/-- **Theorem 4.6, corrected residual evaluator.** Let `C` meet every binary record. There are a
pointer map `p` (with `p k < k`, `p k = 0` or `p k ∉ C`) and unary maps `f X k`, each determined
by the values of `X` on the cover variables below `k`, such that for every assignment `X` of the
cover variables and every gate `k ∉ C` of the core, the residual value is
`y_k(X) = (h_{k,m} ∘ ⋯ ∘ h_{k,1})(1)`, where `h_{k,i} = f X i` if `i` lies on the pointer chain of
`k` and `h_{k,i} = id` otherwise. -/
theorem residual_eq_ancestryProduct (S : CoreSystem) (C : Set ℕ) (hC : S.IsCover C) :
    ∃ (p : ℕ → ℕ) (f : (ℕ → Bool) → ℕ → Bool → Bool),
      (∀ k, 1 ≤ k → k ≤ S.m → k ∉ C → p k < k ∧ (p k = 0 ∨ p k ∉ C)) ∧
      (∀ X X' k, (∀ i, 1 ≤ i → i < k → i ∈ C → X i = X' i) → f X k = f X' k) ∧
      ∀ X k, 1 ≤ k → k ≤ S.m → k ∉ C →
        S.residual C X k = ancestryProduct p C (f X) k S.m true := by
  sorry

/-- The chain of Remark 4.7 with two stages: `y₀ = 1` (gate 1), cover variables `c₁` (gate 2)
and `c₂` (gate 5), `a_r = NOR(c_r, y_{r-1})`, `y_r = NOR(c_r, a_r)` (gates 3, 4, 6, 7). -/
def chainExample : CoreSystem where
  m := 7
  record := fun k =>
    match k with
    | 1 => .const true
    | 2 => .const false
    | 3 => .bin 2 false 1 false
    | 4 => .bin 2 false 3 false
    | 5 => .const false
    | 6 => .bin 5 false 4 false
    | 7 => .bin 5 false 6 false
    | _ => .const false
  wf := by
    intro k hk1 hkm
    interval_cases k <;> simp [CoreRecord.WF]

/-- The cover variables of the chain. -/
def chainCover : Set ℕ := {2, 5}

/-- **Remark 4.7.** The claim of the source notes, that relative to the cover variables every
residual value is a constant or a signed copy `X_i ⊕ σ` of a single variable, is false: on the
two-stage chain, `y₂ = y₀ ∧ ¬c₁ ∧ ¬c₂` is neither. -/
theorem source_compression_claim_false :
    chainExample.IsCover chainCover ∧
    (∀ X, chainExample.residual chainCover X 7 = (!X 2 && !X 5)) ∧
    ¬ (∃ b, ∀ X, chainExample.residual chainCover X 7 = b) ∧
    ¬ (∃ i σ, ∀ X, chainExample.residual chainCover X 7 = xor (X i) σ) := by
  sorry

end GC.StructuralCompilers
