import GC.Computability.NewtonStrahler.HornLayers

/-!
# Truth-table Horn systems

Lemma 7.2 of "Horn Saturation in Strahler-Rank Reachability Rounds": the truth-table Horn system
of a Boolean circuit of fan-in at most two derives exactly the true facts `Val(g, b)`, and the
true fact of a gate has proof rank at most the depth of the gate.
-/

namespace GC.NewtonStrahler

/-- A gate of a Boolean circuit of fan-in at most two with fixed inputs. -/
inductive BGate (n : ℕ) where
  | input (b : Bool)
  | unary (φ : Bool → Bool) (g₁ : Fin n)
  | binary (φ : Bool → Bool → Bool) (g₁ g₂ : Fin n)

/-- Well-formedness: inputs of gate `i` precede `i`, and the two inputs of a binary gate are
distinct. -/
def BGate.WF {n : ℕ} (i : Fin n) : BGate n → Prop
  | .input _ => True
  | .unary _ g₁ => g₁ < i
  | .binary _ g₁ g₂ => g₁ < i ∧ g₂ < i ∧ g₁ ≠ g₂

/-- A Boolean circuit of fan-in at most two with fixed inputs. -/
structure BCircuit (n : ℕ) where
  gate : Fin n → BGate n
  wf : ∀ i, (gate i).WF i

/-- The value of a gate given the values of all gates. -/
def BGate.eval {n : ℕ} : BGate n → (Fin n → Bool) → Bool
  | .input b, _ => b
  | .unary φ g₁, v => φ (v g₁)
  | .binary φ g₁ g₂, v => φ (v g₁) (v g₂)

variable {n : ℕ}

/-- `v` is the value vector of the circuit. -/
def BCircuit.IsValue (C : BCircuit n) (v : Fin n → Bool) : Prop :=
  ∀ i, v i = (C.gate i).eval v

/-- The depth of a gate: `0` for an input, one more than the largest depth of an input of the
gate otherwise. -/
def BCircuit.depth (C : BCircuit n) (i : Fin n) : ℕ :=
  match _h : C.gate i with
  | .input _ => 0
  | .unary _ g₁ => C.depth g₁ + 1
  | .binary _ g₁ g₂ => max (C.depth g₁) (C.depth g₂) + 1
termination_by i.val
decreasing_by
  all_goals
    have hw := C.wf i
    rw [_h] at hw
    simp only [BGate.WF] at hw
  · exact hw
  · exact hw.1
  · exact hw.2.1

/-- The rules of the truth-table system contributed by gate `g`. -/
def BCircuit.gateRules (C : BCircuit n) (g : Fin n) : List (Rule (Fin n × Bool)) :=
  match C.gate g with
  | .input _ => []
  | .unary φ g₁ => [false, true].map fun b₁ => ⟨{(g₁, b₁)}, (g, φ b₁)⟩
  | .binary φ g₁ g₂ =>
      [(false, false), (false, true), (true, false), (true, true)].map fun b =>
        ⟨{(g₁, b.1), (g₂, b.2)}, (g, φ b.1 b.2)⟩

/-- The truth-table Horn system (Lemma 7.2): facts `Val(g, b) = (g, b)`, axioms `Val(g, b)` for
input gates of value `b`, and for every gate and every pair of input values the rule
`{Val(g₁, b₁), Val(g₂, b₂)} ⇒ Val(g, φ_g(b₁, b₂))` (one premise for gates of fan-in one). -/
def BCircuit.truthTable (C : BCircuit n) : HornSystem (Fin n × Bool) where
  axioms := {f | C.gate f.1 = .input f.2}
  rules := (List.finRange n).flatMap C.gateRules

lemma BCircuit.depth_input {C : BCircuit n} {i : Fin n} {b : Bool} (h : C.gate i = .input b) :
    C.depth i = 0 := by
  rw [BCircuit.depth.eq_def]; split <;> simp_all

lemma BCircuit.depth_unary {C : BCircuit n} {i g₁ : Fin n} {φ : Bool → Bool}
    (h : C.gate i = .unary φ g₁) : C.depth i = C.depth g₁ + 1 := by
  rw [BCircuit.depth.eq_def]; split <;> simp_all

lemma BCircuit.depth_binary {C : BCircuit n} {i g₁ g₂ : Fin n} {φ : Bool → Bool → Bool}
    (h : C.gate i = .binary φ g₁ g₂) : C.depth i = max (C.depth g₁) (C.depth g₂) + 1 := by
  rw [BCircuit.depth.eq_def]; split <;> simp_all

/-- Soundness: only true facts are derivable. -/
theorem BCircuit.truthTable_sound {C : BCircuit n} {v : Fin n → Bool} (hv : C.IsValue v)
    {f : Fin n × Bool} (T : Deriv C.truthTable f) : f.2 = v f.1 := by
  induction T with
  | ax h =>
    rename_i f
    have h' : C.gate f.1 = .input f.2 := h
    rw [hv f.1, h']; rfl
  | node r hr sub ih =>
    simp only [BCircuit.truthTable, List.mem_flatMap, List.mem_finRange, true_and] at hr
    obtain ⟨g, hg⟩ := hr
    unfold BCircuit.gateRules at hg
    split at hg <;> rename_i heq
    · simp at hg
    · rename_i φ g₁
      obtain ⟨b₁, -, rfl⟩ := List.mem_map.mp hg
      have h1 : b₁ = v g₁ := ih (g₁, b₁) (Finset.mem_singleton_self _)
      show φ b₁ = v g
      rw [hv g, heq, BGate.eval, h1]
    · rename_i φ g₁ g₂
      obtain ⟨b, -, rfl⟩ := List.mem_map.mp hg
      have h1 : b.1 = v g₁ := ih (g₁, b.1) (by simp)
      have h2 : b.2 = v g₂ := ih (g₂, b.2) (by simp)
      show φ b.1 b.2 = v g
      rw [hv g, heq, BGate.eval, h1, h2]

/-- Completeness with the rank bound: the true fact `Val(g, v g)` has a derivation tree of rank
at most the depth of `g`. -/
theorem BCircuit.truthTable_rank_le_depth {C : BCircuit n} {v : Fin n → Bool}
    (hv : C.IsValue v) (g : Fin n) : (g, v g) ∈ rankLayer C.truthTable (C.depth g) := by
  classical
  induction g using WellFoundedLT.induction with
  | ind g ih =>
    have hw := C.wf g
    have hmem : ∀ r ∈ C.gateRules g, r ∈ C.truthTable.rules := fun r hr => by
      simp only [BCircuit.truthTable, List.mem_flatMap, List.mem_finRange, true_and]
      exact ⟨g, hr⟩
    rcases hg : C.gate g with b | ⟨φ, g₁⟩ | ⟨φ, g₁, g₂⟩
    · have hax : (g, v g) ∈ C.truthTable.axioms := by
        show C.gate g = .input (v g)
        rw [hg, hv g, hg]; rfl
      exact ⟨Deriv.ax hax, by simp [Deriv.rank]⟩
    · rw [hg] at hw
      simp only [BGate.WF] at hw
      obtain ⟨T₁, hT₁⟩ := ih g₁ hw
      let r : Rule (Fin n × Bool) := ⟨{(g₁, v g₁)}, (g, φ (v g₁))⟩
      have hr : r ∈ C.truthTable.rules := hmem r (by
        unfold BCircuit.gateRules; rw [hg]
        exact List.mem_map.mpr ⟨v g₁, by cases v g₁ <;> simp, rfl⟩)
      have hconcl : r.concl = (g, v g) := by
        show (g, φ (v g₁)) = (g, v g)
        rw [hv g, hg]; rfl
      rw [← hconcl, BCircuit.depth_unary hg]
      refine concl_mem_rankLayer hr fun p hp => ?_
      rw [Finset.mem_singleton.mp hp, rankBelow_succ]
      exact ⟨T₁, hT₁⟩
    · rw [hg] at hw
      simp only [BGate.WF] at hw
      obtain ⟨h₁, h₂, -⟩ := hw
      let r : Rule (Fin n × Bool) := ⟨{(g₁, v g₁), (g₂, v g₂)}, (g, φ (v g₁) (v g₂))⟩
      have hr : r ∈ C.truthTable.rules := hmem r (by
        unfold BCircuit.gateRules; rw [hg]
        exact List.mem_map.mpr ⟨(v g₁, v g₂), by cases v g₁ <;> cases v g₂ <;> simp, rfl⟩)
      have hconcl : r.concl = (g, v g) := by
        show (g, φ (v g₁) (v g₂)) = (g, v g)
        rw [hv g, hg]; rfl
      rw [← hconcl, BCircuit.depth_binary hg]
      refine concl_mem_rankLayer hr fun p hp => ?_
      rw [rankBelow_succ]
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact rankLayer_mono _ (le_max_left _ _) (ih g₁ h₁)
      · rw [Finset.mem_singleton.mp hp]
        exact rankLayer_mono _ (le_max_right _ _) (ih g₂ h₂)

/-- **Lemma 7.2 (truth-table systems).** `Val(g, b)` is derivable if and only if `b` is the value
of `g`, and the true fact `Val(g, v g)` has proof rank at most the depth of `g`. -/
theorem BCircuit.truthTable_spec {C : BCircuit n} {v : Fin n → Bool} (hv : C.IsValue v)
    (g : Fin n) (b : Bool) :
    (Nonempty (Deriv C.truthTable (g, b)) ↔ b = v g) ∧
      (g, v g) ∈ rankLayer C.truthTable (C.depth g) := by
  refine ⟨⟨fun ⟨T⟩ => BCircuit.truthTable_sound hv T, ?_⟩, BCircuit.truthTable_rank_le_depth hv g⟩
  rintro rfl
  obtain ⟨T, -⟩ := BCircuit.truthTable_rank_le_depth hv g
  exact ⟨T⟩

end GC.NewtonStrahler
