import GC.GroupTheory.A5Programs.Scans
import GC.GroupTheory.A5Programs.TwoGen
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# One entry is a power program; dominators condense (manuscript 004d)

* `oneEntry_power`: in a program with a single entry `r`, every node is `x^(a_v)` for every
  value `x` of the entry, with integer exponents given by the local rules `a_r = 1`,
  `a_{uv} = a_u + a_v`, `a_{u⁻¹} = -a_u` (Theorem 3.1). The exponents are the values of the
  program in the additive group `ℤ`.
* `thirty_classes`: over `A₅` the exponents may be reduced modulo 30, so a one-entry region has
  at most 30 distinct value functions and nodes with equal exponents agree for every entry value
  (Corollary 3.2).
* `dominator_power`: if a node `d` dominates `v` (every path from an entry to `v` passes through
  `d`), then `val v = (val d)^a` for an exponent `a` independent of the values of the entries
  (Theorem 4.3, main statement); `inv_gate_dominated`, `square_gate_dominated`: inverse and
  squaring gates are dominated by their operand, so they are never prime (Theorem 4.3(iii)).
* `dichotomy`: one entry is a power program, while two entries already carry every Boolean
  circuit (Theorem 6.1).
-/

namespace GC.A5Programs

open Equiv

/-! ## One entry -/

/-- Exponents of the nodes of a one-entry program: its values in `Multiplicative ℤ` with the
entry `1`. -/
def oneEntryExp (ops : List (Op Unit)) (k : ℕ) : ℤ :=
  Multiplicative.toAdd (val (fun _ => Multiplicative.ofAdd (1 : ℤ)) ops k)

/-- The local rules for the exponents (004d, Theorem 3.1). -/
theorem oneEntryExp_snoc (ops : List (Op Unit)) (op : Op Unit) :
    oneEntryExp (ops ++ [op]) ops.length =
      match op with
      | .leaf _ => 1
      | .mul i j => oneEntryExp ops i + oneEntryExp ops j
      | .inv i => - oneEntryExp ops i := by
  unfold oneEntryExp
  rw [val_snoc, if_neg (lt_irrefl _), if_pos rfl]
  cases op <;> rfl

/-- **One-generator power normal form** (004d, Theorem 3.1). In a program over any group whose
only leaves are the entry `r`, node `k` equals `x ^ a_k` for every value `x` of `r`. -/
theorem oneEntry_power {G : Type*} [Group G] (ops : List (Op Unit)) (k : ℕ) (x : G) :
    val (fun _ => x) ops k = x ^ oneEntryExp ops k := by
  have h := map_val (zpowersHom G x) (fun _ => Multiplicative.ofAdd (1 : ℤ)) ops k
  have hν : (zpowersHom G x) ∘ (fun _ : Unit => Multiplicative.ofAdd (1 : ℤ)) = fun _ => x := by
    funext u; simp
  rw [hν] at h
  rw [← h]
  simp [oneEntryExp]

/-- **Thirty-class contraction** (004d, Corollary 3.2). Over `A₅`, with exponents reduced
modulo 30, every node of a one-entry region is `x ^ e_k` with `e_k ∈ ZMod 30`; nodes with the
same residue are equal for every entry value, and there are at most 30 value functions. -/
theorem thirty_classes (ops : List (Op Unit)) :
    (∀ k (x : A5), val (fun _ => x) ops k = x ^ ((oneEntryExp ops k : ZMod 30).val)) ∧
    (∀ k l, (oneEntryExp ops k : ZMod 30) = oneEntryExp ops l →
      ∀ x : A5, val (fun _ => x) ops k = val (fun _ => x) ops l) ∧
    ((Finset.range ops.length).image (fun k => fun x : A5 => val (fun _ => x) ops k)).card
      ≤ 30 := by
  have hmod : ∀ (n : ℤ) (x : A5), x ^ n = x ^ ((n : ZMod 30).val) := by
    intro n x
    have h30 : x ^ (30 : ℤ) = 1 := by
      rw [show (30 : ℤ) = ((30 : ℕ) : ℤ) from rfl, zpow_natCast, A5_pow30]
    rw [← zpow_natCast, ZMod.val_intCast]
    conv_lhs => rw [← Int.emod_add_mul_ediv n 30]
    rw [zpow_add, zpow_mul, h30, one_zpow, mul_one]
    rfl
  have h1 : ∀ k (x : A5), val (fun _ => x) ops k = x ^ ((oneEntryExp ops k : ZMod 30).val) :=
    fun k x => by rw [oneEntry_power, hmod]
  refine ⟨h1, fun k l hkl x => by rw [h1, h1, hkl], ?_⟩
  classical
  have : (Finset.range ops.length).image (fun k => fun x : A5 => val (fun _ => x) ops k) ⊆
      (Finset.univ : Finset (ZMod 30)).image (fun e => fun x : A5 => x ^ e.val) := by
    intro f hf
    simp only [Finset.mem_image, Finset.mem_range] at hf
    obtain ⟨k, _, rfl⟩ := hf
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨oneEntryExp ops k, funext fun x => (h1 k x).symm⟩
  calc _ ≤ _ := Finset.card_le_card this
    _ ≤ (Finset.univ : Finset (ZMod 30)).card := Finset.card_image_le
    _ = 30 := by simp

/-! ## Dominators -/

section Dominators

variable {α : Type} (ops : List (Op α))

/-- `Avoids d v`: node `v` is reached from some entry along a path that does not pass
through `d` (paths follow operand arcs). -/
inductive Avoids (d : ℕ) : ℕ → Prop
  | leaf {v : ℕ} {a : α} : v ≠ d → ops[v]? = some (.leaf a) → Avoids d v
  | mulLeft {v i j : ℕ} : v ≠ d → ops[v]? = some (.mul i j) → Avoids d i → Avoids d v
  | mulRight {v i j : ℕ} : v ≠ d → ops[v]? = some (.mul i j) → Avoids d j → Avoids d v
  | inv {v i : ℕ} : v ≠ d → ops[v]? = some (.inv i) → Avoids d i → Avoids d v

/-- `d` dominates the node `v`: every path from an entry (from the added source) to `v` passes
through `d`. -/
def Dominates (d v : ℕ) : Prop := v < ops.length ∧ ¬ Avoids ops d v

variable {G : Type*} [Group G]

/-- **Dominator power condensation** (004d, Theorem 4.3). In a well-formed program over any
group, if `d` dominates `v`, then `val v = (val d)^a` for an integer exponent `a` that does not
depend on the values assigned to the entries. -/
theorem dominator_power (hwf : WellFormed ops) {d v : ℕ} (hdom : Dominates ops d v) :
    ∃ a : ℤ, ∀ ν : α → G, val ν ops v = (val ν ops d) ^ a := by
  obtain ⟨hv, hnav⟩ := hdom
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    by_cases hvd : v = d
    · exact ⟨1, fun ν => by rw [hvd, zpow_one]⟩
    have hget : ops[v]? = some (ops[v]'hv) := List.getElem?_eq_getElem hv
    have hw := hwf v hv
    -- an operand of `v` is `d` or is dominated by `d`
    have hop : ∀ u, u < v → (∀ (hA : Avoids ops d u), Avoids ops d v) →
        ∃ a : ℤ, ∀ ν : α → G, val ν ops u = (val ν ops d) ^ a := by
      intro u huv hlift
      by_cases hud : u = d
      · exact ⟨1, fun ν => by rw [hud, zpow_one]⟩
      · exact ih u huv (by omega) (fun hA => hnav (hlift hA))
    have hval : ∀ (ν : α → G), val ν ops v = (ops[v]'hv).step ν (evalProg ν (ops.take v)) :=
      fun ν => val_of_lt ν ops hv
    have hpre : ∀ (ν : α → G) i, i < v → val ν (ops.take v) i = val ν ops i := by
      intro ν i hi
      conv_rhs => rw [← List.take_append_drop v ops]
      rw [val_append_of_lt _ _ _ (by simp; omega)]
    cases hcase : ops[v]'hv with
    | leaf a =>
      exfalso; rw [hcase] at hget; exact hnav (.leaf hvd hget)
    | mul i j =>
      rw [hcase] at hget hw
      obtain ⟨a, ha⟩ := hop i hw.1 (fun hA => .mulLeft hvd hget hA)
      obtain ⟨b, hb⟩ := hop j hw.2 (fun hA => .mulRight hvd hget hA)
      refine ⟨a + b, fun ν => ?_⟩
      rw [hval, hcase]
      show val ν (ops.take v) i * val ν (ops.take v) j = _
      rw [hpre ν i hw.1, hpre ν j hw.2, ha, hb, zpow_add]
    | inv i =>
      rw [hcase] at hget hw
      obtain ⟨a, ha⟩ := hop i hw (fun hA => .inv hvd hget hA)
      refine ⟨-a, fun ν => ?_⟩
      rw [hval, hcase]
      show (val ν (ops.take v) i)⁻¹ = _
      rw [hpre ν i hw, ha, zpow_neg]

/-- An inverse gate is dominated by its operand (004d, Theorem 4.3(iii)). -/
theorem inv_gate_dominated {v i : ℕ} (hv : v < ops.length) (h : ops[v]? = some (.inv i)) :
    Dominates ops i v := by
  refine ⟨hv, fun hA => ?_⟩
  cases hA with
  | leaf _ h' => rw [h] at h'; cases h'
  | mulLeft _ h' _ => rw [h] at h'; cases h'
  | mulRight _ h' _ => rw [h] at h'; cases h'
  | inv hne h' hA' =>
    rw [h] at h'; cases h'
    cases hA' with
    | leaf hne' _ => exact hne' rfl
    | mulLeft hne' _ _ => exact hne' rfl
    | mulRight hne' _ _ => exact hne' rfl
    | inv hne' _ _ => exact hne' rfl

/-- A squaring gate `u · u` is dominated by its operand (004d, Theorem 4.3(iii)). -/
theorem square_gate_dominated {v i : ℕ} (hv : v < ops.length) (h : ops[v]? = some (.mul i i)) :
    Dominates ops i v := by
  refine ⟨hv, fun hA => ?_⟩
  have hstart : ∀ w, Avoids ops i w → w = i → False := by
    intro w hA hw
    cases hA with
    | leaf hne _ => exact hne hw
    | mulLeft hne _ _ => exact hne hw
    | mulRight hne _ _ => exact hne hw
    | inv hne _ _ => exact hne hw
  cases hA with
  | leaf _ h' => rw [h] at h'; cases h'
  | mulLeft _ h' hA' => rw [h] at h'; cases h'; exact hstart _ hA' rfl
  | mulRight _ h' hA' => rw [h] at h'; cases h'; exact hstart _ hA' rfl
  | inv _ h' _ => rw [h] at h'; cases h'

end Dominators

/-- **One entry versus two entries** (004d, Theorem 6.1, mathematical content). (i) Over every
group, a program with one entry computes only powers of the entry, with exponents given by the
local rules. (ii) Programs with the two entries `P ↦ p`, `Q ↦ q` of `A₅` and no constants carry
every Boolean circuit: the copy of each Boolean node evaluates to `e` or `a` according to its
value (with size at most `17 s + 60`). -/
theorem dichotomy :
    (∀ {G : Type} [Group G] (ops : List (Op Unit)) (k : ℕ) (x : G),
      val (fun _ => x) ops k = x ^ oneEntryExp ops k) ∧
    (∀ bs : List BOp, BWellFormed bs →
      WellFormed (normalForm (compile bs).1) ∧
      (normalForm (compile bs).1).length ≤ 17 * bs.length + 60 ∧
      ∀ k < bs.length,
        val pq (normalForm (compile bs).1) (60 + (compile bs).2.getD k 0) = enc (bval bs k)) :=
  ⟨fun ops k x => oneEntry_power ops k x, fun bs hbs => boolean_to_twoGen bs hbs⟩

end GC.A5Programs
