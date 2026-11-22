import GC.GroupTheory.A5Programs.Descriptors

/-!
# Opening `A₅` cycles leaves a P-complete coefficient (manuscript 004f)

* `hard_coefficient`: the cycle `q = g r`, `q = r e` is satisfiable iff `g = e`, and then every
  `r` extends uniquely (Theorem 2.1); `hard_coefficient_boolean`: with `g` the copy of a node of
  a Boolean circuit compiled into `A₅`, satisfiability decides the Boolean value
  (Corollary 2.2, mathematical core); `hard_coefficient_unique`: exactly one shift `h` makes the
  system with coefficient `g h⁻¹` satisfiable.
* `mixer_cycle`, `mixer_inverse`: the mixer `(x, y) ↦ (x y, x y²)` and its opened form
  (Lemma 3.1).
* `mixerStrip_bijective`, `mixerStrip_no_small_summary`: the transfer map of a mixer strip is a
  bijection, so no function of fewer than `W` group values determines the outputs
  (Theorem 3.2(i), (iii)).
* `nielsen_embedding`: every multiplication circuit with `s` vertices is computed by a Nielsen
  strip with `s` registers and at most `2 s` transvections `g_i ← g_i g_j`, `i ≠ j`
  (Theorem 7.2).
* Symbolic opening of a cycle (Theorem 3.3) is `cycle_monodromy` with `comp_descriptors`
  (file `Descriptors.lean`).
-/

namespace GC.A5Programs

open Equiv

section General

variable {G : Type*} [Group G]

/-- **Hard-coefficient cycle** (004f, Theorem 2.1). The two Latin factors `F₁ : q = g r` and
`F₂ : q = r e` form a cycle whose return map is `r ↦ g r`; the system is satisfiable iff
`g = e`, and then every `r` extends uniquely, by `q = r`. -/
theorem hard_coefficient (g : G) :
    ((∃ r q : G, q = g * r ∧ q = r * 1) ↔ g = 1) ∧
    (g = 1 → ∀ r : G, ∃! q : G, q = g * r ∧ q = r * 1) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨r, q, h1, h2⟩
    rw [h2, mul_one] at h1
    exact (mul_eq_right.1 h1.symm)
  · rintro rfl; exact ⟨1, 1, by simp, by simp⟩
  · rintro rfl r
    exact ⟨r, by simp, fun q hq => by rw [hq.2, mul_one]⟩

/-- Exactly one shift `h` makes the system with coefficient `g h⁻¹` satisfiable, namely
`h = g` (004f, proof of Corollary 2.2). -/
theorem hard_coefficient_unique (g : G) :
    ∃! h : G, ∃ r q : G, q = (g * h⁻¹) * r ∧ q = r * 1 := by
  refine ⟨g, ⟨1, 1, by simp, by simp⟩, fun h hh => ?_⟩
  have := (hard_coefficient (g * h⁻¹)).1.1 hh
  exact (mul_inv_eq_one.1 this).symm

/-- **Mixer cycle** (004f, Lemma 3.1): the factors `u = x y`, `v = u y` are equivalent to the
opened system `y² = x⁻¹ v`, `u = x y`. -/
theorem mixer_cycle (x y u v : G) : (u = x * y ∧ v = u * y) ↔ (y * y = x⁻¹ * v ∧ u = x * y) := by
  constructor
  · rintro ⟨rfl, rfl⟩; exact ⟨by group, rfl⟩
  · rintro ⟨h1, rfl⟩
    refine ⟨rfl, ?_⟩
    have : v = x * (y * y) := by rw [h1]; group
    rw [this]; group

/-- The mixer `M(x, y) = (x y, x y²)`. -/
def mixer (p : G × G) : G × G := (p.1 * p.2, p.1 * p.2 * p.2)

/-- The mixer is a bijection, with inverse `y = u⁻¹ v`, `x = u v⁻¹ u` (004f, Section 4). -/
theorem mixer_inverse :
    Function.LeftInverse (fun p : G × G => (p.1 * p.2⁻¹ * p.1, p.1⁻¹ * p.2)) (mixer (G := G)) ∧
    Function.RightInverse (fun p : G × G => (p.1 * p.2⁻¹ * p.1, p.1⁻¹ * p.2))
      (mixer (G := G)) := by
  refine ⟨fun p => Prod.ext ?_ ?_, fun p => Prod.ext ?_ ?_⟩ <;> simp only [mixer] <;> group

/-- The mixer as an equivalence of `G²`. -/
def mixerEquiv : G × G ≃ G × G where
  toFun := mixer
  invFun := fun p => (p.1 * p.2⁻¹ * p.1, p.1⁻¹ * p.2)
  left_inv := mixer_inverse.1
  right_inv := mixer_inverse.2

/-- Apply the mixer to registers `i ≠ j`: `(g_i, g_j) ← M(g_i, g_j)`. -/
def mixAt {W : ℕ} (i j : Fin W) (g : Fin W → G) : Fin W → G :=
  Function.update (Function.update g i (g i * g j)) j (g i * g j * g j)

theorem mixAt_bijective {W : ℕ} {i j : Fin W} (hij : i ≠ j) :
    Function.Bijective (mixAt (G := G) i j) := by
  -- the inverse mixes back with the explicit inverse formulas
  let inv : (Fin W → G) → (Fin W → G) := fun h =>
    Function.update (Function.update h i (h i * (h j)⁻¹ * h i)) j ((h i)⁻¹ * h j)
  have hji : j ≠ i := Ne.symm hij
  refine ⟨Function.LeftInverse.injective (g := inv) ?_,
    Function.RightInverse.surjective (g := inv) ?_⟩
  · intro g; funext k
    by_cases hk : k = j
    · subst hk; (simp [inv, mixAt, Function.update_of_ne hij]) <;> group
    · by_cases hk' : k = i
      · subst hk'; (simp [inv, mixAt, Function.update_of_ne hij]) <;> group
      · simp [inv, mixAt, Function.update_of_ne hk, Function.update_of_ne hk']
  · intro g; funext k
    by_cases hk : k = j
    · subst hk; (simp [inv, mixAt, Function.update_of_ne hij]) <;> group
    · by_cases hk' : k = i
      · subst hk'; (simp [inv, mixAt, Function.update_of_ne hij]) <;> group
      · simp [inv, mixAt, Function.update_of_ne hk, Function.update_of_ne hk']

/-- A mixer strip: a sequence of mixers on ordered pairs of distinct registers (a layer of
`W/2` disjoint pairs is a run of `W/2` consecutive entries). -/
def mixerStrip {W : ℕ} (pairs : List (Fin W × Fin W)) (g : Fin W → G) : Fin W → G :=
  pairs.foldl (fun h p => mixAt p.1 p.2 h) g

/-- **Mixer-strip barrier, bijectivity** (004f, Theorem 3.2(iii), first part). -/
theorem mixerStrip_bijective {W : ℕ} (pairs : List (Fin W × Fin W))
    (hp : ∀ p ∈ pairs, p.1 ≠ p.2) : Function.Bijective (mixerStrip (G := G) pairs) := by
  induction pairs using List.reverseRecOn with
  | nil => exact Function.bijective_id
  | append_singleton ps p ih =>
    have h1 := ih (fun q hq => hp q (List.mem_append_left _ hq))
    have h2 := mixAt_bijective (G := G) (hp p (by simp))
    have : mixerStrip (G := G) (ps ++ [p]) = mixAt p.1 p.2 ∘ mixerStrip ps := by
      funext g; simp [mixerStrip, List.foldl_append]
    rw [this]; exact h2.comp h1

/-- **No small summary** (004f, Theorem 3.2(iii)): for a finite group with at least two
elements, no function of fewer than `W` group values determines all output registers of a
mixer strip of width `W`. -/
theorem mixerStrip_no_small_summary [Fintype G] (hG : 2 ≤ Fintype.card G) {W : ℕ}
    (pairs : List (Fin W × Fin W)) (hp : ∀ p ∈ pairs, p.1 ≠ p.2) {k : ℕ} (hk : k < W)
    (f : (Fin W → G) → (Fin k → G)) (h : (Fin k → G) → (Fin W → G)) :
    ¬ ∀ x, h (f x) = mixerStrip pairs x := by
  intro hfh
  have hinj : Function.Injective f := by
    intro x y hxy
    apply (mixerStrip_bijective (G := G) pairs hp).1
    rw [← hfh, ← hfh, hxy]
  have := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_fun, Fintype.card_fin] at this
  have : Fintype.card G ^ W ≤ Fintype.card G ^ k := this
  have := (Nat.pow_le_pow_iff_right (by omega)).1 this
  omega

end General

/-- **Hard coefficient from a Boolean circuit** (004f, Corollary 2.2, mathematical core). Take any
Boolean circuit, compile it into `A₅` (Corollary 3.4 of 004g) and let `g` be the copy of
node `k`. The hard-coefficient cycle with coefficient `g` is satisfiable iff node `k` is false. -/
theorem hard_coefficient_boolean (bs : List BOp) (hwf : BWellFormed bs) {k : ℕ}
    (hk : k < bs.length) :
    (∃ r q : Perm (Fin 5), q = val id (compile bs).1 ((compile bs).2.getD k 0) * r ∧ q = r * 1) ↔
      bval bs k = false := by
  rw [(hard_coefficient _).1, (boolean_to_A5 bs hwf).2.2.2 k hk]
  cases bval bs k
  · simp [enc]
  · simp only [enc]; constructor
    · intro h; exact absurd h (by decide)
    · intro h; exact absurd h (by decide)

/-! ## Nielsen strips -/

section Nielsen

variable {G : Type} [Group G]

/-- The transvection `g_i ← g_i g_j`. -/
def transvect (p : ℕ × ℕ) (g : ℕ → G) : ℕ → G := Function.update g p.1 (g p.1 * g p.2)

/-- Run a list of transvections. -/
def runStrip (ts : List (ℕ × ℕ)) (g : ℕ → G) : ℕ → G :=
  ts.foldl (fun h p => transvect p h) g

theorem runStrip_append (a b : List (ℕ × ℕ)) (g : ℕ → G) :
    runStrip (a ++ b) g = runStrip b (runStrip a g) := by
  simp [runStrip, List.foldl_append]

/-- Initial registers: the value of every input, `e` for every gate. -/
def initRegs (C : List (Op G)) (k : ℕ) : G :=
  match C[k]? with
  | some (.leaf a) => a
  | _ => 1

/-- The transvections for gate `z`: `z ← z x`, then `z ← z y`. -/
def gateTrans (z : ℕ) : Op G → List (ℕ × ℕ)
  | .mul x y => [(z, x), (z, y)]
  | _ => []

/-- The Nielsen strip of a circuit. -/
def nielsenStrip (C : List (Op G)) : List (ℕ × ℕ) :=
  (List.range C.length).flatMap fun z => match C[z]? with
    | some op => gateTrans z op
    | none => []

/-- A multiplication circuit: inputs and product gates only. -/
def NoInv (C : List (Op G)) : Prop := ∀ op ∈ C, ∀ i, op ≠ .inv i

theorem nielsen_prefix (C : List (Op G)) (hwf : WellFormed C) (hC : NoInv C) :
    ∀ n ≤ C.length,
      runStrip ((List.range n).flatMap fun z => match C[z]? with
        | some op => gateTrans z op
        | none => []) (initRegs C) =
      fun k => if k < n then val id C k else initRegs C k := by
  intro n hn
  induction n with
  | zero => funext k; simp [runStrip]
  | succ n ih =>
    have hn' : n < C.length := hn
    rw [List.range_succ, List.flatMap_append, runStrip_append, ih (by omega)]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have hget : C[n]? = some (C[n]'hn') := List.getElem?_eq_getElem hn'
    rw [hget]
    have hval := val_of_lt id C hn'
    have hpre : ∀ i, i < n → val id (C.take n) i = val id C i := by
      intro i hi
      conv_rhs => rw [← List.take_append_drop n C]
      rw [val_append_of_lt _ _ _ (by simp; omega)]
    have hw := hwf n hn'
    cases hop : C[n]'hn' with
    | leaf a =>
      simp only [gateTrans, runStrip, List.foldl_nil]
      funext k
      by_cases hk : k < n
      · simp [hk, show k < n + 1 by omega]
      · by_cases hkn : k = n
        · subst hkn
          simp only [lt_irrefl, if_false, lt_add_one, if_true]
          rw [hval, hop]
          simp [initRegs, hget, hop, Op.step]
        · simp [hk, show ¬ k < n + 1 by omega]
    | mul x y =>
      rw [hop] at hw
      obtain ⟨hx, hy⟩ := hw
      simp only [gateTrans, runStrip, List.foldl_cons, List.foldl_nil, transvect]
      funext k
      by_cases hkn : k = n
      · subst hkn
        simp only [Function.update_self, lt_irrefl, if_false, lt_add_one, if_true]
        simp only [Function.update_of_ne (show y ≠ k by omega), if_pos hx, if_pos hy]
        rw [hval, hop]
        have h1 : initRegs C k = 1 := by simp [initRegs, hget, hop]
        rw [h1, one_mul]
        show _ = val id (C.take k) x * val id (C.take k) y
        rw [hpre x hx, hpre y hy]
      · rw [Function.update_of_ne hkn, Function.update_of_ne hkn]
        by_cases hk : k < n
        · simp [hk, show k < n + 1 by omega]
        · simp [hk, show ¬ k < n + 1 by omega]
    | inv i =>
      exact absurd hop (hC _ (List.getElem_mem hn') i)

/-- **Linear reversible embedding** (004f, Theorem 7.2). For every well-formed multiplication
circuit `C` over a group, the Nielsen strip has at most `2 s` transvections, each `g_i ← g_i g_j`
with `i ≠ j`, and after running it from the initial registers, register `k` holds the value of
node `k` for every `k < s`. -/
theorem nielsen_embedding (C : List (Op G)) (hwf : WellFormed C) (hC : NoInv C) :
    (nielsenStrip C).length ≤ 2 * C.length ∧
    (∀ p ∈ nielsenStrip C, p.1 ≠ p.2) ∧
    ∀ k < C.length, runStrip (nielsenStrip C) (initRegs C) k = val id C k := by
  refine ⟨?_, ?_, ?_⟩
  · unfold nielsenStrip
    rw [List.length_flatMap]
    have : ∀ z ∈ List.range C.length, (match C[z]? with
        | some op => gateTrans z op
        | none => []).length ≤ 2 := by
      intro z _
      rcases C[z]? with _ | op
      · simp
      · cases op <;> simp [gateTrans]
    calc (List.map (fun z => (match C[z]? with
          | some op => gateTrans z op
          | none => []).length) (List.range C.length)).sum
        ≤ (List.map (fun _ => 2) (List.range C.length)).sum :=
          List.sum_le_sum (fun z hz => by simpa using this z hz)
      _ = 2 * C.length := by simp [mul_comm]
  · intro p hp
    simp only [nielsenStrip, List.mem_flatMap, List.mem_range] at hp
    obtain ⟨z, hz, hp⟩ := hp
    have hget : C[z]? = some (C[z]'hz) := List.getElem?_eq_getElem hz
    rw [hget] at hp
    have hw := hwf z hz
    cases hop : C[z]'hz with
    | leaf a => rw [hop] at hp; simp [gateTrans] at hp
    | mul x y =>
      rw [hop] at hp hw
      simp only [gateTrans, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact Nat.ne_of_gt hw.1
      · exact Nat.ne_of_gt hw.2
    | inv i => rw [hop] at hp; simp [gateTrans] at hp
  · intro k hk
    have := nielsen_prefix C hwf hC C.length le_rfl
    rw [nielsenStrip, this]
    simp [hk]

end Nielsen

end GC.A5Programs
