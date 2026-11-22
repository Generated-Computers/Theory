import GC.GroupTheory.A5Programs.Collisions
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Prime.Basic

/-!
# Reversible power updates and the Fibonacci update (manuscript 004c, Section 3)

* `pow_bijective_iff`: `x ↦ x^a` is a permutation of `A₅` iff `gcd(a, 30) = 1` (Lemma 3.5).
* `unitPower_R_bijective_iff`, `unitPower_L_bijective_iff`: `(x, y) ↦ (x, x^a y^b)` is a
  permutation of `A₅²` iff `gcd(b, 30) = 1`, and `(x, y) ↦ (x^a y^b, y)` iff `gcd(a, 30) = 1`
  (Theorem 3.6).
* `fib_update_inverse`: the update `(x, y) ↦ (x y, x)` is inverted by `(u, v) ↦ (v, v⁻¹ u)`
  (Corollary 3.3).
-/

namespace GC.A5Programs

open Equiv

set_option maxRecDepth 100000 in
theorem A5list_pow30 : ∀ g ∈ A5list, g ^ 30 = 1 := by decide +kernel

/-- `A₅` has exponent dividing 30. -/
theorem A5_pow30 (x : A5) : x ^ 30 = 1 := by
  apply Subtype.ext
  simp only [Subgroup.coe_pow, OneMemClass.coe_one]
  exact A5list_pow30 _ ((mem_A5list_iff _).2 x.2)

theorem A5_pow_inj_of_coprime {a : ℕ} (ha : Nat.Coprime a 30) {x y : A5} (h : x ^ a = y ^ a) :
    x = y := by
  have key : ∀ z : A5, z = (z ^ a) ^ (Nat.gcdA a 30) := by
    intro z
    have hg : ((Nat.gcd a 30 : ℕ) : ℤ) = a * Nat.gcdA a 30 + 30 * Nat.gcdB a 30 :=
      Nat.gcd_eq_gcd_ab a 30
    rw [ha.gcd_eq_one, Nat.cast_one] at hg
    calc z = z ^ (1 : ℤ) := (zpow_one z).symm
      _ = z ^ ((a : ℤ) * Nat.gcdA a 30 + 30 * Nat.gcdB a 30) := by rw [← hg]
      _ = (z ^ a) ^ (Nat.gcdA a 30) * (z ^ (30 : ℕ)) ^ (Nat.gcdB a 30) := by
        rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, show ((30 : ℤ)) = ((30 : ℕ) : ℤ) from
          rfl, zpow_natCast]
      _ = (z ^ a) ^ (Nat.gcdA a 30) := by rw [A5_pow30, one_zpow, mul_one]
  rw [key x, key y, h]

/-- An element of order `r` for each prime `r ∣ 30`. -/
theorem A5_exists_order (r : ℕ) (hr : r = 2 ∨ r = 3 ∨ r = 5) : ∃ z : A5, z ≠ 1 ∧ z ^ r = 1 := by
  have h2 : (mk5 ![1,0,3,2,4] ![1,0,3,2,4]) ∈ alternatingGroup (Fin 5) :=
    (mem_A5list_iff _).1 (by decide)
  have h3 : qA ∈ alternatingGroup (Fin 5) := (mem_A5list_iff _).1 (by decide)
  have h5 : pA ∈ alternatingGroup (Fin 5) := (mem_A5list_iff _).1 (by decide)
  rcases hr with rfl | rfl | rfl
  · refine ⟨⟨_, h2⟩, fun h => ?_, Subtype.ext ?_⟩
    · have := congrArg Subtype.val h; simp only [OneMemClass.coe_one] at this; revert this; decide
    · simp only [Subgroup.coe_pow, OneMemClass.coe_one]; decide
  · refine ⟨⟨_, h3⟩, fun h => ?_, Subtype.ext ?_⟩
    · have := congrArg Subtype.val h; simp only [OneMemClass.coe_one] at this; revert this; decide
    · simp only [Subgroup.coe_pow, OneMemClass.coe_one]; decide
  · refine ⟨⟨_, h5⟩, fun h => ?_, Subtype.ext ?_⟩
    · have := congrArg Subtype.val h; simp only [OneMemClass.coe_one] at this; revert this; decide
    · simp only [Subgroup.coe_pow, OneMemClass.coe_one]; decide

theorem not_coprime_30 {a : ℕ} (ha : ¬ Nat.Coprime a 30) : ∃ r, (r = 2 ∨ r = 3 ∨ r = 5) ∧ r ∣ a := by
  rw [show (30 : ℕ) = 2 * (3 * 5) from rfl, Nat.coprime_mul_iff_right,
    Nat.coprime_mul_iff_right] at ha
  have p2 := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two (n := a))
  have p3 := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three (n := a))
  have p5 := (Nat.Prime.coprime_iff_not_dvd Nat.prime_five (n := a))
  by_contra hcon
  push Not at hcon
  apply ha
  refine ⟨?_, ?_, ?_⟩
  · exact (p2.2 (hcon 2 (Or.inl rfl))).symm
  · exact (p3.2 (hcon 3 (Or.inr (Or.inl rfl)))).symm
  · exact (p5.2 (hcon 5 (Or.inr (Or.inr rfl)))).symm

theorem A5_pow_not_inj {a : ℕ} (ha : ¬ Nat.Coprime a 30) :
    ∃ z : A5, z ≠ 1 ∧ z ^ a = (1 : A5) ^ a := by
  obtain ⟨r, hr, m, rfl⟩ := not_coprime_30 ha
  obtain ⟨z, hz, hzr⟩ := A5_exists_order r hr
  exact ⟨z, hz, by rw [pow_mul, hzr, one_pow, one_pow]⟩

/-- **Power permutations** (004c, Lemma 3.5): `x ↦ x^a` is a permutation of `A₅` exactly when
`a` is prime to 30. -/
theorem pow_bijective_iff (a : ℕ) : Function.Bijective (fun x : A5 => x ^ a) ↔ Nat.Coprime a 30 := by
  constructor
  · intro hb
    by_contra ha
    obtain ⟨z, hz, h⟩ := A5_pow_not_inj ha
    exact hz (hb.1 h)
  · intro ha
    exact Finite.injective_iff_bijective.1 fun x y h => A5_pow_inj_of_coprime ha h

/-- **Unit-power reversibility** (004c, Theorem 3.6), right form. -/
theorem unitPower_R_bijective_iff (a b : ℕ) :
    Function.Bijective (fun p : A5 × A5 => (p.1, p.1 ^ a * p.2 ^ b)) ↔ Nat.Coprime b 30 := by
  constructor
  · intro hb
    by_contra hc
    obtain ⟨z, hz, h⟩ := A5_pow_not_inj hc
    have := hb.1 (a₁ := (1, z)) (a₂ := (1, 1)) (by simp [h])
    exact hz (Prod.ext_iff.1 this).2
  · intro hc
    refine Finite.injective_iff_bijective.1 fun p q h => ?_
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    rw [h1, mul_right_inj] at h2
    exact Prod.ext h1 (A5_pow_inj_of_coprime hc h2)

/-- **Unit-power reversibility** (004c, Theorem 3.6), left form. -/
theorem unitPower_L_bijective_iff (a b : ℕ) :
    Function.Bijective (fun p : A5 × A5 => (p.1 ^ a * p.2 ^ b, p.2)) ↔ Nat.Coprime a 30 := by
  constructor
  · intro hb
    by_contra hc
    obtain ⟨z, hz, h⟩ := A5_pow_not_inj hc
    have := hb.1 (a₁ := (z, 1)) (a₂ := (1, 1)) (by simp [h])
    exact hz (Prod.ext_iff.1 this).1
  · intro hc
    refine Finite.injective_iff_bijective.1 fun p q h => ?_
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    rw [h2, mul_left_inj] at h1
    exact Prod.ext (A5_pow_inj_of_coprime hc h1) h2

/-- **Noncommutative Fibonacci update** (004c, Corollary 3.3): `T(x, y) = (x y, x)` is a
bijection of `G²` with inverse `(u, v) ↦ (v, v⁻¹ u)`, for every group `G`. -/
theorem fib_update_inverse {G : Type*} [Group G] :
    Function.LeftInverse (fun p : G × G => (p.2, p.2⁻¹ * p.1)) (fun p : G × G => (p.1 * p.2, p.1)) ∧
    Function.RightInverse (fun p : G × G => (p.2, p.2⁻¹ * p.1))
      (fun p : G × G => (p.1 * p.2, p.1)) :=
  ⟨fun p => by simp, fun p => by simp⟩

end GC.A5Programs
