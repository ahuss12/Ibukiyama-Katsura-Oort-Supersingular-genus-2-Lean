/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import Mathlib

/-!
# Polynomial data for IKO Section 1

Definitions 1.6 and 1.7 are implemented with natural-number division for
the floor functions. The curve equations here are branch polynomials;
they are not definitions of smooth projective curves or supersingularity.
-/

set_option autoImplicit false
noncomputable section

namespace SupersingularCurves.IKO

open Polynomial Finset

variable {K : Type*} [Field K]

def quadratic (t : K) : K[X] := (X - 1) * (X - C t)

/-- The branch polynomial of IKO family (a). -/
def familyA (t : K) : K[X] := (X ^ 3 - 1) * (X ^ 3 - C t)

/-- The branch polynomial of IKO family (b). -/
def familyB (t : K) : K[X] := X * (X ^ 2 - 1) * (X ^ 2 - C t)

/-- IKO Definition 1.6, with coefficients in the given field. -/
def gPolynomial (p : ℕ) : K[X] :=
  ∑ j ∈ range (p / 3 + 1),
    C (((p - 1) / 2).choose ((p + 1) / 6 + j) : K) *
      C (((p - 1) / 2).choose j : K) * X ^ j

/-- IKO Definition 1.7, with coefficients in the given field. -/
def hPolynomial (p : ℕ) : K[X] :=
  ∑ j ∈ range (p / 4 + 1),
    C (((p - 1) / 2).choose ((p + 1) / 4 + j) : K) *
      C (((p - 1) / 2).choose j : K) * X ^ j

theorem familyA_power_eq_expand (t : K) (n : ℕ) :
    familyA t ^ n = expand K 3 (quadratic t ^ n) := by
  simp [familyA, quadratic]

/-- All coefficients outside multiples of three vanish, uniformly in n. -/
theorem coeff_familyA_power (t : K) (n i : ℕ) :
    (familyA t ^ n).coeff i =
      if 3 ∣ i then (quadratic t ^ n).coeff (i / 3) else 0 := by
  rw [familyA_power_eq_expand, coeff_expand (by decide : 0 < 3)]

theorem coeff_familyA_power_of_not_dvd (t : K) (n i : ℕ) (hi : ¬ 3 ∣ i) :
    (familyA t ^ n).coeff i = 0 := by
  simp [coeff_familyA_power, hi]

theorem familyB_power_eq_expand (t : K) (n : ℕ) :
    familyB t ^ n = expand K 2 (quadratic t ^ n) * X ^ n := by
  simp [familyB, quadratic, mul_pow]
  ring

/-- The nonzero candidate coefficients in family (b) reduce to a quadratic. -/
theorem coeff_familyB_power (t : K) (n i : ℕ) :
    (familyB t ^ n).coeff (2 * i + n) = (quadratic t ^ n).coeff i := by
  rw [familyB_power_eq_expand, coeff_mul_X_pow,
    coeff_expand_mul' (by decide : 0 < 2)]

theorem coeff_familyB_power_general (t : K) (n i : ℕ) :
    (familyB t ^ n).coeff i =
      if n ≤ i then
        if 2 ∣ i - n then (quadratic t ^ n).coeff ((i - n) / 2) else 0
      else 0 := by
  rw [familyB_power_eq_expand, coeff_mul_X_pow']
  simp only [coeff_expand (by decide : 0 < 2)]

theorem coprime_X_pow_sub_C (n : ℕ) (a b : K) (hab : a ≠ b) :
    IsCoprime (X ^ n - C a) (X ^ n - C b) := by
  refine ⟨C ((b - a)⁻¹), -C ((b - a)⁻¹), ?_⟩
  calc
    _ = C ((b - a)⁻¹ * (b - a)) := by
      simp only [map_mul, map_sub]
      ring
    _ = 1 := by rw [inv_mul_cancel₀ (sub_ne_zero.mpr hab.symm), map_one]

/-- The admissible family-(a) branch polynomial has no repeated roots. -/
theorem familyA_separable (t : K) (h3 : (3 : K) ≠ 0)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) : (familyA t).Separable := by
  have hleft : (X ^ 3 - 1 : K[X]).Separable := by
    simpa using separable_X_pow_sub_C (1 : K) h3 one_ne_zero
  exact hleft.mul (separable_X_pow_sub_C t h3 ht0)
    (by simpa using coprime_X_pow_sub_C 3 (1 : K) t ht1.symm)

theorem gPolynomial_five : (gPolynomial 5 : K[X]) = C 2 + C 2 * X := by
  norm_num [gPolynomial, Finset.sum_range_succ, Polynomial.C_ofNat]

theorem gPolynomial_seven :
    (gPolynomial 7 : K[X]) = C 3 + C 9 * X + C 3 * X ^ 2 := by
  norm_num [gPolynomial, Finset.sum_range_succ, Polynomial.C_ofNat]

theorem hPolynomial_three : (hPolynomial 3 : K[X]) = 1 := by
  norm_num [hPolynomial, Finset.sum_range_succ]

theorem hPolynomial_five : (hPolynomial 5 : K[X]) = C 2 + C 2 * X := by
  norm_num [hPolynomial, Finset.sum_range_succ, Polynomial.C_ofNat]

end SupersingularCurves.IKO
