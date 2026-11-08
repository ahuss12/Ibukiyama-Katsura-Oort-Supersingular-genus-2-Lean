/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.IKO.QuadraticCoefficients
import SupersingularCurves.IKO.CoefficientMatrix

/-!
# Uniform coefficient matrices for both IKO families

The formulas hold over every field, for every natural number in the
specified congruence classes. Their geometric interpretation requires
the separate Cartier and Jacobian compatibility theorems.
-/

set_option autoImplicit false
noncomputable section

namespace SupersingularCurves.IKO

open Polynomial Matrix

variable {K : Type*} [Field K]

private theorem coefficientPolynomial_eq_g (p : ℕ) (hp : 3 ≤ p)
    (hp6 : p % 6 = 1 ∨ p % 6 = 5) :
    (coefficientPolynomial ((p - 1) / 2) ((p + 1) / 6) : K[X]) = gPolynomial p := by
  have he : (p - 1) / 2 - (p + 1) / 6 = p / 3 := by omega
  simp only [coefficientPolynomial, gPolynomial, he]

private theorem coefficientPolynomial_eq_h (p : ℕ) (hp : 3 ≤ p)
    (hp2 : p % 2 = 1) :
    (coefficientPolynomial ((p - 1) / 2) ((p + 1) / 4) : K[X]) = hPolynomial p := by
  have he : (p - 1) / 2 - (p + 1) / 4 = p / 4 := by omega
  simp only [coefficientPolynomial, hPolynomial, he]

/-- Full family-(a) matrix in the first congruence class, for all parameters. -/
theorem coefficientMatrix_familyA_formula_one (p : ℕ) (hp : 3 ≤ p)
    (hp6 : p % 6 = 1) (t : K) :
    coefficientMatrix p (familyA t) =
      !![t ^ ((p - 1) / 6) * (gPolynomial p).eval t, 0;
         0, (gPolynomial p).eval t] := by
  have hd : (p + 1) / 6 ≤ (p - 1) / 2 := by omega
  have hs : (-1 : K) ^ ((p - 1) / 2 - (p + 1) / 6) = 1 := by
    rw [show (p - 1) / 2 - (p + 1) / 6 = 2 * (p / 6) by omega, pow_mul]
    simp
  have hh : (quadratic t ^ ((p - 1) / 2)).coeff ((2 * p - 2) / 3) =
      (gPolynomial p).eval t := by
    rw [show (2 * p - 2) / 3 = (p - 1) / 2 + (p + 1) / 6 by omega,
      coeff_quadratic_power_high t _ _ hd,
      coefficientPolynomial_eq_g p hp (Or.inl hp6), hs, one_mul]
  have hl : (quadratic t ^ ((p - 1) / 2)).coeff ((p - 1) / 3) =
      t ^ ((p - 1) / 6) * (gPolynomial p).eval t := by
    rw [show (p - 1) / 3 = (p - 1) / 2 - (p + 1) / 6 by omega,
      coeff_quadratic_power_low t _ _ hd,
      coefficientPolynomial_eq_g p hp (Or.inl hp6), hs, one_mul,
      show (p + 1) / 6 = (p - 1) / 6 by omega]
  rw [coefficientMatrix_familyA_mod_six_one p hp hp6, hh, hl]

/-- Full family-(a) matrix in the second congruence class. -/
theorem coefficientMatrix_familyA_formula_five (p : ℕ) (hp6 : p % 6 = 5) (t : K) :
    coefficientMatrix p (familyA t) =
      !![0, -(t ^ ((p + 1) / 6) * (gPolynomial p).eval t);
         -(gPolynomial p).eval t, 0] := by
  have hp : 3 ≤ p := by omega
  have hd : (p + 1) / 6 ≤ (p - 1) / 2 := by omega
  have hs : (-1 : K) ^ ((p - 1) / 2 - (p + 1) / 6) = -1 := by
    rw [show (p - 1) / 2 - (p + 1) / 6 = 2 * (p / 6) + 1 by omega,
      pow_add, pow_mul]
    simp
  have hh : (quadratic t ^ ((p - 1) / 2)).coeff ((2 * p - 1) / 3) =
      -(gPolynomial p).eval t := by
    rw [show (2 * p - 1) / 3 = (p - 1) / 2 + (p + 1) / 6 by omega,
      coeff_quadratic_power_high t _ _ hd,
      coefficientPolynomial_eq_g p hp (Or.inr hp6), hs, neg_one_mul]
  have hl : (quadratic t ^ ((p - 1) / 2)).coeff ((p - 2) / 3) =
      -(t ^ ((p + 1) / 6) * (gPolynomial p).eval t) := by
    rw [show (p - 2) / 3 = (p - 1) / 2 - (p + 1) / 6 by omega,
      coeff_quadratic_power_low t _ _ hd,
      coefficientPolynomial_eq_g p hp (Or.inr hp6), hs, neg_one_mul, mul_neg]
  rw [coefficientMatrix_familyA_mod_six_five p hp6, hh, hl]

/-- Full family-(b) matrix, including its characteristic-independent sign. -/
theorem coefficientMatrix_familyB_formula_one (p : ℕ) (hp : 3 ≤ p)
    (hp4 : p % 4 = 1) (t : K) :
    coefficientMatrix p (familyB t) =
      !![t ^ ((p + 1) / 4) * ((-1 : K) ^ (p / 4) * (hPolynomial p).eval t), 0;
         0, (-1 : K) ^ (p / 4) * (hPolynomial p).eval t] := by
  have hp2 : p % 2 = 1 := by omega
  have hd : (p + 1) / 4 ≤ (p - 1) / 2 := by omega
  have he : (p - 1) / 2 - (p + 1) / 4 = p / 4 := by omega
  have h00 : 2 ∣ p - 1 - (p - 1) / 2 := by omega
  have h01 : ¬2 ∣ p - 2 - (p - 1) / 2 := by omega
  have h10 : ¬2 ∣ 2 * p - 1 - (p - 1) / 2 := by omega
  have h11 : 2 ∣ 2 * p - 2 - (p - 1) / 2 := by omega
  have hlo : (p - 1 - (p - 1) / 2) / 2 = (p - 1) / 2 - (p + 1) / 4 := by omega
  have hhi : (2 * p - 2 - (p - 1) / 2) / 2 = (p - 1) / 2 + (p + 1) / 4 := by omega
  have hle0 : (p - 1) / 2 ≤ p - 2 := by omega
  have hle1 : (p - 1) / 2 ≤ p - 1 := by omega
  have hle2 : (p - 1) / 2 ≤ 2 * p - 1 := by omega
  have hle3 : (p - 1) / 2 ≤ 2 * p - 2 := by omega
  have hlow := coeff_quadratic_power_low t _ _ hd
  rw [coefficientPolynomial_eq_h p hp hp2, he] at hlow
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coefficientMatrix, coeff_familyB_power_general, h00, h01, h10, h11,
      hlo, hhi, hle0, hle1, hle2, hle3, hlow,
      coeff_quadratic_power_high t _ _ hd, coefficientPolynomial_eq_h p hp hp2, he]

/-- Family (b)'s off-diagonal case also covers p = 3. -/
theorem coefficientMatrix_familyB_formula_three (p : ℕ) (hp4 : p % 4 = 3) (t : K) :
    coefficientMatrix p (familyB t) =
      !![0, t ^ ((p + 1) / 4) * ((-1 : K) ^ (p / 4) * (hPolynomial p).eval t);
         (-1 : K) ^ (p / 4) * (hPolynomial p).eval t, 0] := by
  have hp : 3 ≤ p := by omega
  have hp2 : p % 2 = 1 := by omega
  have hd : (p + 1) / 4 ≤ (p - 1) / 2 := by omega
  have he : (p - 1) / 2 - (p + 1) / 4 = p / 4 := by omega
  have h00 : ¬2 ∣ p - 1 - (p - 1) / 2 := by omega
  have h01 : 2 ∣ p - 2 - (p - 1) / 2 := by omega
  have h10 : 2 ∣ 2 * p - 1 - (p - 1) / 2 := by omega
  have h11 : ¬2 ∣ 2 * p - 2 - (p - 1) / 2 := by omega
  have hlo : (p - 2 - (p - 1) / 2) / 2 = (p - 1) / 2 - (p + 1) / 4 := by omega
  have hhi : (2 * p - 1 - (p - 1) / 2) / 2 = (p - 1) / 2 + (p + 1) / 4 := by omega
  have hle0 : (p - 1) / 2 ≤ p - 2 := by omega
  have hle1 : (p - 1) / 2 ≤ p - 1 := by omega
  have hle2 : (p - 1) / 2 ≤ 2 * p - 1 := by omega
  have hle3 : (p - 1) / 2 ≤ 2 * p - 2 := by omega
  have hlow := coeff_quadratic_power_low t _ _ hd
  rw [coefficientPolynomial_eq_h p hp hp2, he] at hlow
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coefficientMatrix, coeff_familyB_power_general, h00, h01, h10, h11,
      hlo, hhi, hle0, hle1, hle2, hle3, hlow,
      coeff_quadratic_power_high t _ _ hd, coefficientPolynomial_eq_h p hp hp2, he]

end SupersingularCurves.IKO
