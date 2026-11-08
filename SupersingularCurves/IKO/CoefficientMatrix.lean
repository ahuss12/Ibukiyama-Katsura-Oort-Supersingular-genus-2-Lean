/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.IKO.Polynomials
import SupersingularCurves.IKO.Semilinear

/-!
# IKO coefficient matrices and initial exact examples

This defines the raw coefficient matrix M from equation (1.5). The
matrix of Cartier in the regular basis is M^(1/p), a separate geometric
identification. The examples below are exact identities over fields;
no numerical search is used as a proof.
-/

set_option autoImplicit false
noncomputable section

namespace SupersingularCurves.IKO

open Polynomial Matrix

variable {K : Type*} [Field K]

/-- The raw IKO matrix, before taking inverse Frobenius of its entries. -/
def coefficientMatrix (p : ℕ) (f : K[X]) : Matrix (Fin 2) (Fin 2) K :=
  !![(f ^ ((p - 1) / 2)).coeff (p - 1), (f ^ ((p - 1) / 2)).coeff (p - 2);
     (f ^ ((p - 1) / 2)).coeff (2 * p - 1), (f ^ ((p - 1) / 2)).coeff (2 * p - 2)]

/-- The diagonal pattern is uniform for p congruent to 1 modulo 6. -/
theorem coefficientMatrix_familyA_mod_six_one (p : ℕ) (hp : 3 ≤ p)
    (hp6 : p % 6 = 1) (t : K) :
    coefficientMatrix p (familyA t) =
      !![(quadratic t ^ ((p - 1) / 2)).coeff ((p - 1) / 3), 0;
         0, (quadratic t ^ ((p - 1) / 2)).coeff ((2 * p - 2) / 3)] := by
  have h00 : 3 ∣ p - 1 := by omega
  have h01 : ¬3 ∣ p - 2 := by omega
  have h10 : ¬3 ∣ 2 * p - 1 := by omega
  have h11 : 3 ∣ 2 * p - 2 := by omega
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coefficientMatrix, coeff_familyA_power, h00, h01, h10, h11]

/-- The off-diagonal pattern is uniform for p congruent to 5 modulo 6. -/
theorem coefficientMatrix_familyA_mod_six_five (p : ℕ) (hp6 : p % 6 = 5) (t : K) :
    coefficientMatrix p (familyA t) =
      !![0, (quadratic t ^ ((p - 1) / 2)).coeff ((p - 2) / 3);
         (quadratic t ^ ((p - 1) / 2)).coeff ((2 * p - 1) / 3), 0] := by
  have h00 : ¬3 ∣ p - 1 := by omega
  have h01 : 3 ∣ p - 2 := by omega
  have h10 : 3 ∣ 2 * p - 1 := by omega
  have h11 : ¬3 ∣ 2 * p - 2 := by omega
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coefficientMatrix, coeff_familyA_power, h00, h01, h10, h11]

/-- The p = 5 specialization of IKO's family-(a) matrix formula. -/
theorem coefficientMatrix_familyA_five (t : K) :
    coefficientMatrix 5 (familyA t) =
      !![0, -(gPolynomial 5).eval t * t; -(gPolynomial 5).eval t, 0] := by
  have hf : familyA t ^ 2 =
      X ^ 12 - C (2 * (1 + t)) * X ^ 9 + C (t ^ 2 + 4 * t + 1) * X ^ 6 -
        C (2 * t * (1 + t)) * X ^ 3 + C (t ^ 2) := by
    simp only [familyA, map_add, map_mul, map_pow, map_one, map_ofNat]
    ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [coefficientMatrix, show (5 - 1) / 2 = (2 : ℕ) by decide, hf,
      coeff_add, coeff_sub, coeff_C_mul, coeff_C, coeff_X_pow] <;>
    norm_num [gPolynomial_five, Polynomial.C_ofNat] <;> ring

/-- The p = 7 specialization, including the scalar on the first diagonal entry. -/
theorem coefficientMatrix_familyA_seven (t : K) :
    coefficientMatrix 7 (familyA t) =
      !![t * (gPolynomial 7).eval t, 0; 0, (gPolynomial 7).eval t] := by
  have hf : familyA t ^ 3 =
      X ^ 18 - C (3 + 3 * t) * X ^ 15 + C (3 + 9 * t + 3 * t ^ 2) * X ^ 12 -
        C (1 + 9 * t + 9 * t ^ 2 + t ^ 3) * X ^ 9 +
        C (3 * t + 9 * t ^ 2 + 3 * t ^ 3) * X ^ 6 -
        C (3 * t ^ 2 + 3 * t ^ 3) * X ^ 3 + C (t ^ 3) := by
    simp only [familyA, map_add, map_mul, map_pow, map_one, map_ofNat]
    ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [coefficientMatrix, show (7 - 1) / 2 = (3 : ℕ) by decide, hf,
      coeff_add, coeff_sub, coeff_C_mul, coeff_C, coeff_X_pow] <;>
    norm_num [gPolynomial_seven, Polynomial.C_ofNat] <;> ring

theorem coefficientMatrix_familyA_five_zero_iff (t : K) :
    coefficientMatrix 5 (familyA t) = 0 ↔ (gPolynomial 5).eval t = 0 := by
  rw [coefficientMatrix_familyA_five]
  constructor
  · intro h
    have he := congrFun (congrFun h 1) 0
    simpa using he
  · intro h
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h]

theorem coefficientMatrix_familyA_seven_zero_iff (t : K) :
    coefficientMatrix 7 (familyA t) = 0 ↔ (gPolynomial 7).eval t = 0 := by
  rw [coefficientMatrix_familyA_seven]
  constructor
  · intro h
    have he := congrFun (congrFun h 1) 1
    simpa using he
  · intro h
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h]

/-- Family (b) includes the characteristic-three edge case. -/
theorem coefficientMatrix_familyB_three (t : K) :
    coefficientMatrix 3 (familyB t) = !![0, t; 1, 0] := by
  have hf : familyB t = X ^ 5 - C (1 + t) * X ^ 3 + C t * X := by
    simp only [familyB, map_add, map_one]
    ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [coefficientMatrix, show (3 - 1) / 2 = (1 : ℕ) by decide,
      pow_one, hf, coeff_add, coeff_sub, coeff_C_mul, coeff_C, coeff_X_pow] <;>
    norm_num [coeff_X]

/-- IKO family-(b) matrix at p = 5, with its sign and parameter factor. -/
theorem coefficientMatrix_familyB_five (t : K) :
    coefficientMatrix 5 (familyB t) =
      !![-(hPolynomial 5).eval t * t, 0; 0, -(hPolynomial 5).eval t] := by
  have hf : familyB t ^ 2 =
      X ^ 10 - C (2 * (1 + t)) * X ^ 8 + C (t ^ 2 + 4 * t + 1) * X ^ 6 -
        C (2 * t * (1 + t)) * X ^ 4 + C (t ^ 2) * X ^ 2 := by
    simp only [familyB, map_add, map_mul, map_pow, map_one, map_ofNat]
    ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [coefficientMatrix, show (5 - 1) / 2 = (2 : ℕ) by decide, hf,
      coeff_add, coeff_sub, coeff_C_mul, coeff_C, coeff_X_pow] <;>
    norm_num [hPolynomial_five, Polynomial.C_ofNat] <;> ring

theorem coefficientMatrix_familyB_five_zero_iff (t : K) :
    coefficientMatrix 5 (familyB t) = 0 ↔ (hPolynomial 5).eval t = 0 := by
  rw [coefficientMatrix_familyB_five]
  constructor
  · intro h
    have he := congrFun (congrFun h 1) 1
    simpa using he
  · intro h
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h]

/-- The coefficient matrix of the class-(6) example at p = 3 is nonzero nilpotent. -/
theorem coefficientMatrix_x_fifth_sub_one_three :
    coefficientMatrix 3 (X ^ 5 - 1 : K[X]) = !![0, 0; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [coefficientMatrix, coeff_one]

/-- Algebraic separation of the two criteria appearing in Lemma 1.1. -/
theorem x_fifth_sub_one_three_matrix_distinction (σ : K ≃+* K) :
    let M := coefficientMatrix 3 (X ^ 5 - 1 : K[X])
    M ≠ 0 ∧ twistMatrix σ M * M = 0 := by
  dsimp
  rw [coefficientMatrix_x_fifth_sub_one_three]
  obtain ⟨hne, hz⟩ := nonzero_square_zero_example σ
  exact ⟨hne, (semilinearAction_square_zero_iff σ _).mp hz⟩

end SupersingularCurves.IKO
