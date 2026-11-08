/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Differentials.Polynomial

/-!
# The two coefficient formulas for hyperelliptic differentials

These statements concern the constructed Cartier operator on actual Kähler
differentials in a function field satisfying y² = f(x). They do not assume
the Cartier formulas, or assert that the two forms are a basis of all regular
differentials. The latter requires a separate smooth-model and regularity proof.
-/

set_option autoImplicit false
noncomputable section

namespace SupersingularCurves.Differentials

open AlgebraicCurve KaehlerDifferential Polynomial Finset

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
  [PerfectField K] [IsCurveOver K F]
  (p : ℕ) [Fact p.Prime] [CharP K p]
  (x : F) [FiniteDimensional (IntermediateField.adjoin K {x}) F]

/-- Below degree 3p-1 exactly two monomials can survive Cartier. -/
theorem cartier_polynomial_two_coefficients (q : K[X])
    (hq : q.natDegree < 3 * p - 1) :
    cartier p x (aeval x q • D K F x) =
      (frobeniusEquiv K p).symm (q.coeff (p - 1)) • D K F x +
      (frobeniusEquiv K p).symm (q.coeff (2 * p - 1)) • (x • D K F x) := by
  classical
  have hp := (Fact.out : p.Prime).two_le
  have hplt : p - 1 < p := by omega
  have htwo : 2 * p - 1 = p + (p - 1) := by omega
  rw [cartier_polynomial_sum p x q (3 * p - 1) hq]
  let term := fun n => if n % p = p - 1 then
    (frobeniusEquiv K p).symm (q.coeff n) • (x ^ (n / p) • D K F x) else 0
  change ∑ n ∈ range (3 * p - 1), term n = _
  have hs : ({p - 1, 2 * p - 1} : Finset ℕ) ⊆ range (3 * p - 1) := by
    intro n hn
    simp only [mem_insert, mem_singleton] at hn
    rcases hn with rfl | rfl <;> exact mem_range.mpr (by omega)
  have hz : ∀ n ∈ range (3 * p - 1), n ∉ ({p - 1, 2 * p - 1} : Finset ℕ) →
      term n = 0 := by
    intro n hn hnot
    have hn' := mem_range.mp hn
    have hm : n % p ≠ p - 1 := by
      intro hm
      have hne : n ≠ p - 1 ∧ n ≠ 2 * p - 1 := by simpa using hnot
      by_cases hn1 : n < p
      · rw [Nat.mod_eq_of_lt hn1] at hm
        exact hne.1 hm
      · rw [Nat.mod_eq_sub_mod (show p ≤ n by omega)] at hm
        by_cases hn2 : n - p < p
        · rw [Nat.mod_eq_of_lt hn2] at hm
          omega
        · rw [Nat.mod_eq_sub_mod (show p ≤ n - p by omega),
            Nat.mod_eq_of_lt (show n - p - p < p by omega)] at hm
          omega
    simp [term, hm]
  rw [← Finset.sum_subset hs hz, Finset.sum_pair (show p - 1 ≠ 2 * p - 1 by omega)]
  simp [term, htwo, Nat.mod_eq_of_lt hplt, Nat.div_eq_of_lt hplt,
    Nat.add_div_left _ (show 0 < p by omega)]

omit [PerfectField K] [CharP K p] in
/-- Degree at most six gives the two-coefficient bound. -/
theorem natDegree_half_power_two_coefficients (hpodd : p % 2 = 1) (f : K[X])
    (hf : f.natDegree ≤ 6) : (f ^ ((p - 1) / 2)).natDegree < 3 * p - 1 := by
  have hp := (Fact.out : p.Prime).two_le
  rw [Polynomial.natDegree_pow]
  have h := Nat.mul_le_mul_left ((p - 1) / 2) hf
  omega

omit [PerfectField K] [CharP K p] in
/-- Multiplication by X still leaves only two surviving coefficients. -/
theorem natDegree_X_half_power_two_coefficients (hpodd : p % 2 = 1) (f : K[X])
    (hf : f.natDegree ≤ 6) : (X * f ^ ((p - 1) / 2)).natDegree < 3 * p - 1 := by
  have hp := (Fact.out : p.Prime).two_le
  have hdeg := Polynomial.natDegree_mul_le (p := (X : K[X])) (q := f ^ ((p - 1) / 2))
  simp only [natDegree_X, natDegree_pow] at hdeg
  have h := Nat.mul_le_mul_left ((p - 1) / 2) hf
  omega

/-- Cartier on dx/y, with both coefficients and their inverse Frobenius twists. -/
theorem cartier_dx_div_y_two_coefficients (hpodd : p % 2 = 1) (f : K[X])
    (hf : f.natDegree ≤ 6) (y : F) (hy : y ^ 2 = aeval x f) (hy0 : y ≠ 0) :
    cartier p x (y⁻¹ • D K F x) =
      (frobeniusEquiv K p).symm ((f ^ ((p - 1) / 2)).coeff (p - 1)) •
        (y⁻¹ • D K F x) +
      (frobeniusEquiv K p).symm ((f ^ ((p - 1) / 2)).coeff (2 * p - 1)) •
        (x • (y⁻¹ • D K F x)) := by
  calc
    _ = cartier p x (y⁻¹ ^ p •
        (aeval x (f ^ ((p - 1) / 2)) • D K F x)) := by
      rw [← differential_div_eq p x hpodd f y hy hy0]
    _ = y⁻¹ • ((frobeniusEquiv K p).symm ((f ^ ((p - 1) / 2)).coeff (p - 1)) •
          D K F x +
        (frobeniusEquiv K p).symm ((f ^ ((p - 1) / 2)).coeff (2 * p - 1)) •
          (x • D K F x)) := by
      rw [cartier_pow_smul, cartier_polynomial_two_coefficients p x _
        (natDegree_half_power_two_coefficients (K := K) p hpodd f hf)]
    _ = _ := by rw [smul_add, smul_comm (y⁻¹), smul_comm (y⁻¹), smul_comm (y⁻¹)]

/-- Cartier on x dx/y: multiplication by X shifts both coefficient indices. -/
theorem cartier_x_dx_div_y_two_coefficients (hpodd : p % 2 = 1) (f : K[X])
    (hf : f.natDegree ≤ 6) (y : F) (hy : y ^ 2 = aeval x f) (hy0 : y ≠ 0) :
    cartier p x (x • (y⁻¹ • D K F x)) =
      (frobeniusEquiv K p).symm ((f ^ ((p - 1) / 2)).coeff (p - 2)) •
        (y⁻¹ • D K F x) +
      (frobeniusEquiv K p).symm ((f ^ ((p - 1) / 2)).coeff (2 * p - 2)) •
        (x • (y⁻¹ • D K F x)) := by
  have hp := (Fact.out : p.Prime).two_le
  have hinput : x • (y⁻¹ • D K F x) =
      y⁻¹ ^ p • (aeval x (X * f ^ ((p - 1) / 2)) • D K F x) := by
    rw [differential_div_eq p x hpodd f y hy hy0, smul_comm x, map_mul, aeval_X,
      mul_smul]
  conv_lhs => rw [hinput]
  rw [cartier_pow_smul, cartier_polynomial_two_coefficients p x _
    (natDegree_X_half_power_two_coefficients (K := K) p hpodd f hf)]
  have h1 : p - 1 = (p - 2) + 1 := by omega
  have h2 : 2 * p - 1 = (2 * p - 2) + 1 := by omega
  rw [h1, h2, coeff_X_mul, coeff_X_mul, smul_add,
    smul_comm (y⁻¹), smul_comm (y⁻¹), smul_comm (y⁻¹)]

end SupersingularCurves.Differentials
