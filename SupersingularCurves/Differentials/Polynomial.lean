/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Differentials.Monomials
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Tactic.FieldSimp

/-!
# Polynomial coefficients of the actual Cartier operator

We compute the previously constructed Cartier operator on actual Kähler
differentials. For a cubic relation y²=f(x), the coefficient of x^(p-1)
in f^((p-1)/2) gives its action on dx/y. No coefficient condition is used
as a definition of supersingularity. Regularity and the geometric elliptic
criterion are separate statements.

Reference: Achter--Howe, Hasse--Witt and Cartier--Manin matrices, §3.1.
https://www.math.colostate.edu/~achter/math/hwcm0618.pdf
-/

set_option autoImplicit false
noncomputable section

namespace SupersingularCurves.Differentials

open AlgebraicCurve KaehlerDifferential Polynomial Finset

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
  [PerfectField K] [IsCurveOver K F]
  (p : ℕ) [Fact p.Prime] [CharP K p]
  (x : F) [FiniteDimensional (IntermediateField.adjoin K {x}) F]

/-- The coefficient definition does not assert any geometric criterion. -/
def hasseCoefficient (p : ℕ) (f : K[X]) : K :=
  (f ^ ((p - 1) / 2)).coeff (p - 1)

/-- Only monomials whose exponent is p-1 modulo p survive Cartier. -/
theorem cartier_monomial (n : ℕ) :
    cartier p x (x ^ n • D K F x) =
      if n % p = p - 1 then x ^ (n / p) • D K F x else 0 := by
  split_ifs with hn
  · exact cartier_monomial_exceptional p x x n hn
  · exact cartier_monomial_other p x x n hn

/-- Polynomial coefficient extraction, including the inverse Frobenius twist. -/
theorem cartier_polynomial_sum (q : K[X]) (N : ℕ) (hN : q.natDegree < N) :
    cartier p x (aeval x q • D K F x) =
      ∑ n ∈ range N,
        if n % p = p - 1 then
          (frobeniusEquiv K p).symm (q.coeff n) • (x ^ (n / p) • D K F x)
        else 0 := by
  classical
  rw [aeval_eq_sum_range' hN x, Finset.sum_smul, map_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [smul_assoc, cartier_smul, cartier_monomial]
  split_ifs <;> simp

/-- A degree bound leaves just the coefficient indexed by p-1. -/
theorem cartier_polynomial_low_degree (q : K[X]) (hq : q.natDegree < 2 * p - 1) :
    cartier p x (aeval x q • D K F x) =
      (frobeniusEquiv K p).symm (q.coeff (p - 1)) • D K F x := by
  classical
  have hp := (Fact.out : p.Prime).two_le
  rw [cartier_polynomial_sum p x q (2 * p - 1) hq]
  rw [Finset.sum_eq_single (p - 1)]
  · simp [Nat.mod_eq_of_lt (show p - 1 < p by omega),
      Nat.div_eq_of_lt (show p - 1 < p by omega)]
  · intro n hn hne
    have hn' : n < 2 * p - 1 := mem_range.mp hn
    have hm : n % p ≠ p - 1 := by
      intro hm
      by_cases hnp : n < p
      · rw [Nat.mod_eq_of_lt hnp] at hm
        exact hne hm
      · have hnp' : p ≤ n := by omega
        rw [Nat.mod_eq_sub_mod hnp', Nat.mod_eq_of_lt (show n - p < p by omega)] at hm
        omega
    simp [hm]
  · intro hnot
    exact False.elim (hnot (mem_range.mpr (by omega)))

omit [PerfectField K] [CharP K p] in
/-- The cubic bound is sufficient for the single-coefficient calculation. -/
theorem natDegree_half_power_lt (hpodd : p % 2 = 1) (f : K[X])
    (hf : f.natDegree ≤ 3) : (f ^ ((p - 1) / 2)).natDegree < 2 * p - 1 := by
  have hp := (Fact.out : p.Prime).two_le
  rw [Polynomial.natDegree_pow]
  have h := Nat.mul_le_mul_left ((p - 1) / 2) hf
  omega

omit [PerfectField K] [IsCurveOver K F] [CharP K p]
  [FiniteDimensional (IntermediateField.adjoin K {x}) F] in
/-- Express dx/y with a p-th-power denominator, using the actual curve equation. -/
theorem differential_div_eq (hpodd : p % 2 = 1) (f : K[X]) (y : F)
    (hy : y ^ 2 = aeval x f) (hy0 : y ≠ 0) :
    y⁻¹ • D K F x = y⁻¹ ^ p • (aeval x (f ^ ((p - 1) / 2)) • D K F x) := by
  have hp := (Fact.out : p.Prime).two_le
  have he : 2 * ((p - 1) / 2) = p - 1 := by omega
  rw [smul_smul, map_pow, ← hy, ← pow_mul, he, inv_pow]
  congr 1
  field_simp
  rw [← pow_succ']
  congr 1
  omega

/-- The elliptic coefficient formula is a theorem about the old Cartier map. -/
theorem cartier_dx_div_y (hpodd : p % 2 = 1) (f : K[X]) (hf : f.natDegree ≤ 3)
    (y : F) (hy : y ^ 2 = aeval x f) (hy0 : y ≠ 0) :
    cartier p x (y⁻¹ • D K F x) =
      (frobeniusEquiv K p).symm (hasseCoefficient p f) • (y⁻¹ • D K F x) := by
  calc
    _ = cartier p x (y⁻¹ ^ p •
        (aeval x (f ^ ((p - 1) / 2)) • D K F x)) := by
          rw [← differential_div_eq p x hpodd f y hy hy0]
    _ = y⁻¹ • ((frobeniusEquiv K p).symm (hasseCoefficient p f) • D K F x) := by
      rw [cartier_pow_smul, cartier_polynomial_low_degree p x _
        (natDegree_half_power_lt (K := K) p hpodd f hf)]
      rfl
    _ = _ := smul_comm _ _ _

/-- A nonzero differential is necessary for the converse coefficient test. -/
theorem cartier_dx_div_y_eq_zero_iff (hpodd : p % 2 = 1)
    (f : K[X]) (hf : f.natDegree ≤ 3) (y : F)
    (hy : y ^ 2 = aeval x f) (hy0 : y ≠ 0) (hdx : D K F x ≠ 0) :
    cartier p x (y⁻¹ • D K F x) = 0 ↔ hasseCoefficient p f = 0 := by
  rw [cartier_dx_div_y p x hpodd f hf y hy hy0, smul_eq_zero]
  have hω : y⁻¹ • D K F x ≠ 0 := smul_ne_zero (inv_ne_zero hy0) hdx
  simp [hω]

end SupersingularCurves.Differentials
