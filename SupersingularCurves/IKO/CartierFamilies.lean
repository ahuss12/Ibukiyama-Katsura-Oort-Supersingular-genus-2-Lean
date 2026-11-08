/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.IKO.CartierCompatibility

/-!
# The IKO root criteria on actual rational differentials

These are consequences for the constructed Cartier operator on the span
of dx/y and x dx/y. Each curve equation and the coordinate hypotheses
are explicit. The global regular-basis and Jacobian bridges remain separate.
-/

set_option autoImplicit false
noncomputable section

namespace SupersingularCurves.IKO

open AlgebraicCurve KaehlerDifferential Polynomial
open SupersingularCurves.Differentials

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem natDegree_familyA_le (t : K) : (familyA t).natDegree ≤ 6 := by
  unfold familyA
  compute_degree

theorem natDegree_familyB_le (t : K) : (familyB t).natDegree ≤ 6 := by
  unfold familyB
  compute_degree
  norm_num

variable [PerfectField K] [IsCurveOver K F]
  (p : ℕ) [Fact p.Prime] [CharP K p]
  (x : F) [FiniteDimensional (IntermediateField.adjoin K {x}) F]

/-- Family (a): Cartier vanishes on the two-form span exactly at roots of g. -/
theorem familyA_cartier_zero_iff (hp5 : 5 ≤ p) (t : K) (y : F)
    (hy : y ^ 2 = aeval x (familyA t)) (hy0 : y ≠ 0)
    (htr : Transcendental K x) (hdx : D K F x ≠ 0) :
    (∀ v : Fin 2 → K, cartier p x (differentialCombination x y v) = 0) ↔
      (gPolynomial p).eval t = 0 := by
  have hp : p.Prime := Fact.out
  have hodd := hp.mod_two_eq_one_iff_ne_two.mpr (show p ≠ 2 by omega)
  rw [cartier_differentialSpan_zero_iff p x hodd _ (natDegree_familyA_le t)
    y hy hy0 htr hdx]
  exact coefficientMatrix_familyA_zero_iff p hp hp5 t

/-- Family (b): the analogous criterion, including characteristic three. -/
theorem familyB_cartier_zero_iff (hp3 : 3 ≤ p) (t : K) (y : F)
    (hy : y ^ 2 = aeval x (familyB t)) (hy0 : y ≠ 0)
    (htr : Transcendental K x) (hdx : D K F x ≠ 0) :
    (∀ v : Fin 2 → K, cartier p x (differentialCombination x y v) = 0) ↔
      (hPolynomial p).eval t = 0 := by
  have hp : p.Prime := Fact.out
  have hodd := hp.mod_two_eq_one_iff_ne_two.mpr (show p ≠ 2 by omega)
  rw [cartier_differentialSpan_zero_iff p x hodd _ (natDegree_familyB_le t)
    y hy hy0 htr hdx]
  exact coefficientMatrix_familyB_zero_iff p hp hp3 t

/-- Family (a): the square of actual Cartier gives the same root criterion. -/
theorem familyA_cartier_square_zero_iff (hp5 : 5 ≤ p) (t : K) (ht : t ≠ 0) (y : F)
    (hy : y ^ 2 = aeval x (familyA t)) (hy0 : y ≠ 0)
    (htr : Transcendental K x) (hdx : D K F x ≠ 0) :
    (∀ v : Fin 2 → K, cartier p x (cartier p x (differentialCombination x y v)) = 0) ↔
      (gPolynomial p).eval t = 0 := by
  have hp : p.Prime := Fact.out
  have hodd := hp.mod_two_eq_one_iff_ne_two.mpr (show p ≠ 2 by omega)
  rw [cartier_differentialSpan_square_zero_iff p x hodd _ (natDegree_familyA_le t)
    y hy hy0 htr hdx]
  exact coefficientMatrix_familyA_frobenius_square_zero_iff p hp5 t ht

/-- Family (b): the square criterion also holds at every odd prime. -/
theorem familyB_cartier_square_zero_iff (hp3 : 3 ≤ p) (t : K) (ht : t ≠ 0) (y : F)
    (hy : y ^ 2 = aeval x (familyB t)) (hy0 : y ≠ 0)
    (htr : Transcendental K x) (hdx : D K F x ≠ 0) :
    (∀ v : Fin 2 → K, cartier p x (cartier p x (differentialCombination x y v)) = 0) ↔
      (hPolynomial p).eval t = 0 := by
  have hp : p.Prime := Fact.out
  have hodd := hp.mod_two_eq_one_iff_ne_two.mpr (show p ≠ 2 by omega)
  rw [cartier_differentialSpan_square_zero_iff p x hodd _ (natDegree_familyB_le t)
    y hy hy0 htr hdx]
  exact coefficientMatrix_familyB_frobenius_square_zero_iff p hp3 t ht

/-- The equality of the two criteria is special to family (a). -/
theorem familyA_cartier_square_zero_iff_zero (hp5 : 5 ≤ p) (t : K) (ht : t ≠ 0)
    (y : F) (hy : y ^ 2 = aeval x (familyA t)) (hy0 : y ≠ 0)
    (htr : Transcendental K x) (hdx : D K F x ≠ 0) :
    (∀ v : Fin 2 → K, cartier p x (cartier p x (differentialCombination x y v)) = 0) ↔
      (∀ v : Fin 2 → K, cartier p x (differentialCombination x y v) = 0) := by
  rw [familyA_cartier_square_zero_iff p x hp5 t ht y hy hy0 htr hdx,
    familyA_cartier_zero_iff p x hp5 t y hy hy0 htr hdx]

/-- Family (b) has the same special equality of the two criteria. -/
theorem familyB_cartier_square_zero_iff_zero (hp3 : 3 ≤ p) (t : K) (ht : t ≠ 0)
    (y : F) (hy : y ^ 2 = aeval x (familyB t)) (hy0 : y ≠ 0)
    (htr : Transcendental K x) (hdx : D K F x ≠ 0) :
    (∀ v : Fin 2 → K, cartier p x (cartier p x (differentialCombination x y v)) = 0) ↔
      (∀ v : Fin 2 → K, cartier p x (differentialCombination x y v) = 0) := by
  rw [familyB_cartier_square_zero_iff p x hp3 t ht y hy hy0 htr hdx,
    familyB_cartier_zero_iff p x hp3 t y hy hy0 htr hdx]

omit [Fact p.Prime] [CharP K p] in
/-- In characteristic three the fifth-power example separates C = 0 from C² = 0
on actual rational differentials, subject to the displayed coordinate hypotheses. -/
theorem x_fifth_sub_one_three_cartier_distinction [CharP K 3] (y : F)
    (hy : y ^ 2 = aeval x (X ^ 5 - 1 : K[X])) (hy0 : y ≠ 0)
    (htr : Transcendental K x) (hdx : D K F x ≠ 0) :
    (¬ ∀ v : Fin 2 → K, cartier 3 x (differentialCombination x y v) = 0) ∧
      (∀ v : Fin 2 → K, cartier 3 x (cartier 3 x (differentialCombination x y v)) = 0) := by
  have hdeg : (X ^ 5 - 1 : K[X]).natDegree ≤ 6 := by compute_degree; norm_num
  rw [cartier_differentialSpan_zero_iff 3 x (by decide) _ hdeg y hy hy0 htr hdx,
    cartier_differentialSpan_square_zero_iff 3 x (by decide) _ hdeg y hy hy0 htr hdx]
  simpa only [← frobenius_twistMatrix] using
    x_fifth_sub_one_three_matrix_distinction (frobeniusEquiv K 3)

end SupersingularCurves.IKO
