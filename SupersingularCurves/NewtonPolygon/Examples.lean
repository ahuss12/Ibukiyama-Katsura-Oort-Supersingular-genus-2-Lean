/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.NewtonPolygon.Basic

/-! Concrete positive and negative examples from polynomial coefficients and
an actual linear endomorphism. No variety is claimed to realize these examples. -/

set_option autoImplicit false
noncomputable section

namespace SupersingularCurves.NewtonPolygon
open Polynomial Set Matrix

/-- A degree-two endomorphism with characteristic polynomial `T² + p`. -/
def halfSlopeEndomorphism (p : ℕ) : Module.End ℚ (Fin 2 → ℚ) :=
  (!![0, -(p : ℚ); 1, 0] : Matrix (Fin 2) (Fin 2) ℚ).toLin'

theorem halfSlopeEndomorphism_charpoly (p : ℕ) :
    (halfSlopeEndomorphism p).charpoly = X ^ 2 + C (p : ℚ) := by
  simp [halfSlopeEndomorphism, Matrix.charpoly_fin_two, Matrix.trace_fin_two,
    Matrix.det_fin_two]

theorem halfSlopeEndomorphism_newton (p : ℕ) [Fact p.Prime] :
    ofEndomorphism p 1 (halfSlopeEndomorphism p) = supersingular 1 := by
  rw [ofEndomorphism, halfSlopeEndomorphism_charpoly]
  have hrev : (X ^ 2 + C (p : ℚ)).reverse = 1 + C (p : ℚ) * X ^ 2 := by
    rw [reverse_add_C]
    have hx : (X ^ 2 : ℚ[X]).reverse = 1 := by
      have h1 : (1 : ℚ[X]).reverse = 1 := by
        simpa only [Polynomial.C_1] using (reverse_C (1 : ℚ))
      simpa only [mul_one, h1] using (reverse_X_pow_mul (1 : ℚ[X]) 2)
    simp [hx]
  rw [hrev]
  simpa using padic_binomial_supersingular p 1 (g := 1) (by decide)

/-- Genus-two and genus-five shapes are checked with the same normalization. -/
theorem genus_two_polynomial_newton (p : ℕ) [Fact p.Prime] :
    padic p 1 (1 + C ((p : ℚ) ^ 2) * X ^ 4) = supersingular 2 := by
  simpa using padic_binomial_supersingular p 1 (g := 2) (by decide)

theorem genus_five_polynomial_newton (p : ℕ) [Fact p.Prime] :
    padic p 1 (1 + C ((p : ℚ) ^ 5) * X ^ 10) = supersingular 5 := by
  simpa using padic_binomial_supersingular p 1 (g := 5) (by decide)

/-- The coefficients of `1 + T + 3T²` give the three expected valuation points. -/
theorem ordinary_three_coefficientPoints :
    coefficientPoints (normalizedValuation 3 1) (1 + X + C 3 * X ^ 2) =
      ({(0, 0), (1, 0), (2, 1)} : Set (ℚ × ℚ)) := by
  have hv1 : normalizedValuation 3 1 1 = 0 := normalizedValuation_one 3 1
  have hv3 : normalizedValuation 3 1 3 = 1 := by
    simpa [normalizedValuation] using
      congrArg (fun z : ℤ => (z : ℚ)) (padicValRat.self (by decide : 1 < 3))
  ext P
  constructor
  · rintro ⟨i, hi, rfl⟩
    by_cases h0 : i = 0
    · subst i; simp [coeff_add, coeff_one, coeff_X, hv1]
    · by_cases h1 : i = 1
      · subst i; simp [coeff_add, coeff_one, coeff_X, hv1]
      · by_cases h2 : i = 2
        · subst i; simp [coeff_add, coeff_one, coeff_X, hv3]
        · simp [coeff_add, coeff_one, coeff_X, h0, h2, Ne.symm h1] at hi
  · intro hP
    rcases hP with hP | hP | hP
    · subst P
      exact ⟨0, by norm_num, by simp [hv1]⟩
    · subst P
      exact ⟨1, by norm_num [coeff_add, coeff_one, coeff_X],
        by simp [coeff_add, coeff_one, coeff_X, hv1]⟩
    · subst P
      exact ⟨2, by norm_num [coeff_add, coeff_one, coeff_X],
        by simp [coeff_add, coeff_one, coeff_X, hv3]⟩

/-- A non-supersingular example: the middle point belongs to the lower boundary. -/
theorem ordinary_three_middle_mem :
    (1, 0) ∈ padic 3 1 (1 + X + C 3 * X ^ 2) := by
  rw [padic, ofPolynomial, ordinary_three_coefficientPoints]
  have hc : Convex ℚ {P : ℚ × ℚ | 0 ≤ P.2} := by
    intro P hP Q hQ a b ha hb hab
    change 0 ≤ a * P.2 + b * Q.2
    exact add_nonneg (mul_nonneg ha hP) (mul_nonneg hb hQ)
  refine ⟨subset_convexHull ℚ _ (by simp), ?_⟩
  intro Q hQ _
  apply convexHull_min (t := {P : ℚ × ℚ | 0 ≤ P.2}) _ hc hQ
  rintro P (rfl | rfl | rfl) <;> norm_num

theorem ordinary_three_not_supersingular :
    ¬HasSupersingularShape 1 (padic 3 1 (1 + X + C 3 * X ^ 2)) := by
  intro h
  have hm := ordinary_three_middle_mem
  rw [show padic 3 1 (1 + X + C 3 * X ^ 2) = supersingular 1 from h] at hm
  have hs := supersingular_half_slope 1 hm
  norm_num at hs

end SupersingularCurves.NewtonPolygon
