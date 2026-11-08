/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Differentials.Regularity

/-!
# The reciprocal chart for every separable quintic or sextic

The polynomial `reflect 6 f` gives the equation in coordinates u = 1/x,
z = y/x^3. Its separability is proved, including the possible branch point
at u = 0. No reciprocal-chart regularity is included as an input assumption.
-/

set_option autoImplicit false
noncomputable section

namespace SupersingularCurves.Hyperelliptic
open Polynomial AlgebraicCurve KaehlerDifferential
open SupersingularCurves.Differentials
variable {K : Type*} [Field K]

theorem sextic_expansion (f : K[X]) (hf : f.natDegree ≤ 6) :
    f = C (f.coeff 0) + C (f.coeff 1) * X + C (f.coeff 2) * X^2 +
      C (f.coeff 3) * X^3 + C (f.coeff 4) * X^4 + C (f.coeff 5) * X^5 +
      C (f.coeff 6) * X^6 := by
  simpa [Finset.sum_range_succ] using
    f.as_sum_range_C_mul_X_pow' (n := 7) (by omega)

theorem reflect_six_expansion (f : K[X]) (hf : f.natDegree ≤ 6) :
    f.reflect 6 = C (f.coeff 6) + C (f.coeff 5) * X + C (f.coeff 4) * X^2 +
      C (f.coeff 3) * X^3 + C (f.coeff 2) * X^4 + C (f.coeff 1) * X^5 +
      C (f.coeff 0) * X^6 := by
  have hx : reflect 6 (X : K[X]) = X^5 := by
    simpa using (reflect_monomial (R := K) 6 1)
  conv_lhs => rw [sextic_expansion f hf]
  simp only [reflect_add, reflect_C_mul, reflect_C, hx]
  norm_num [reflect_monomial, revAt_le]
  ring

theorem eval_reflect_six (f : K[X]) (hf : f.natDegree ≤ 6)
    (t : K) (ht : t ≠ 0) : (f.reflect 6).eval t = t^6 * f.eval t⁻¹ := by
  conv_lhs => rw [reflect_six_expansion f hf]
  conv_rhs => rw [sextic_expansion f hf]
  simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X]
  field_simp [ht]
  ring

theorem eval_derivative_reflect_six (f : K[X]) (hf : f.natDegree ≤ 6)
    (t : K) (ht : t ≠ 0) :
    (f.reflect 6).derivative.eval t =
      6 * t^5 * f.eval t⁻¹ - t^4 * f.derivative.eval t⁻¹ := by
  conv_lhs => rw [reflect_six_expansion f hf]
  conv_rhs => rw [sextic_expansion f hf]
  simp only [derivative_add, derivative_mul, derivative_C, derivative_X,
    derivative_pow, eval_add, eval_mul, eval_pow, eval_C, eval_X,
    eval_zero, eval_one]
  norm_num
  field_simp [ht]
  ring

/-- Reversing a separable quintic or sextic gives a separable second chart. -/
theorem reflect_six_separable [IsAlgClosed K] (f : K[X]) (hf : f.Separable)
    (hd : f.natDegree = 5 ∨ f.natDegree = 6) : (f.reflect 6).Separable := by
  change IsCoprime (f.reflect 6) (f.reflect 6).derivative
  rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k := K) K
    (f.reflect 6) (f.reflect 6).derivative]
  intro t
  change (f.reflect 6).eval t ≠ 0 ∨ (f.reflect 6).derivative.eval t ≠ 0
  by_cases ht : t = 0
  · subst t
    simp only [← coeff_zero_eq_eval_zero, coeff_derivative, coeff_reflect]
    norm_num [revAt_le]
    rcases hd with hd | hd
    · exact Or.inr (by simpa [← hd, coeff_natDegree] using (leadingCoeff_ne_zero.mpr hf.ne_zero))
    · exact Or.inl (by simpa [← hd, coeff_natDegree] using (leadingCoeff_ne_zero.mpr hf.ne_zero))
  · have hle : f.natDegree ≤ 6 := by omega
    by_cases hz : (f.reflect 6).eval t = 0
    · right
      have hroot : f.eval t⁻¹ = 0 := by
        rw [eval_reflect_six f hle t ht] at hz
        exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ ht)
      rw [eval_derivative_reflect_six f hle t ht, hroot, mul_zero, zero_sub]
      exact neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ ht)
        (hf.eval₂_derivative_ne_zero (RingHom.id K) hroot))
    · exact Or.inl hz

variable {F : Type*} [Field F] [Algebra K F]

/-- The actual quadratic equation in the reciprocal coordinates. -/
theorem reciprocal_equation (f : K[X]) (hf : f.natDegree ≤ 6)
    (x y : F) (hx : x ≠ 0) (hy : y^2 = aeval x f) :
    (y * x⁻¹^3)^2 = aeval x⁻¹ (f.reflect 6) := by
  let : Invertible x := invertibleOfNonzero hx
  have he := eval₂_reflect_mul_pow (algebraMap K F) x 6 f hf
  simp only [invOf_eq_inv, ← aeval_def] at he
  calc
    (y * x⁻¹^3)^2 = aeval x f * (x^6)⁻¹ := by
      rw [mul_pow, hy, ← pow_mul, inv_pow]
    _ = aeval x⁻¹ (f.reflect 6) := by
      rw [← he]
      field_simp

/-- Regularity at every place for any separable quintic or sextic equation. -/
theorem quintic_sextic_pair_regular [IsAlgClosed K] [IsCurveOver K F]
    (x : F) [FiniteDimensional (IntermediateField.adjoin K {x}) F]
    (f : K[X]) (hf : f.Separable) (hd : f.natDegree = 5 ∨ f.natDegree = 6)
    (y : F) (hy : y^2 = aeval x f) (hx : x ≠ 0) (hy0 : y ≠ 0) :
    y⁻¹ • D K F x ∈ regularDifferentials K F ∧
      x • (y⁻¹ • D K F x) ∈ regularDifferentials K F :=
  hyperelliptic_pair_mem_regularDifferentials x x y f (f.reflect 6)
    hf (reflect_six_separable f hf hd) hy
    (reciprocal_equation f (by omega) x y hx hy) hx hy0

end SupersingularCurves.Hyperelliptic
