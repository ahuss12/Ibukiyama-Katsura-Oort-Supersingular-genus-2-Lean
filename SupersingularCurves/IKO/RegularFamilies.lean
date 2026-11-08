/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Hyperelliptic.FunctionField
import SupersingularCurves.IKO.CartierFamilies

/-!
# The two IKO families have actual regular differentials

Both branch polynomials and both reciprocal-chart polynomials are proved
separable for admissible parameters. The two displayed forms are then regular
at every actual place. We also construct the quadratic function fields from
their explicit simple roots, discharging the prior coordinate hypotheses.
Spanning the entire regular-differential space remains a separate result.
-/

set_option autoImplicit false
noncomputable section

namespace SupersingularCurves.IKO

open Polynomial AlgebraicCurve KaehlerDifferential
open SupersingularCurves.Differentials SupersingularCurves.Hyperelliptic

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem coprime_X_X_pow_sub_C (n : ℕ) (hn : 0 < n) (t : K) (ht : t ≠ 0) :
    IsCoprime X (X ^ n - C t) := by
  refine ⟨C t⁻¹ * X ^ (n - 1), -C t⁻¹, ?_⟩
  have he : n - 1 + 1 = n := by omega
  calc
    _ = C t⁻¹ * C t := by rw [mul_assoc, ← pow_succ, he]; ring
    _ = 1 := by rw [← map_mul, inv_mul_cancel₀ ht, map_one]

/-- The second family is separable at every admissible parameter in odd characteristic. -/
theorem familyB_separable (t : K) (h2 : (2 : K) ≠ 0)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) : (familyB t).Separable := by
  have hs1 : (X ^ 2 - 1 : K[X]).Separable := by
    simpa using separable_X_pow_sub_C (1 : K) h2 one_ne_zero
  have hs2 := separable_X_pow_sub_C t h2 ht0
  have hc1 : IsCoprime (X : K[X]) (X ^ 2 - 1) := by
    simpa using coprime_X_X_pow_sub_C 2 (by decide) (1 : K) one_ne_zero
  have hc2 := coprime_X_X_pow_sub_C 2 (by decide) t ht0
  have hc3 : IsCoprime (X ^ 2 - 1 : K[X]) (X ^ 2 - C t) := by
    simpa using coprime_X_pow_sub_C 2 (1 : K) t ht1.symm
  exact (separable_X.mul hs1 hc1).mul hs2 (hc2.mul_left hc3)

/-- The reciprocal chart has parameter t⁻¹ and an explicit nonzero scalar factor. -/
theorem familyA_reciprocal_equation (t : K) (ht0 : t ≠ 0) (x y : F)
    (hx0 : x ≠ 0) (hy : y ^ 2 = aeval x (familyA t)) :
    (y * x⁻¹ ^ 3) ^ 2 = aeval x⁻¹ (C t * familyA t⁻¹) := by
  rw [mul_pow, hy]
  simp only [familyA, map_mul, map_sub, map_pow, map_one, aeval_X, aeval_C, map_inv₀]
  have ht : algebraMap K F t ≠ 0 := (_root_.map_ne_zero _).mpr ht0
  field_simp
  ring

theorem familyB_reciprocal_equation (t : K) (ht0 : t ≠ 0) (x y : F)
    (hx0 : x ≠ 0) (hy : y ^ 2 = aeval x (familyB t)) :
    (y * x⁻¹ ^ 3) ^ 2 = aeval x⁻¹ (C t * familyB t⁻¹) := by
  rw [mul_pow, hy]
  simp only [familyB, map_mul, map_sub, map_pow, map_one, aeval_X, aeval_C, map_inv₀]
  have ht : algebraMap K F t ≠ 0 := (_root_.map_ne_zero _).mpr ht0
  field_simp
  ring

theorem familyA_reciprocal_separable (t : K) (h3 : (3 : K) ≠ 0)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) : (C t * familyA t⁻¹).Separable := by
  exact Separable.unit_mul ((isUnit_iff_ne_zero.mpr ht0).map C)
    (familyA_separable t⁻¹ h3 (inv_ne_zero ht0) (by simpa using ht1))

theorem familyB_reciprocal_separable (t : K) (h2 : (2 : K) ≠ 0)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) : (C t * familyB t⁻¹).Separable := by
  exact Separable.unit_mul ((isUnit_iff_ne_zero.mpr ht0).map C)
    (familyB_separable t⁻¹ h2 (inv_ne_zero ht0) (by simpa using ht1))

/-- All places are covered by the finite and reciprocal charts for family (a). -/
theorem familyA_pair_regular [PerfectField K] [IsCurveOver K F]
    (x : F) [FiniteDimensional (IntermediateField.adjoin K {x}) F]
    (t : K) (h3 : (3 : K) ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (y : F) (hy : y ^ 2 = aeval x (familyA t)) (hx0 : x ≠ 0) (hy0 : y ≠ 0) :
    y⁻¹ • D K F x ∈ regularDifferentials K F ∧
      x • (y⁻¹ • D K F x) ∈ regularDifferentials K F :=
  hyperelliptic_pair_mem_regularDifferentials x x y _ _
    (familyA_separable t h3 ht0 ht1) (familyA_reciprocal_separable t h3 ht0 ht1)
    hy (familyA_reciprocal_equation t ht0 x y hx0 hy) hx0 hy0

theorem familyB_pair_regular [PerfectField K] [IsCurveOver K F]
    (x : F) [FiniteDimensional (IntermediateField.adjoin K {x}) F]
    (t : K) (h2 : (2 : K) ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (y : F) (hy : y ^ 2 = aeval x (familyB t)) (hx0 : x ≠ 0) (hy0 : y ≠ 0) :
    y⁻¹ • D K F x ∈ regularDifferentials K F ∧
      x • (y⁻¹ • D K F x) ∈ regularDifferentials K F :=
  hyperelliptic_pair_mem_regularDifferentials x x y _ _
    (familyB_separable t h2 ht0 ht1) (familyB_reciprocal_separable t h2 ht0 ht1)
    hy (familyB_reciprocal_equation t ht0 x y hx0 hy) hx0 hy0

/-- The simple root x = 1 constructs the actual family-(a) function field. -/
def familyAModel (t : K) (h3 : (3 : K) ≠ 0) (ht1 : t ≠ 1) : SimpleRootModel K where
  f := familyA t
  root := 1
  root_zero := by simp [familyA]
  derivative_ne_zero := by
    have he : (familyA t).derivative.eval 1 = 3 * (1 - t) := by
      norm_num [familyA, derivative_mul]
    rw [he]
    exact mul_ne_zero h3 (sub_ne_zero.mpr ht1.symm)

/-- The simple root x = 0 constructs the actual family-(b) function field. -/
def familyBModel (t : K) (ht0 : t ≠ 0) : SimpleRootModel K where
  f := familyB t
  root := 0
  root_zero := by simp [familyB]
  derivative_ne_zero := by simpa [familyB, derivative_mul] using ht0

end SupersingularCurves.IKO
