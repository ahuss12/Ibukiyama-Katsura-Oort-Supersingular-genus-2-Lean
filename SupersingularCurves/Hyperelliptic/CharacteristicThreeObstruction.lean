/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Hyperelliptic.GenusTwoSuperspecial

/-!
# No superspecial presented genus-two curves in characteristic three

For every separable polynomial of degree five or six in characteristic three,
the actual genus-two Cartier matrix is nonzero. In degree five its bottom-left
entry is the leading coefficient. In degree six a zero matrix would force the
polynomial's derivative to vanish, contradicting separability and positive
degree. The proved geometric-to-Cartier direction then rules out geometric
superspeciality for every represented Jacobian of the presented curve.

This boundary case does not assert the general superspecial converse.
-/

set_option autoImplicit false
noncomputable section

namespace SupersingularCurves.IKO
open Polynomial

variable {K : Type*} [Field K] [CharP K 3]

/-- A separable quintic or sextic in characteristic three has nonzero
genus-two coefficient matrix. -/
theorem coefficientMatrix_three_ne_zero_of_separable
    (f : K[X]) (hf : f.Separable) (hd : f.natDegree = 5 ∨ f.natDegree = 6) :
    coefficientMatrix 3 f ≠ 0 := by
  intro h
  have h1 : f.coeff 1 = 0 := by
    simpa [coefficientMatrix] using congrFun (congrFun h 0) 1
  have h2 : f.coeff 2 = 0 := by
    simpa [coefficientMatrix] using congrFun (congrFun h 0) 0
  have h4 : f.coeff 4 = 0 := by
    simpa [coefficientMatrix] using congrFun (congrFun h 1) 1
  have h5 : f.coeff 5 = 0 := by
    simpa [coefficientMatrix] using congrFun (congrFun h 1) 0
  rcases hd with hd | hd
  · have hlead : f.leadingCoeff = 0 := by
      simpa only [leadingCoeff, hd] using h5
    exact hf.ne_zero (leadingCoeff_eq_zero.mp hlead)
  · have hderiv : f.derivative = 0 := by
      ext n
      rw [coeff_derivative, coeff_zero]
      by_cases hn : n < 6
      · have h3 : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
        have h6 : (6 : K) = 0 := by
          have : (6 : K) = 2 * 3 := by norm_num
          rw [this, h3, mul_zero]
        interval_cases n <;> norm_num [h1, h2, h4, h5]
        · exact Or.inr h3
        · exact Or.inr h6
      · rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
    have hu : IsUnit f := by
      simpa only [separable_def, hderiv, isCoprime_zero_right] using hf
    have hdeg := natDegree_eq_zero_of_isUnit hu
    omega

end SupersingularCurves.IKO

namespace SupersingularCurves.Hyperelliptic.SimpleRootModel
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open NeronModelInfra GoodReductionJacobian
open SupersingularCurves.Geometry SupersingularCurves.Differentials
open SupersingularCurves.IKO

variable {K : Type*} [Field K] [IsAlgClosed K] [CharP K 3] [NeZero (2 : K)]
  (a : SimpleRootModel K) (hf : a.f.Separable)
  (hd : a.f.natDegree = 5 ∨ a.f.natDegree = 6)
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

include hf hd

/-- Cartier does not vanish on the entire regular differential space of
any presented genus-two curve in characteristic three. -/
theorem not_all_regularCartier_three_zero :
    ¬ ∀ ω : regularDifferentials K a.FunctionField, regularCartier 3 a.x ω = 0 := by
  rw [a.all_regularCartier_zero_iff hf hd 3 (by decide)]
  exact coefficientMatrix_three_ne_zero_of_separable a.f hf hd

/-- Cartier does not vanish on all global forms of any presented genus-two
curve in characteristic three. -/
theorem not_all_globalCartier_three_zero :
    ¬ ∀ ω : a.GlobalForms, a.globalCartier 3 ω = 0 := by
  rw [a.all_globalCartier_zero_iff hf hd 3 (by decide)]
  exact coefficientMatrix_three_ne_zero_of_separable a.f hf hd

/-- Every representing Jacobian fails geometric superspeciality, not just
the chosen realization. -/
theorem jacobian_not_isSuperspecial_three
    {s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) a.curveModel.toBase}
    (J : Jacobian a.curveModel s) : ¬ J.IsSuperspecial 3 := by
  intro h
  exact coefficientMatrix_three_ne_zero_of_separable a.f hf hd
    (a.jacobian_isSuperspecial_imp_matrix 3 hf hd (by decide) J h)

/-- No presented separable genus-two quintic or sextic in characteristic
three has a geometrically superspecial Jacobian. -/
theorem not_isSuperspecial_three :
    ¬ Geometry.CurveModel.IsSuperspecial 3 a.curveModel := by
  intro h
  exact coefficientMatrix_three_ne_zero_of_separable a.f hf hd
    (a.isSuperspecial_imp_matrix 3 hf hd (by decide) h)

end SupersingularCurves.Hyperelliptic.SimpleRootModel
