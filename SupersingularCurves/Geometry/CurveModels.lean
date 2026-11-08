/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.Jacobian
import SupersingularCurves.IKO.RegularBasis
import Theorems.Thm_AlgebraicCurve_CurveModel_nonempty_of_perfectField
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_nonempty_place_of_ratFunc_tower

/-!
# Actual smooth proper models of the quadratic function fields

The upstream existence theorem constructs models by gluing normalization charts.
Here its hypotheses are discharged for our constructed quadratic extensions.
Over an algebraically closed field, an actual base point is obtained from a place.
The scheme function-field equivalence transports the defining equation. This
module does not assert that a representing Jacobian has been constructed.
-/

set_option autoImplicit false
noncomputable section

open AlgebraicCurve AlgebraicGeometry AlgebraicGeometry.RelPicard CategoryTheory Polynomial NeronModelInfra GoodReductionJacobian

namespace SupersingularCurves.Hyperelliptic.SimpleRootModel

variable {K : Type*} [Field K] (a : SimpleRootModel K)

/-- The finite-type/transcendence hypotheses follow from the quadratic construction. -/
theorem curveModel_nonempty [PerfectField K] [Infinite K] :
    Nonempty (CurveModel K a.FunctionField) :=
  CurveModel.nonempty_of_perfectField K a.FunctionField
    ⟨a.x, a.transcendental_x, a.finiteDimensional_coordinate⟩

/-- A genuine integral smooth proper curve with the specified function field. -/
def curveModel [PerfectField K] [Infinite K] : CurveModel K a.FunctionField :=
  Classical.choice a.curveModel_nonempty

/-- An actual geometric base point, obtained using the point/place correspondence. -/
def curveModelBasepoint [IsAlgClosed K] [NeZero (2 : K)] :
    SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) a.curveModel.toBase := by
  classical
  let v : Place K a.FunctionField := Classical.choice
    (RationalFunctionField.nonempty_place_of_ratFunc_tower K a.FunctionField)
  exact a.curveModel.pointEquivPlace.symm v

/-- The original equation holds in the scheme's own function field. -/
theorem curveModel_equation [PerfectField K] [Infinite K] :
    letI := a.curveModel.functionFieldAlgebra
    (a.curveModel.ffAlgEquiv a.y) ^ 2 =
      aeval (a.curveModel.ffAlgEquiv a.x) a.f := by
  letI := a.curveModel.functionFieldAlgebra
  have h := congrArg a.curveModel.ffAlgEquiv a.equation_in_functionField
  simpa only [map_pow, ← Polynomial.aeval_algHom_apply] using h

end SupersingularCurves.Hyperelliptic.SimpleRootModel

namespace SupersingularCurves.IKO

variable {K : Type*} [Field K] [IsAlgClosed K] [NeZero (2 : K)]

/-- The family-(a) smooth proper model. The exclusions match the genus-two family. -/
def familyACurve (t : K) (h3 : (3 : K) ≠ 0) (_ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    CurveModel K (familyAModel t h3 ht1).FunctionField :=
  (familyAModel t h3 ht1).curveModel

/-- The family-(b) smooth proper model. -/
def familyBCurve (t : K) (ht0 : t ≠ 0) (_ht1 : t ≠ 1) :
    CurveModel K (familyBModel t ht0).FunctionField :=
  (familyBModel t ht0).curveModel

/-- A pointed smooth proper model and its genus-two function field exist together. -/
theorem familyA_pointed_curve (t : K) (h3 : (3 : K) ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    Nonempty (SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
      (familyACurve t h3 ht0 ht1).toBase) ∧
      genusFF K (familyAModel t h3 ht1).FunctionField = 2 :=
  ⟨⟨(familyAModel t h3 ht1).curveModelBasepoint⟩, familyA_genus t h3 ht0 ht1⟩

theorem familyB_pointed_curve (t : K) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    Nonempty (SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
      (familyBCurve t ht0 ht1).toBase) ∧
      genusFF K (familyBModel t ht0).FunctionField = 2 :=
  ⟨⟨(familyBModel t ht0).curveModelBasepoint⟩, familyB_genus t ht0 ht1⟩

end SupersingularCurves.IKO
