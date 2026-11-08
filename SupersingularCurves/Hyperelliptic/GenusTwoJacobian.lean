/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Hyperelliptic.GenusTwoCartier
import SupersingularCurves.Geometry.JacobianIndependence
import SupersingularCurves.PicardTorsion.Equivalence
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_isAlgClosed

/-!
# Nilpotent Cartier implies p-rank zero for the actual Jacobian

This uses the logarithm on actual divisor-class torsion and the point group of
any representing Jacobian. It makes no supersingular or superspecial
classification assumption. The constructed Jacobian is also provided.
-/
set_option autoImplicit false
noncomputable section
namespace SupersingularCurves.Hyperelliptic.SimpleRootModel
open CategoryTheory AlgebraicGeometry AlgebraicCurve KaehlerDifferential
open AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open SupersingularCurves.Geometry SupersingularCurves.Differentials
open SupersingularCurves.IKO SupersingularCurves.PicardTorsion
variable {K : Type*} [Field K] [IsAlgClosed K] [NeZero (2 : K)]
  (a : SimpleRootModel K)

/-- A representing Jacobian of the actual smooth proper model, with Abel–Jacobi. -/
def jacobianRealization : JacobianRealization a.curveModel a.curveModelBasepoint :=
  constructJacobian ⟨a.x, a.transcendental_x, a.finiteDimensional_coordinate⟩
    a.curveModel a.curveModelBasepoint

variable (p : ℕ) [Fact p.Prime] [CharP K p]

/-- This implication does not need a genus or polynomial-degree hypothesis. -/
theorem jacobian_hasPRankOver_zero_of_cartier_square_zero
    (hN : ∀ ω : regularDifferentials K a.FunctionField,
      regularCartier p a.x (regularCartier p a.x ω) = 0)
    {s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) a.curveModel.toBase}
    (J : Jacobian a.curveModel s) : J.abelianVariety.HasPRankOver p 0 := by
  classical
  have hC : ConstantsAreBase K a.FunctionField :=
    constantsAreBase_of_isAlgClosed K a.FunctionField
  have ht : ∀ q : Pic0.torsion K a.FunctionField p, q = 0 :=
    torsion_eq_zero_of_regularCartierSquared_zero p a.x hC hN
  have hc : Nat.card (J.abelianVariety.torsionPoints p) = 1 := by
    rw [card_torsionPoints_eq_picard _ J.picardPoints p]
    exact Nat.card_eq_one_iff_exists.mpr ⟨0, ht⟩
  exact ⟨Nat.finite_of_card_ne_zero (by rw [hc]; decide), by simpa using hc⟩

/-- The general IKO twisted-matrix condition kills actual Jacobian p-torsion. -/
theorem jacobian_hasPRankOver_zero_of_matrix
    (hf : a.f.Separable) (hd : a.f.natDegree = 5 ∨ a.f.natDegree = 6)
    (hp : p % 2 = 1)
    (hM : (coefficientMatrix p a.f).map (fun c => c^p) * coefficientMatrix p a.f = 0)
    {s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) a.curveModel.toBase}
    (J : Jacobian a.curveModel s) : J.abelianVariety.HasPRankOver p 0 :=
  a.jacobian_hasPRankOver_zero_of_cartier_square_zero p
    ((a.all_regularCartier_square_zero_iff hf hd p hp).mpr hM) J

end SupersingularCurves.Hyperelliptic.SimpleRootModel
