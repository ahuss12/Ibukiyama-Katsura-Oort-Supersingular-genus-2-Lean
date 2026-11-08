/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.JacobianPoints
import SupersingularCurves.Geometry.CurveModels
import Theorems.Thm_AlgebraicCurve_CurveModel_exists_representsRelSubPic_abelJacobi_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_CurveModel_smoothOfRelativeDimension_genusFF_of_representsRelSubPic

/-!
# Representing Jacobians with the actual divisor-class group

Existence, smooth dimension, and the point-group identification are derived from
pinned upstream Picard representability theorems. No Jacobian existence or
Cartier/supersingularity criterion is an assumption of the construction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

namespace SupersingularCurves.Geometry
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open AlgebraicCurve NeronModelInfra GoodReductionJacobian
open scoped CategoryTheory.MonObj

variable {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]

/-- A genuine representing Jacobian with a group-compatible divisor-class map
and the Abel–Jacobi morphism taking the chosen base point to the identity. -/
structure JacobianRealization (M : AlgebraicCurve.CurveModel K F)
    (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase) where
  jacobian : Jacobian M s
  picardPoints : Pic0 K F ≃+ Additive jacobian.abelianVariety.Points
  abelJacobi : SchemeHomOver M.toBase jacobian.designation.toBase
  basepoint_eq_zero : s.1 ≫ abelJacobi.1 = jacobian.designation.zeroSection

variable [IsAlgClosed K] [IsCurveOver K F]

/-- The universal property and the correct group identification are proved to
exist for a pointed curve model of a one-variable function field. -/
theorem jacobianRealization_nonempty
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K {x}) F)
    (M : AlgebraicCurve.CurveModel K F)
    (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase) :
    Nonempty (JacobianRealization M s) := by
  obtain ⟨D, h, aj, _, hproper, hconnected, hzero, _, pts, hadd, _⟩ :=
    AlgebraicCurve.CurveModel.exists_representsRelSubPic_abelJacobi_of_isAlgClosed K F M s
  let J : Jacobian M s :=
    { designation := D
      represents := h
      smooth := AlgebraicCurve.CurveModel.smoothOfRelativeDimension_genusFF_of_representsRelSubPic
        K F hfg M s D h
      proper := hproper
      connected := hconnected }
  let e : Pic0 K F ≃+ Additive J.abelianVariety.Points :=
    J.picardPointsAddEquiv pts hadd
  exact ⟨⟨J, e, aj, hzero⟩⟩

/-- Choose data only after genuine existence and group compatibility are proved. -/
def constructJacobian
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K {x}) F)
    (M : AlgebraicCurve.CurveModel K F)
    (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase) :
    JacobianRealization M s :=
  Classical.choice (jacobianRealization_nonempty hfg M s)

end SupersingularCurves.Geometry
