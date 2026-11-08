/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusVerschiebungQuotientFactorCotangent
import SupersingularCurves.Geometry.JacobianVerschiebungTwistVanishing

/-!
# Jacobian identities for the actual quotient cotangent maps

The independently constructed Jacobian identity sections agree with the
group-scheme identity sections on both successive Frobenius twists. This
transfers the proved Cartier-square and nonvanishing results to the actual
cotangent maps used in the finite quotient construction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

namespace SupersingularCurves.Geometry.Jacobian
open CategoryTheory AlgebraicGeometry AlgebraicCurve NeronModelInfra GoodReductionJacobian
open SchemeFrobenius FrobeniusVerschiebungSubgroup PointedCotangent

variable {K : Type u} [Field K] [IsAlgClosed K]
variable {F : Type v} [Field F] [Algebra K F]
variable {M : CurveModel K F}
  {s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase}
variable (J : Jacobian M s)
variable (p : ℕ) [Fact p.Prime] [CharP K p]

/-- The second actual group-scheme identity is the designated Jacobian identity. -/
theorem groupScheme_twiceTwistZero_eq :
    GroupScheme.twistZero p (twistGroup p J.abelianVariety) = J.twiceTwistedZero p := by
  have hzero : GroupScheme.zero (twistGroup p J.abelianVariety) =
      GroupScheme.twistZero p J.abelianVariety.group :=
    relativeGroupLawOfGrpObj_grpObjOverMk_one (law p J.abelianVariety) (𝟙 _)
  apply Subtype.ext
  rw [← GroupScheme.relative_zero, hzero, J.groupScheme_twistZero_eq p]
  exact section_relative p (J.twistToBase p) (J.twistedZero p)

variable (D : QuotientData p J.abelianVariety)

/-- Vanishing of the actual twisted V differential is independent of the
two proved equal choices of identity-section notation. -/
theorem quotient_twistedVerschiebungCotangent_eq_zero_iff :
    D.verschiebungTwistCotangent = 0 ↔ J.twistedVerschiebungCotangent p = 0 :=
  differential_eq_zero_iff_of_points_eq
    (J.groupScheme_twiceTwistZero_eq p) (J.groupScheme_twistZero_eq p) _ _ _ _

/-- Nonzero actual Jacobian V differential gives nonzero actual twisted V
in the quotient's cotangent factorization. -/
theorem quotient_twistedVerschiebungCotangent_ne_zero
    (𝒱 : M.C.TwoAffineOpenCover) (h : J.verschiebungCotangent p ≠ 0) :
    D.verschiebungTwistCotangent ≠ 0 := by
  intro hzero
  exact J.twistedVerschiebungCotangent_ne_zero p 𝒱 h
    ((J.quotient_twistedVerschiebungCotangent_eq_zero_iff p D).mp hzero)

variable [Algebra.EssFiniteType K F] [IsCurveOver K F]
variable (V : DifferentialChart M)
variable (x : F) [FiniteDimensional (IntermediateField.adjoin K {x}) F]

/-- Cartier squared zero gives the actual twofold cotangent composite used
in the quotient factorization, with both actual Frobenius twists retained. -/
theorem quotient_twistedVerschiebungCotangent_comp_eq_zero_of_globalCartier_square_zero
    (hzero : ∀ ω : V.GlobalForms, V.globalCartier p x (V.globalCartier p x ω) = 0) :
    D.verschiebungTwistCotangent ∘ₗ
      GroupScheme.verschiebungCotangent p J.abelianVariety.group
        (GroupScheme.law_commutative J.abelianVariety.group) = 0 := by
  unfold QuotientData.verschiebungTwistCotangent GroupScheme.verschiebungCotangent
  rw [← differential_comp]
  apply (differential_eq_zero_iff_of_points_eq
    (J.groupScheme_twiceTwistZero_eq p) J.groupScheme_zero_eq _ _ _ _).mpr
  exact J.differential_verschiebung_twice_eq_zero_of_globalCartier_square_zero p V x hzero

end SupersingularCurves.Geometry.Jacobian
