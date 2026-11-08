/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.JacobianVerschiebung
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_representsRelSubPic_baseChange
import Theorems.Thm_AlgebraicGeometry_RelPicard_relativeGroupLaw_baseChange_eq

/-!
# Picard representability on the actual Frobenius twist

The base-change theorem for the actual relative Picard functor proves that
the Frobenius twist of the representing scheme represents the twisted curve.
Its Poincare bundle is the base change of the original bundle, and the induced
tensor-product group law is the group law already used to construct V.

Consequently curve-Frobenius Picard pullback and the independently descended
V now have the same actual source and target. Their equality is still a
further theorem; it is not imposed in this construction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

namespace SupersingularCurves.Geometry.SchemeFrobenius
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open NeronModelInfra GoodReductionJacobian

variable (p : ℕ) [Fact p.Prime]
variable {K : Type u} [Field K] [CharP K p]
variable {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of K)}
  {s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c}
variable (D : RelativePic0Designation K c)

/-- The actual Frobenius base change of the designated Picard scheme. -/
def twistDesignation : RelativePic0Designation K (toBase p c) := by
  letI : Algebra K K := (frobenius K p).toAlgebra
  exact D.baseChange K

theorem twistDesignation_toBase : (twistDesignation p D).toBase = toBase p D.toBase := rfl

theorem twistDesignation_zero :
    (twistDesignation p D).zeroSection =
      (twistedSection p D.toBase ⟨D.zeroSection, D.zeroSection_toBase⟩).1 := rfl

variable {D} (h : RepresentsRelSubPic c s (algEquivZeroCut c s) D)

/-- The actual base-changed Poincare bundle on the twisted curve. -/
def twistPoincare :
    RigidifiedLineBundle (toBase p c) (twistedSection p c s) (twistDesignation p D).toBase := by
  letI : Algebra K K := (frobenius K p).toAlgebra
  exact BaseChange.ofR c s K
    (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (baseMap p K), pullback.condition⟩)

/-- The Frobenius-twisted representing scheme represents the actual twisted
curve's algebraically trivial line bundles, on all test schemes. -/
def twistRepresents :
    RepresentsRelSubPic (toBase p c) (twistedSection p c s)
      (algEquivZeroCut (toBase p c) (twistedSection p c s)) (twistDesignation p D) := by
  letI : Algebra K K := (frobenius K p).toAlgebra
  exact (exists_representsRelSubPic_baseChange K c s D h K).choose

theorem twistRepresents_poincare :
    Nonempty ((twistRepresents p h).poincare.L ≅ (twistPoincare p h).L) := by
  letI : Algebra K K := (frobenius K p).toAlgebra
  exact (exists_representsRelSubPic_baseChange K c s D h K).choose_spec

/-- The Picard representation induces precisely the base-changed tensor law
used in the independent Frobenius/Verschiebung construction. -/
theorem twistRepresents_groupLaw :
    (twistRepresents p h).relativeGroupLaw
        (P := algEquivZeroGroupCut (toBase p c) (twistedSection p c s)) =
      twistLaw p D.toBase (h.relativeGroupLaw (P := algEquivZeroGroupCut c s)) := by
  letI : Algebra K K := (frobenius K p).toAlgebra
  exact relativeGroupLaw_baseChange_eq K c s D h K
    (twistRepresents p h) (twistRepresents_poincare p h)

end SupersingularCurves.Geometry.SchemeFrobenius

namespace SupersingularCurves.Geometry.Jacobian
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open AlgebraicCurve NeronModelInfra GoodReductionJacobian

variable (p : ℕ) [Fact p.Prime]
variable {K : Type u} [Field K] [CharP K p] [PerfectField K]
variable {F : Type v} [Field F] [Algebra K F]
variable {M : CurveModel K F}
  {s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase}
variable (J : Jacobian M s)

/-- The actual Picard representation on J^(p), for the Frobenius-twisted curve. -/
abbrev twistedPicardRepresentation := SchemeFrobenius.twistRepresents p J.represents

/-- Pullback by curve relative Frobenius, now with the same actual domain and
codomain as the independently constructed V. Equality with V remains open. -/
def frobeniusPicardPullback : J.FrobeniusTwist p ⟶ J.designation.P :=
  (SchemeFrobenius.picardPullback p J.represents (J.twistedPicardRepresentation p)).1

theorem frobeniusPicardPullback_zero :
    (J.twistedZero p).1 ≫ J.frobeniusPicardPullback p = J.designation.zeroSection :=
  SchemeFrobenius.picardPullback_zero p J.represents (J.twistedPicardRepresentation p)

theorem frobeniusPicardPullback_over :
    J.frobeniusPicardPullback p ≫ J.designation.toBase = J.twistToBase p :=
  (SchemeFrobenius.picardPullback p J.represents (J.twistedPicardRepresentation p)).2

/-- Its differential is constructed from actual Picard pullback, separately
from the differential of the independently descended V. -/
def frobeniusPicardPullbackCotangent : J.Cotangent →ₗ[K] J.TwistedCotangent p :=
  PointedCotangent.differential (J.twistToBase p) (J.twistedZero p)
    (z := ⟨J.designation.zeroSection, J.designation.zeroSection_toBase⟩)
    (J.frobeniusPicardPullback p) (J.frobeniusPicardPullback_over p)
    (J.frobeniusPicardPullback_zero p)

end SupersingularCurves.Geometry.Jacobian
