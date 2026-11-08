/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.Verschiebung
import SupersingularCurves.Geometry.PointedCotangent

/-!
# Independent Jacobian Verschiebung over perfect fields

For any given genuine representing Jacobian, V is constructed from its
tensor-product group law by descending multiplication by p along relative
Frobenius. Its source is the actual Frobenius fibre product, not the original
scheme with the twist suppressed. The cotangent differential consequently
maps from Cot(J) to Cot(J^(p)). It is characterized by its action on all
actual square-zero points.

This does not identify V with curve Frobenius pullback, identify its
differential with Cartier, or assert a geometric classification criterion.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

namespace SupersingularCurves.Geometry.Jacobian
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open AlgebraicCurve NeronModelInfra GoodReductionJacobian

variable (p : ℕ) [Fact p.Prime]
variable {K : Type u} [Field K] [CharP K p] [PerfectField K]
variable {F : Type v} [Field F] [Algebra K F]
variable {M : CurveModel K F}
  {s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase}
variable (J : Jacobian M s)

local instance smoothJacobian : Smooth J.designation.toBase :=
  SmoothOfRelativeDimension.smooth (genusFF K F) J.designation.toBase

/-- The genuine group law induced by tensor product of line bundles. -/
abbrev groupLaw : RelativeGroupLaw K J.designation.toBase :=
  J.represents.relativeGroupLaw (P := algEquivZeroGroupCut M.toBase s)

/-- The scheme-theoretic Frobenius twist of the representing Jacobian. -/
abbrev FrobeniusTwist := SchemeFrobenius.Twist p J.designation.toBase

abbrev twistToBase : J.FrobeniusTwist p ⟶ Spec (CommRingCat.of K) :=
  SchemeFrobenius.toBase p J.designation.toBase

def twistedZero : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (J.twistToBase p) :=
  SchemeFrobenius.twistedSection p J.designation.toBase
    ⟨J.designation.zeroSection, J.designation.zeroSection_toBase⟩

abbrev relativeFrobenius : J.designation.P ⟶ J.FrobeniusTwist p :=
  SchemeFrobenius.relative p J.designation.toBase

/-- Actual V, independently constructed by faithfully flat descent. -/
def verschiebung : J.FrobeniusTwist p ⟶ J.designation.P :=
  PerfectFieldVerschiebung.verschiebung p J.designation.toBase J.groupLaw
    (J.represents.relativeGroupLaw_isCommutative (P := algEquivZeroGroupCut M.toBase s))

theorem frobenius_verschiebung :
    J.relativeFrobenius p ≫ J.verschiebung p = J.groupLaw.schemeNsmul p :=
  PerfectFieldVerschiebung.frobenius_verschiebung p J.designation.toBase J.groupLaw
    (J.represents.relativeGroupLaw_isCommutative (P := algEquivZeroGroupCut M.toBase s))

theorem verschiebung_frobenius :
    J.verschiebung p ≫ J.relativeFrobenius p =
      (SchemeFrobenius.twistLaw p J.designation.toBase J.groupLaw).schemeNsmul p :=
  PerfectFieldVerschiebung.verschiebung_frobenius p J.designation.toBase J.groupLaw
    (J.represents.relativeGroupLaw_isCommutative (P := algEquivZeroGroupCut M.toBase s))

theorem verschiebung_over : J.verschiebung p ≫ J.designation.toBase = J.twistToBase p :=
  PerfectFieldVerschiebung.verschiebung_over p J.designation.toBase J.groupLaw
    (J.represents.relativeGroupLaw_isCommutative (P := algEquivZeroGroupCut M.toBase s))

theorem verschiebung_unique (v : J.FrobeniusTwist p ⟶ J.designation.P)
    (hv : J.relativeFrobenius p ≫ v = J.groupLaw.schemeNsmul p) :
    v = J.verschiebung p :=
  PerfectFieldVerschiebung.verschiebung_unique p J.designation.toBase J.groupLaw
    (J.represents.relativeGroupLaw_isCommutative (P := algEquivZeroGroupCut M.toBase s)) v hv

theorem frobenius_zero :
    J.designation.zeroSection ≫ J.relativeFrobenius p = (J.twistedZero p).1 :=
  SchemeFrobenius.section_relative p J.designation.toBase
    ⟨J.designation.zeroSection, J.designation.zeroSection_toBase⟩

theorem verschiebung_zero :
    (J.twistedZero p).1 ≫ J.verschiebung p = J.designation.zeroSection := by
  rw [← J.frobenius_zero p, Category.assoc, J.frobenius_verschiebung p]
  have hzero : (J.groupLaw.one (𝟙 (Spec (CommRingCat.of K)))).1 =
      J.designation.zeroSection := by
    rw [groupLaw, J.represents.relativeGroupLaw_one (P := algEquivZeroGroupCut M.toBase s)]
  rw [← hzero, ← SchemeFrobenius.nsmul_point, J.groupLaw.nsmul_unit]

/-- The actual maximal-ideal cotangent space at zero on the twisted scheme. -/
abbrev TwistedCotangent := PointedCotangent.Cotangent (J.twistToBase p) (J.twistedZero p)

variable (V : Type u) [AddCommGroup V] [Module K V]
  [Module Kᵐᵒᵖ V] [IsCentralScalar K V]

abbrev TwistedInfinitesimalPoints := TangentPoints (J.twistToBase p) (J.twistedZero p).1 V

def twistedCotangentPointsEquiv :
    (J.TwistedCotangent p →ₗ[K] V) ≃ J.TwistedInfinitesimalPoints p V :=
  PointedCotangent.pointsEquiv (J.twistToBase p) (J.twistedZero p) V

variable {V}

def verschiebungInfinitesimalPoint (t : J.TwistedInfinitesimalPoints p V) :
    J.InfinitesimalPoints V :=
  PointedCotangent.mapPoint (J.twistToBase p) (J.twistedZero p)
    (z := ⟨J.designation.zeroSection, J.designation.zeroSection_toBase⟩)
    (J.verschiebung p) (J.verschiebung_over p) (J.verschiebung_zero p) t

/-- The true differential V*: Cot(J) → Cot(J^(p)), with the twist explicit. -/
def verschiebungCotangent : J.Cotangent →ₗ[K] J.TwistedCotangent p :=
  PointedCotangent.differential (J.twistToBase p) (J.twistedZero p)
    (z := ⟨J.designation.zeroSection, J.designation.zeroSection_toBase⟩)
    (J.verschiebung p) (J.verschiebung_over p) (J.verschiebung_zero p)

theorem verschiebungCotangent_action (l : J.TwistedCotangent p →ₗ[K] V) :
    J.cotangentPointsEquiv V (l ∘ₗ J.verschiebungCotangent p) =
      J.verschiebungInfinitesimalPoint p (J.twistedCotangentPointsEquiv p V l) :=
  PointedCotangent.differential_action (J.twistToBase p) (J.twistedZero p)
    (z := ⟨J.designation.zeroSection, J.designation.zeroSection_toBase⟩)
    (J.verschiebung p) (J.verschiebung_over p) (J.verschiebung_zero p) l

end SupersingularCurves.Geometry.Jacobian
