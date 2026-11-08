/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.PicardFrobeniusCotangent
import SupersingularCurves.Geometry.FrobeniusCechSquare
import SupersingularCurves.Geometry.CartierCechSquare

/-!
# The actual twice-iterated Jacobian Verschiebung differential

The second map is the actual Frobenius base change of the independently
constructed Verschiebung morphism. Both Picard comparisons are proved using
the normalized Poincare cocycle on the corresponding actual curve twist.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

namespace SupersingularCurves.Geometry.Jacobian
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open AlgebraicCurve NeronModelInfra GoodReductionJacobian SchemeFrobenius
open InfinitesimalPicard

variable {K : Type u} [Field K]
variable {F : Type v} [Field F] [Algebra K F]
variable {M : CurveModel K F}
  {s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase}
variable (J : Jacobian M s)
variable (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectField K]

local instance : Smooth J.designation.toBase :=
  SmoothOfRelativeDimension.smooth (genusFF K F) J.designation.toBase

local instance : Smooth (J.twistToBase p) :=
  inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd
    J.designation.toBase (baseMap p K)))

local instance : Smooth (twistDesignation p J.designation).toBase :=
  inferInstanceAs (Smooth (J.twistToBase p))

/-- The designated identity on the second actual Frobenius twist. -/
def twiceTwistedZero :
    SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (toBase p (J.twistToBase p)) :=
  twistedSection p (J.twistToBase p) (J.twistedZero p)

/-- The actual base change of V preserves the two designated identity sections. -/
theorem map_verschiebung_zero :
    (J.twiceTwistedZero p).1 ≫ map p (J.verschiebung p) (J.verschiebung_over p) =
      (J.twistedZero p).1 := by
  rw [twiceTwistedZero, ← section_relative, Category.assoc, relative_natural,
    ← Category.assoc, J.verschiebung_zero p, J.frobenius_zero p]

/-- The independently constructed cotangent differential of the actual
base change of V, with both target twists retained. -/
def twistedVerschiebungCotangent :
    J.TwistedCotangent p →ₗ[K]
      PointedCotangent.Cotangent (toBase p (J.twistToBase p)) (J.twiceTwistedZero p) :=
  PointedCotangent.differential (toBase p (J.twistToBase p)) (J.twiceTwistedZero p)
    (map p (J.verschiebung p) (J.verschiebung_over p))
    (map_toBase p (J.verschiebung p) (J.verschiebung_over p))
    (J.map_verschiebung_zero p)

/-- The second actual Picard pullback equals the actual base change of V. -/
theorem twistedPicardPullback_eq_map_verschiebung :
    (picardPullback p (J.twistedPicardRepresentation p)
      (twistRepresents p (J.twistedPicardRepresentation p))).1 =
        map p (J.verschiebung p) (J.verschiebung_over p) := by
  rw [PicardCohomology.picardPullback_eq_verschiebung]
  simpa only [twistedPicardRepresentation, twistRepresents_groupLaw,
    twistDesignation_toBase, verschiebung, groupLaw] using
    (PerfectFieldVerschiebung.map_verschiebung p J.designation.toBase
    J.groupLaw (J.represents.relativeGroupLaw_isCommutative
      (P := algEquivZeroGroupCut M.toBase s))).symm

/-- Equality of the actual local-ring cotangent maps at the second twist. -/
theorem frobeniusCotangent_twist_eq_twistedVerschiebungCotangent :
    PicardCohomology.frobeniusCotangent p (J.twistedPicardRepresentation p) =
      J.twistedVerschiebungCotangent p := by
  unfold PicardCohomology.frobeniusCotangent PicardCohomology.pullbackCotangent
    twistedVerschiebungCotangent
  congr 1
  exact J.twistedPicardPullback_eq_map_verschiebung p

/-- Equality at the first twist uses the independently proved Picard/V identity. -/
theorem frobeniusCotangent_eq_verschiebungCotangent :
    PicardCohomology.frobeniusCotangent p J.represents = J.verschiebungCotangent p :=
  J.frobeniusPicardPullbackCotangent_eq_verschiebungCotangent p

/-- Square-zero actual absolute Frobenius on Čech H1 forces the actual
twice-iterated Verschiebung cotangent differential to vanish. -/
theorem verschiebungCotangent_twice_eq_zero_of_absoluteCech_square_zero
    (𝒱 : M.C.TwoAffineOpenCover)
    (hzero : ∀ q : CechH1 M.toBase 𝒱,
      absoluteCech p M.toBase 𝒱 (absoluteCech p M.toBase 𝒱 q) = 0) :
    J.twistedVerschiebungCotangent p ∘ₗ J.verschiebungCotangent p = 0 := by
  rw [← J.frobeniusCotangent_twist_eq_twistedVerschiebungCotangent p,
    ← J.frobeniusCotangent_eq_verschiebungCotangent p]
  exact PicardCohomology.frobeniusCotangent_twice_eq_zero p J.represents 𝒱
    (cechPullback_twice_eq_zero_of_absoluteCech_square_zero p M.toBase 𝒱 hzero)

/-- The vanishing conclusion for the actual composite scheme morphism
`V^(p) ≫ V`, expressed as its actual maximal-ideal cotangent differential. -/
theorem differential_verschiebung_twice_eq_zero_of_absoluteCech_square_zero
    (𝒱 : M.C.TwoAffineOpenCover)
    (hzero : ∀ q : CechH1 M.toBase 𝒱,
      absoluteCech p M.toBase 𝒱 (absoluteCech p M.toBase 𝒱 q) = 0) :
    PointedCotangent.differential
      (toBase p (J.twistToBase p)) (J.twiceTwistedZero p)
      (z := ⟨J.designation.zeroSection, J.designation.zeroSection_toBase⟩)
      (map p (J.verschiebung p) (J.verschiebung_over p) ≫ J.verschiebung p)
      (by rw [Category.assoc, J.verschiebung_over p, map_toBase])
      (by rw [← Category.assoc, J.map_verschiebung_zero p, J.verschiebung_zero p]) = 0 := by
  rw [PointedCotangent.differential_comp]
  exact J.verschiebungCotangent_twice_eq_zero_of_absoluteCech_square_zero p 𝒱 hzero

variable [IsAlgClosed K] [Algebra.EssFiniteType K F] [IsCurveOver K F]
variable (V : DifferentialChart M)
variable (x : F) [FiniteDimensional (IntermediateField.adjoin K {x}) F]

/-- Cartier squared zero implies vanishing of the actual successive
Verschiebung cotangent maps, with their actual Frobenius twists retained. -/
theorem verschiebungCotangent_twice_eq_zero_of_globalCartier_square_zero
    (hzero : ∀ ω : V.GlobalForms, V.globalCartier p x (V.globalCartier p x ω) = 0) :
    J.twistedVerschiebungCotangent p ∘ₗ J.verschiebungCotangent p = 0 :=
  J.verschiebungCotangent_twice_eq_zero_of_absoluteCech_square_zero p V.cover
    (V.absoluteCech_square_zero_of_globalCartier_square_zero p x hzero)

/-- Cartier squared zero kills the differential of the actual composite
scheme morphism `V^(p) ≫ V`. No scheme-projection cotangent normalization is
assumed: both actual Picard pullbacks are compared on Čech cohomology. -/
theorem differential_verschiebung_twice_eq_zero_of_globalCartier_square_zero
    (hzero : ∀ ω : V.GlobalForms, V.globalCartier p x (V.globalCartier p x ω) = 0) :
    PointedCotangent.differential
      (toBase p (J.twistToBase p)) (J.twiceTwistedZero p)
      (z := ⟨J.designation.zeroSection, J.designation.zeroSection_toBase⟩)
      (map p (J.verschiebung p) (J.verschiebung_over p) ≫ J.verschiebung p)
      (by rw [Category.assoc, J.verschiebung_over p, map_toBase])
      (by rw [← Category.assoc, J.map_verschiebung_zero p, J.verschiebung_zero p]) = 0 :=
  J.differential_verschiebung_twice_eq_zero_of_absoluteCech_square_zero p V.cover
    (V.absoluteCech_square_zero_of_globalCartier_square_zero p x hzero)

end SupersingularCurves.Geometry.Jacobian
