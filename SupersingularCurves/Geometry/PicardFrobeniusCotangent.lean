/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusCechComparison
import SupersingularCurves.Geometry.VerschiebungNaturality

/-!
# Relative Frobenius on arbitrary represented Picard cotangents

The actual Picard pullback differential is compared with the actual relative
Frobenius map on Čech cohomology for every Picard representation. In particular
the comparison can be applied again on the actual Frobenius twist.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.PicardCohomology
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian InfinitesimalPicard SchemeFrobenius
open scoped TensorProduct
open P2MW.S_AlgebraicCurve_CurveModel_finrank_cotangentSpace_zeroSection_eq_genusFF_of_representsRelSubPic

variable (p : ℕ) [Fact p.Prime]
variable {K : Type u} [Field K] [CharP K p]
variable {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of K)}
variable {s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c}
variable {D : RelativePic0Designation K c}
variable (h : RepresentsRelSubPic c s (algEquivZeroCut c s) D)

/-- The differential of actual curve-Frobenius Picard pullback. -/
def frobeniusCotangent : Cotangent D →ₗ[K] Cotangent (twistDesignation p D) :=
  pullbackCotangent (twistRepresents p h) h (relative p c)
    (relative_toBase p c) (section_relative p c s)

variable (𝒱 : C.TwoAffineOpenCover)
variable {W : Type u} [AddCommGroup W] [Module K W]
  [Module Kᵐᵒᵖ W] [IsCentralScalar K W]

/-- The comparison holds for every square-zero coefficient module and uses
the actual pulled-back Poincare deformation. -/
theorem frobeniusCotangent_cochain (l : Cotangent (twistDesignation p D) →ₗ[K] W) :
    cotangentCechLinearEquiv h 𝒱 W (l ∘ₗ frobeniusCotangent p h) =
      (cechPullback p c 𝒱).rTensor W
        (cotangentCechLinearEquiv (twistRepresents p h) (twistedCover p c 𝒱) W l) := by
  change cotangentCechEquiv h 𝒱 W
    (l ∘ₗ pullbackCotangent (twistRepresents p h) h (relative p c)
      (relative_toBase p c) (section_relative p c s)) = _
  rw [cotangentCechEquiv_pullback]
  exact deformationCechEquiv_pullbackDeformation
    (relative p c) (relative_toBase p c) (section_relative p c s)
    𝒱 (twistedCover p c 𝒱) (relative_preimage_U0 p c 𝒱).ge
    (relative_preimage_U1 p c 𝒱).ge W
    (P2mTJ.defOf (twistRepresents p h)
      (PointedCotangent.pointsEquiv _ _ W l))

/-- The tangent version of the same actual Picard pullback comparison. -/
theorem tangentCechEquiv_frobeniusCotangent
    (l : Module.Dual K (Cotangent (twistDesignation p D))) :
    tangentCechEquiv h 𝒱 (l ∘ₗ frobeniusCotangent p h) =
      cechPullback p c 𝒱
        (tangentCechEquiv (twistRepresents p h) (twistedCover p c 𝒱) l) := by
  have he := congrArg (TensorProduct.rid K (CechH1 c 𝒱))
    (frobeniusCotangent_cochain p h 𝒱 l)
  refine he.trans ?_
  change _ = cechPullback p c 𝒱
    (TensorProduct.rid K _ (cotangentCechLinearEquiv
      (twistRepresents p h) (twistedCover p c 𝒱) K l))
  generalize cotangentCechLinearEquiv (twistRepresents p h)
    (twistedCover p c 𝒱) K l = z
  change TensorProduct.rid K (CechH1 c 𝒱) ((cechPullback p c 𝒱).rTensor K z) =
    cechPullback p c 𝒱 (TensorProduct.rid K _ z)
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x a => simp only [LinearMap.rTensor_tmul, TensorProduct.rid_tmul, map_smul]

/-- If the actual two successive relative Frobenius pullbacks on cohomology
vanish, so does the actual composite Picard cotangent differential. -/
theorem frobeniusCotangent_twice_eq_zero
    (hzero : ∀ q,
      cechPullback p c 𝒱 (cechPullback p (toBase p c) (twistedCover p c 𝒱) q) = 0) :
    frobeniusCotangent p (twistRepresents p h) ∘ₗ frobeniusCotangent p h = 0 := by
  apply LinearMap.ext
  intro x
  apply (Module.forall_dual_apply_eq_zero_iff K _).mp
  intro l
  have hl : (l ∘ₗ frobeniusCotangent p (twistRepresents p h)) ∘ₗ
      frobeniusCotangent p h = 0 := by
    apply (tangentCechEquiv h 𝒱).injective
    rw [map_zero, tangentCechEquiv_frobeniusCotangent,
      tangentCechEquiv_frobeniusCotangent]
    exact hzero _
  exact LinearMap.congr_fun hl x

variable [PerfectField K] [Smooth D.toBase]

/-- Actual Picard pullback is the independently descended Verschiebung for
any smooth representing Picard scheme, including every actual twist. -/
theorem picardPullback_eq_verschiebung :
    (picardPullback p h (twistRepresents p h)).1 =
      PerfectFieldVerschiebung.verschiebung p D.toBase
        (h.relativeGroupLaw (P := algEquivZeroGroupCut c s))
        (h.relativeGroupLaw_isCommutative (P := algEquivZeroGroupCut c s)) :=
  PerfectFieldVerschiebung.verschiebung_unique p D.toBase _ _ _
    (frobenius_picardPullback p h)

end SupersingularCurves.Geometry.PicardCohomology

namespace SupersingularCurves.Geometry.PerfectFieldVerschiebung
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian SchemeFrobenius

variable (p : ℕ) [Fact p.Prime]
variable {K : Type u} [Field K] [CharP K p] [PerfectField K]
variable {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of K)) [Smooth c]
variable (L : RelativeGroupLaw K c) (hc : L.IsCommutative)

local instance : Smooth (toBase p c) :=
  inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd c (baseMap p K)))

/-- Twisting the actual Verschiebung morphism gives the independently
constructed Verschiebung of the twisted group law. -/
theorem map_verschiebung :
    SchemeFrobenius.map p (verschiebung p c L hc) (verschiebung_over p c L hc) =
      verschiebung p (toBase p c) (twistLaw p c L) (twistLaw_commutative p c L hc) := by
  apply verschiebung_unique
  rw [relative_natural, verschiebung_frobenius]

end SupersingularCurves.Geometry.PerfectFieldVerschiebung
