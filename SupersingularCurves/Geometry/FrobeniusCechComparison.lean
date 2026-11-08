/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.CechDeformationNaturality
import SupersingularCurves.Geometry.FrobeniusCechPullback

/-!
# Jacobian Verschiebung and actual curve Frobenius on Cech cohomology

The Jacobian morphism was constructed independently by descent. Its
cotangent differential is now compared with the actual curve-Frobenius
cochain map, via the normalized Poincare deformation cocycle. The Frobenius
twist is retained throughout. No Cartier adjointness or geometric
superspecial/supersingular classification is assumed or claimed here.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

namespace SupersingularCurves.Geometry.Jacobian
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open AlgebraicCurve NeronModelInfra GoodReductionJacobian InfinitesimalPicard
open scoped TensorProduct
open P2MW.S_AlgebraicCurve_CurveModel_finrank_cotangentSpace_zeroSection_eq_genusFF_of_representsRelSubPic

variable {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]
variable {M : CurveModel K F}
  {s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase}
variable (J : Jacobian M s) (𝒱 : M.C.TwoAffineOpenCover)
variable (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectField K]

/-- The actual tangent/Cech comparison on the Frobenius-twisted Jacobian. -/
def twistedTangentCechEquiv : Module.Dual K (J.TwistedCotangent p) ≃ₗ[K]
    CechH1 (SchemeFrobenius.toBase p M.toBase) (SchemeFrobenius.twistedCover p M.toBase 𝒱) :=
  PicardCohomology.tangentCechEquiv (J.twistedPicardRepresentation p)
    (SchemeFrobenius.twistedCover p M.toBase 𝒱)

variable {V : Type u} [AddCommGroup V] [Module K V]
  [Module Kᵐᵒᵖ V] [IsCentralScalar K V]

/-- On every coefficient module, V on cotangent functionals equals the
actual relative-Frobenius cochain pullback under the normalized comparison. -/
theorem verschiebungCotangent_cochain (l : J.TwistedCotangent p →ₗ[K] V) :
    PicardCohomology.cotangentCechLinearEquiv J.represents 𝒱 V
        (l ∘ₗ J.verschiebungCotangent p) =
      (SchemeFrobenius.cechPullback p M.toBase 𝒱).rTensor V
        (PicardCohomology.cotangentCechLinearEquiv (J.twistedPicardRepresentation p)
          (SchemeFrobenius.twistedCover p M.toBase 𝒱) V l) := by
  rw [J.verschiebungCotangent_cech]
  exact deformationCechEquiv_pullbackDeformation
    (SchemeFrobenius.relative p M.toBase) (SchemeFrobenius.relative_toBase p M.toBase)
    (SchemeFrobenius.section_relative p M.toBase s)
    𝒱 (SchemeFrobenius.twistedCover p M.toBase 𝒱)
    (SchemeFrobenius.relative_preimage_U0 p M.toBase 𝒱).ge
    (SchemeFrobenius.relative_preimage_U1 p M.toBase 𝒱).ge V
    (P2mTJ.defOf (J.twistedPicardRepresentation p) (J.twistedCotangentPointsEquiv p V l))

/-- The tangent action of independently constructed Jacobian Verschiebung
is the actual curve-relative-Frobenius map on H1. -/
theorem tangentCechEquiv_verschiebung_cochain (l : Module.Dual K (J.TwistedCotangent p)) :
    J.tangentCechEquiv 𝒱 (l ∘ₗ J.verschiebungCotangent p) =
      SchemeFrobenius.cechPullback p M.toBase 𝒱 (J.twistedTangentCechEquiv 𝒱 p l) := by
  have h := congrArg (TensorProduct.rid K (CechH1 M.toBase 𝒱))
    (J.verschiebungCotangent_cochain 𝒱 p l)
  refine h.trans ?_
  change _ = SchemeFrobenius.cechPullback p M.toBase 𝒱
    (TensorProduct.rid K _ (PicardCohomology.cotangentCechLinearEquiv
      (J.twistedPicardRepresentation p) (SchemeFrobenius.twistedCover p M.toBase 𝒱) K l))
  generalize PicardCohomology.cotangentCechLinearEquiv (J.twistedPicardRepresentation p)
    (SchemeFrobenius.twistedCover p M.toBase 𝒱) K l = z
  change TensorProduct.rid K (CechH1 M.toBase 𝒱)
    ((SchemeFrobenius.cechPullback p M.toBase 𝒱).rTensor K z) =
      SchemeFrobenius.cechPullback p M.toBase 𝒱
        (TensorProduct.rid K _ z)
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x a =>
    simp only [LinearMap.rTensor_tmul, TensorProduct.rid_tmul, map_smul]

theorem twistedCotangentDualCechEquiv_tangent
    (x : J.TwistedCotangent p) (l : Module.Dual K (J.TwistedCotangent p)) :
    J.twistedCotangentDualCechEquiv 𝒱 p x (J.twistedTangentCechEquiv 𝒱 p l) = l x := by
  let : LocallyOfFiniteType (SchemeFrobenius.twistDesignation p J.designation).toBase :=
    inferInstanceAs (LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd
      J.designation.toBase (SchemeFrobenius.baseMap p K)))
  exact PicardCohomology.cotangentDualCechEquiv_tangent
    (J.twistedPicardRepresentation p) (SchemeFrobenius.twistedCover p M.toBase 𝒱) x l

/-- Adjointness with actual Frobenius on every Cech H1 class, with the
Jacobian cotangent differential and all scalar twists independently fixed. -/
theorem cotangentDualCechEquiv_frobenius_cochain (x : J.Cotangent)
    (q : CechH1 (SchemeFrobenius.toBase p M.toBase)
      (SchemeFrobenius.twistedCover p M.toBase 𝒱)) :
    J.cotangentDualCechEquiv 𝒱 x (SchemeFrobenius.cechPullback p M.toBase 𝒱 q) =
      J.twistedCotangentDualCechEquiv 𝒱 p (J.verschiebungCotangent p x) q := by
  obtain ⟨l, rfl⟩ := (J.twistedTangentCechEquiv 𝒱 p).surjective q
  rw [← J.tangentCechEquiv_verschiebung_cochain 𝒱 p l,
    J.cotangentDualCechEquiv_tangent, J.twistedCotangentDualCechEquiv_tangent]
  rfl

end SupersingularCurves.Geometry.Jacobian
