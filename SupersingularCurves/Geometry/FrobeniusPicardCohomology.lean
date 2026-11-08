/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.PicardCotangentCech
import SupersingularCurves.Geometry.FrobeniusPicardComparison

/-!
# Verschiebung and the actual Frobenius-pulled-back deformation cocycle

The cotangent/dual-Cech-H1 comparisons are instantiated for the genuine
Jacobian and its actual Frobenius twist. The independently constructed V acts
on cotangent functionals by the normalized Cech class of the curve-Frobenius
pullback of the actual Poincare deformation.

The comparison with regular differential forms, the residue-pairing Cartier
identity, and the geometric superspecial/supersingular criteria remain further
theorems. In particular, the cohomology action below is recorded on actual
line-bundle deformations; no unproved Cech cochain formula is asserted.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

namespace SupersingularCurves.Geometry
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open AlgebraicCurve NeronModelInfra GoodReductionJacobian InfinitesimalPicard
open scoped TensorProduct
open P2MW.S_AlgebraicGeometry_RelPicard_exists_trivialModDeformations_map_H1_tensor_natural
open P2MW.S_AlgebraicCurve_CurveModel_finrank_cotangentSpace_zeroSection_eq_genusFF_of_representsRelSubPic

namespace SchemeFrobenius
variable (p : ℕ) [Fact p.Prime] {K : Type u} [Field K] [CharP K p]
variable {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))

/-- The actual base-changed affine cover on the Frobenius-twisted curve. -/
def twistedCover (𝒱 : C.TwoAffineOpenCover) : (Twist p c).TwoAffineOpenCover := by
  letI : Algebra K K := (frobenius K p).toAlgebra
  exact 𝒱.pullback c K

end SchemeFrobenius

namespace Jacobian
variable {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]
variable {M : CurveModel K F}
  {s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase}
variable (J : Jacobian M s) (𝒱 : M.C.TwoAffineOpenCover)

/-- The actual Jacobian cotangent space is dual Cech H1, with the comparison
fixed by the local-ring and normalized Poincare-cocycle constructions. -/
def cotangentDualCechEquiv :
    J.Cotangent ≃ₗ[K] Module.Dual K (CechH1 M.toBase 𝒱) :=
  PicardCohomology.cotangentDualCechEquiv J.represents 𝒱

/-- The corresponding tangent comparison, retaining its actual cocycle map. -/
def tangentCechEquiv : Module.Dual K J.Cotangent ≃ₗ[K] CechH1 M.toBase 𝒱 :=
  PicardCohomology.tangentCechEquiv J.represents 𝒱

theorem cotangentDualCechEquiv_tangent (x : J.Cotangent) (l : Module.Dual K J.Cotangent) :
    J.cotangentDualCechEquiv 𝒱 x (J.tangentCechEquiv 𝒱 l) = l x :=
  PicardCohomology.cotangentDualCechEquiv_tangent J.represents 𝒱 x l

variable (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectField K]

/-- The same actual comparison on J^(p), with C^(p) and its base-changed cover. -/
def twistedCotangentDualCechEquiv :
    J.TwistedCotangent p ≃ₗ[K]
      Module.Dual K (CechH1 (SchemeFrobenius.toBase p M.toBase)
        (SchemeFrobenius.twistedCover p M.toBase 𝒱)) := by
  let : LocallyOfFiniteType (SchemeFrobenius.twistDesignation p J.designation).toBase :=
    inferInstanceAs (LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd
      J.designation.toBase (SchemeFrobenius.baseMap p K)))
  exact PicardCohomology.cotangentDualCechEquiv (J.twistedPicardRepresentation p)
    (SchemeFrobenius.twistedCover p M.toBase 𝒱)

variable {V : Type u} [AddCommGroup V] [Module K V]
  [Module Kᵐᵒᵖ V] [IsCentralScalar K V]

/-- The actual Frobenius pullback of the Poincare deformation associated to
a cotangent functional on J^(p). -/
def frobeniusPoincareDeformation (l : J.TwistedCotangent p →ₗ[K] V) :
    TrivialModDeformations M.toBase s V :=
  pullbackDeformation (SchemeFrobenius.relative p M.toBase)
    (SchemeFrobenius.relative_toBase p M.toBase)
    (SchemeFrobenius.section_relative p M.toBase s)
    (P2mTJ.defOf (J.twistedPicardRepresentation p) (J.twistedCotangentPointsEquiv p V l))

/-- V on actual cotangent functionals agrees with the normalized Cech class
of the actual Frobenius-pulled-back Poincare deformation, for every coefficient
module. The V used here is the independently descended scheme morphism. -/
theorem verschiebungCotangent_cech (l : J.TwistedCotangent p →ₗ[K] V) :
    PicardCohomology.cotangentCechLinearEquiv J.represents 𝒱 V
        (l ∘ₗ J.verschiebungCotangent p) =
      deformationCechEquiv M.toBase s 𝒱 V
        (deformationClass M.toBase s V (J.frobeniusPoincareDeformation p l)) := by
  rw [← J.frobeniusPicardPullbackCotangent_eq_verschiebungCotangent p]
  exact PicardCohomology.cotangentCechEquiv_pullback (J.twistedPicardRepresentation p)
    J.represents 𝒱 (SchemeFrobenius.relative p M.toBase)
    (SchemeFrobenius.relative_toBase p M.toBase)
    (SchemeFrobenius.section_relative p M.toBase s) l

/-- The tangent-space version has values in H1 itself. -/
theorem tangentCechEquiv_verschiebung (l : Module.Dual K (J.TwistedCotangent p)) :
    J.tangentCechEquiv 𝒱 (l ∘ₗ J.verschiebungCotangent p) =
      TensorProduct.rid K (CechH1 M.toBase 𝒱)
        (deformationCechEquiv M.toBase s 𝒱 K
          (deformationClass M.toBase s K (J.frobeniusPoincareDeformation p l))) := by
  exact congrArg (TensorProduct.rid K (CechH1 M.toBase 𝒱))
    (J.verschiebungCotangent_cech 𝒱 p l)

/-- The dual comparison evaluates a Frobenius-pulled-back deformation by the
actual V cotangent differential. This is an adjointness statement for the
deformation cocycle, before the remaining comparison with regular forms. -/
theorem cotangentDualCechEquiv_frobeniusDeformation
    (x : J.Cotangent) (l : Module.Dual K (J.TwistedCotangent p)) :
    J.cotangentDualCechEquiv 𝒱 x
      (TensorProduct.rid K (CechH1 M.toBase 𝒱)
        (deformationCechEquiv M.toBase s 𝒱 K
          (deformationClass M.toBase s K (J.frobeniusPoincareDeformation p l)))) =
      l (J.verschiebungCotangent p x) := by
  rw [← J.tangentCechEquiv_verschiebung 𝒱 p l, J.cotangentDualCechEquiv_tangent]
  rfl

end Jacobian
end SupersingularCurves.Geometry
