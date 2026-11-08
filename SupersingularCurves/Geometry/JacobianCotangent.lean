/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.JacobianInfinitesimal

/-!
# The actual local cotangent space of the representing Jacobian

The cotangent space is the maximal ideal modulo its square in the local ring
at the zero section. Maps out of it are identified with actual square-zero
points using the local-ring construction, not merely equality of dimensions.
Combining this with Poincare pullback gives the infinitesimal Picard comparison.

For a pointed curve morphism, the cotangent map below is the differential of
the induced morphism of representing Picard schemes. It is constructed from
the universal cotangent-valued infinitesimal point. Naturality proves its
action on every infinitesimal point and its uniqueness.

This does not identify that differential with Cartier or assert the geometric
superspecial/supersingular criteria.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
noncomputable section
universe u v w

namespace SupersingularCurves.Geometry.Jacobian
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open AlgebraicCurve NeronModelInfra GoodReductionJacobian
open InfinitesimalPicard
open P2MW.S_AlgebraicGeometry_Scheme_exists_tangentPoints_equiv_linearMap_cotangentSpace

variable {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]
variable {M : AlgebraicCurve.CurveModel K F}
  {s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase}
variable (J : Jacobian M s)

/-- The stalk at the actual zero section, with its natural local ring. -/
abbrev ZeroStalk :=
  J.designation.P.presheaf.stalk
    (J.designation.zeroSection.base (IsLocalRing.closedPoint K))

/-- The structure morphism gives the scalar action on the zero-section stalk. -/
instance zeroStalkAlgebra : Algebra K J.ZeroStalk :=
  ((J.designation.P.presheaf.germ ⊤
      (J.designation.zeroSection.base (IsLocalRing.closedPoint K)) trivial).hom.comp
    (J.designation.toBase.appTop.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)).toAlgebra

/-- The geometric cotangent space `m / m²` at the identity. -/
abbrev Cotangent := IsLocalRing.CotangentSpace J.ZeroStalk

/-- Evaluation at the rational zero section. -/
abbrev zeroAugmentation : J.ZeroStalk →ₐ[K] K :=
  P2mTJ1.πₐ
    (P2mTJ1.π_algebraMap (fun _ => rfl) J.designation.zeroSection_toBase)

theorem ker_zeroAugmentation :
    RingHom.ker J.zeroAugmentation = IsLocalRing.maximalIdeal J.ZeroStalk :=
  P2mTJ1.ker_πₐ _

/-- Identifies the augmentation-ideal presentation with the maximal-ideal
presentation of the cotangent space. -/
def cotangentAugmentationEquiv :
    J.Cotangent ≃ₗ[K] (RingHom.ker J.zeroAugmentation).Cotangent :=
  P2mTJ1.cotangentCast J.ker_zeroAugmentation.symm

/-- The actual zero-section cotangent space has the curve's genus as dimension.
This dimension statement is separate from the functorial comparisons below. -/
theorem finrank_cotangent [IsAlgClosed K] [IsCurveOver K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K {x}) F) :
    Module.finrank K J.Cotangent = genusFF K F := by
  let hK :=
    P2MW.S_AlgebraicCurve_CurveModel_finrank_cotangentSpace_zeroSection_eq_genusFF_of_representsRelSubPic.P2mTJ.bijective_algebraMap_residueField
      J.designation.toBase J.designation.zeroSection J.designation.zeroSection_toBase
  have hdim := AlgebraicCurve.CurveModel.finrank_cotangentSpace_zeroSection_eq_genusFF_of_representsRelSubPic
    K F hfg M s J.designation J.represents
  rw [P2MW.S_AlgebraicCurve_CurveModel_finrank_cotangentSpace_zeroSection_eq_genusFF_of_representsRelSubPic.P2mTJ.finrank_cotangentSpace_residueField_eq hK]
    at hdim
  exact hdim

variable (V : Type u) [AddCommGroup V] [Module K V]
  [Module Kᵐᵒᵖ V] [IsCentralScalar K V]

/-- Cotangent functionals give square-zero points by the local ring map with
the prescribed first-order part. -/
def cotangentPointsEquiv : (J.Cotangent →ₗ[K] V) ≃ J.InfinitesimalPoints V :=
  (J.cotangentAugmentationEquiv.arrowCongr (LinearEquiv.refl K V)).toEquiv.trans
    (P2mTJ1.pointEquiv (fun _ => rfl)
      (P2mTJ1.π_algebraMap (fun _ => rfl) J.designation.zeroSection_toBase))

variable {V}
variable {W : Type u} [AddCommGroup W] [Module K W]
  [Module Kᵐᵒᵖ W] [IsCentralScalar K W]

/-- The local-ring comparison respects changes of square-zero coefficients. -/
theorem cotangentPointsEquiv_map (φ : V →ₗ[K] W) (l : J.Cotangent →ₗ[K] V) :
    J.cotangentPointsEquiv W (φ ∘ₗ l) = (J.cotangentPointsEquiv V l).map φ := by
  exact P2mTJ1.pointOf_map (x := J.designation.toBase)
    (pt := J.designation.zeroSection) (fun _ => rfl)
    (P2mTJ1.π_algebraMap (fun _ => rfl) J.designation.zeroSection_toBase)
    φ (l ∘ₗ J.cotangentAugmentationEquiv.symm.toLinearMap)

/-- Cotangent functionals classify actual first-order line-bundle deformations
via the local ring and the independently representing Poincare bundle. -/
def cotangentDeformationEquiv :
    (J.Cotangent →ₗ[K] V) ≃ DeformationClasses M.toBase s V :=
  (J.cotangentPointsEquiv V).trans (J.infinitesimalPicardEquiv V)

theorem cotangentDeformationEquiv_map (φ : V →ₗ[K] W) (l : J.Cotangent →ₗ[K] V) :
    J.cotangentDeformationEquiv (φ ∘ₗ l) =
      mapCoefficients φ (J.cotangentDeformationEquiv l) := by
  change J.infinitesimalPicardEquiv W (J.cotangentPointsEquiv W (φ ∘ₗ l)) = _
  rw [J.cotangentPointsEquiv_map, J.infinitesimalPicardEquiv_mapCoefficients]
  rfl

variable {F' : Type w} [Field F'] [Algebra K F']
  {M' : AlgebraicCurve.CurveModel K F'}
  {s' : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M'.toBase}
variable (J' : Jacobian M' s')
variable (f : M'.C ⟶ M.C) (hf : f ≫ M.toBase = M'.toBase)
  (hs : s'.1 ≫ f = s.1)

theorem pullbackInfinitesimalPoint_map (φ : V →ₗ[K] W)
    (t : J.InfinitesimalPoints V) :
    J.pullbackInfinitesimalPoint J' f hf hs (t.map φ) =
      (J.pullbackInfinitesimalPoint J' f hf hs t).map φ := by
  apply TangentPoints.ext
  exact Category.assoc _ _ _

local instance cotangentOppositeModule : Module Kᵐᵒᵖ J.Cotangent :=
  Module.compHom _ (RingEquiv.toOpposite K).symm.toRingHom

local instance cotangentCentralScalar : IsCentralScalar K J.Cotangent :=
  ⟨fun _ _ => rfl⟩

/-- The actual cotangent differential of the Picard pullback morphism,
constructed independently of Cartier from the universal infinitesimal point. -/
def pullbackCotangent : J'.Cotangent →ₗ[K] J.Cotangent :=
  (J'.cotangentPointsEquiv J.Cotangent).symm
    (J.pullbackInfinitesimalPoint J' f hf hs
      (J.cotangentPointsEquiv J.Cotangent LinearMap.id))

/-- Evaluation of the cotangent differential on every test coefficient module. -/
theorem cotangentPointsEquiv_pullback (l : J.Cotangent →ₗ[K] V) :
    J'.cotangentPointsEquiv V (l ∘ₗ J.pullbackCotangent J' f hf hs) =
      J.pullbackInfinitesimalPoint J' f hf hs (J.cotangentPointsEquiv V l) := by
  rw [J'.cotangentPointsEquiv_map]
  change ((J'.cotangentPointsEquiv J.Cotangent)
    ((J'.cotangentPointsEquiv J.Cotangent).symm _)).map l = _
  rw [Equiv.apply_symm_apply, ← J.pullbackInfinitesimalPoint_map,
    ← J.cotangentPointsEquiv_map, LinearMap.comp_id]

/-- The geometric differential commutes with the infinitesimal Picard
comparison; both routes use pullback of actual line bundles. -/
theorem cotangentDeformationEquiv_pullback (l : J.Cotangent →ₗ[K] V) :
    J'.cotangentDeformationEquiv (l ∘ₗ J.pullbackCotangent J' f hf hs) =
      pullbackClasses f hf hs (J.cotangentDeformationEquiv l) := by
  change J'.infinitesimalPicardEquiv V
    (J'.cotangentPointsEquiv V (l ∘ₗ J.pullbackCotangent J' f hf hs)) = _
  rw [J.cotangentPointsEquiv_pullback, J.infinitesimalPicardEquiv_pullback]
  rfl

/-- Already the universal cotangent-valued point determines this differential. -/
theorem pullbackCotangent_unique (d : J'.Cotangent →ₗ[K] J.Cotangent)
    (hd : J'.cotangentPointsEquiv J.Cotangent d =
      J.pullbackInfinitesimalPoint J' f hf hs
        (J.cotangentPointsEquiv J.Cotangent LinearMap.id)) :
    d = J.pullbackCotangent J' f hf hs := by
  apply (J'.cotangentPointsEquiv J.Cotangent).injective
  exact hd.trans (Equiv.apply_symm_apply _ _).symm

end SupersingularCurves.Geometry.Jacobian
