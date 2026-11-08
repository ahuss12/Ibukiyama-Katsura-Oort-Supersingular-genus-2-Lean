/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.AbelianTateGalois
import Definitions.Def_AlgebraicGeometry_RiemannForm

/-! # Comparing the two actual point presentations of the Tate module -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SupersingularCurves.Geometry.AbelianTate
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open RelativeGroupLaw
open scoped CategoryTheory.MonObj

variable {K : Type} [Field K] {g h : ℕ}

private theorem ofUnitPt_mul (A : AbelianVariety K g)
    (x y : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) A.group.X.hom) :
    RiemannForm.ofUnitPt A.group.X.hom ((GroupScheme.law A.group).mul _ x y) =
      (GroupScheme.law A.group).mul _
        (RiemannForm.ofUnitPt A.group.X.hom x)
        (RiemannForm.ofUnitPt A.group.X.hom y) := by
  let t := Spec.map (CommRingCat.ofHom (algebraMap K K))
  have ht : (𝟙 (Spec (CommRingCat.of K))) ≫ 𝟙 _ = t := by
    exact (Category.id_comp _).trans (RiemannForm.specMap_algebraMap_self.symm)
  have h := (GroupScheme.law A.group).mul_natural (𝟙 _) t (𝟙 _) ht x y
  have he (z : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) A.group.X.hom) :
      schemeHomOverComp (𝟙 _) ht z = RiemannForm.ofUnitPt A.group.X.hom z :=
    Subtype.ext (Category.id_comp _)
  simpa only [he] using h

/-- The usual categorical group-scheme points and the relative-law algebraic
points are the same additive group, including the group operations. -/
def pointsGeometricEquiv (A : AbelianVariety K g) :
    A.AdditivePoints ≃+ GeometricPoints A K where
  toFun x := AlgPoints.ofPoint
    (RiemannForm.ofUnitPt A.group.X.hom (overHomToSchemeHomOver x.toMul))
  invFun x := Additive.ofMul (schemeHomOverToOverHom
    (RiemannForm.toUnitPt A.group.X.hom (AlgPoints.toPoint x)))
  left_inv x := by
    change Additive.ofMul (schemeHomOverToOverHom
      (RiemannForm.toUnitPt _ (RiemannForm.ofUnitPt _ (overHomToSchemeHomOver x.toMul)))) = x
    rw [RiemannForm.toUnitPt_ofUnitPt, schemeHomOverToOverHom_overHomToSchemeHomOver]
    rfl
  right_inv x := by
    apply AlgPoints.toPoint_injective
    change RiemannForm.ofUnitPt _ (overHomToSchemeHomOver (schemeHomOverToOverHom
      (RiemannForm.toUnitPt _ (AlgPoints.toPoint x)))) = _
    rw [overHomToSchemeHomOver_schemeHomOverToOverHom, RiemannForm.ofUnitPt_toUnitPt]
  map_add' x y := by
    apply AlgPoints.toPoint_injective
    change RiemannForm.ofUnitPt _ (overHomToSchemeHomOver (x.toMul * y.toMul)) =
      (GroupScheme.law A.group).mul _
        (RiemannForm.ofUnitPt _ (overHomToSchemeHomOver x.toMul))
        (RiemannForm.ofUnitPt _ (overHomToSchemeHomOver y.toMul))
    rw [← ofUnitPt_mul]
    congr 1

/-- The point comparison is pointwise the same underlying scheme morphism. -/
@[simp] theorem pointsGeometricEquiv_toPoint (A : AbelianVariety K g)
    (x : A.AdditivePoints) :
    (AlgPoints.toPoint (pointsGeometricEquiv A x)).1 = x.toMul.left := rfl

/-- Pointwise passage to the inverse limit gives an integral Tate equivalence. -/
def integralGeometricEquiv (ℓ : ℕ) [Fact ℓ.Prime] (A : AbelianVariety K g) :
    Integral ℓ A ≃ₗ[ℤ_[ℓ]] GeometricIntegral ℓ A K where
  toFun x := ⟨fun n => pointsGeometricEquiv A (x.1 n), fun n =>
    ⟨by rw [← map_zsmul, TateModule.torsion, map_zero],
      by rw [← map_zsmul, TateModule.compat]⟩⟩
  invFun x := ⟨fun n => (pointsGeometricEquiv A).symm (x.1 n), fun n =>
    ⟨by rw [← map_zsmul, TateModule.torsion, map_zero],
      by rw [← map_zsmul, TateModule.compat]⟩⟩
  left_inv x := Subtype.ext (funext fun n => (pointsGeometricEquiv A).symm_apply_apply _)
  right_inv x := Subtype.ext (funext fun n => (pointsGeometricEquiv A).apply_symm_apply _)
  map_add' x y := Subtype.ext (funext fun n => (pointsGeometricEquiv A).map_add _ _)
  map_smul' a x := Subtype.ext (funext fun n => map_zsmul (pointsGeometricEquiv A) _ _)

@[simp] theorem integralGeometricEquiv_apply (ℓ : ℕ) [Fact ℓ.Prime]
    (A : AbelianVariety K g) (x : Integral ℓ A) (n : ℕ) :
    (integralGeometricEquiv ℓ A x).1 n = pointsGeometricEquiv A (x.1 n) := rfl

end SupersingularCurves.Geometry.AbelianTate
