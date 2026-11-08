/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.ScalarFrobeniusTateHopfSubgroup
import Theorems.Thm_AlgebraicGeometry_finite_schemeHomOver_of_isFinite

/-! # The actual point groups in a finite Hopf presentation -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
universe u
namespace SupersingularCurves.Geometry.ScalarFrobeniusTate
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped CategoryTheory.MonObj
variable {K : Type u} [Field K]

/-- Points with the canonical spectrum-over-spectrum structure map. -/
abbrev FiniteGroupPoints (G : GroupScheme K) :=
  Additive ((Spec (CommRingCat.of K)).asOver (Spec (CommRingCat.of K)) ⟶ G.X)

instance finiteGroupPoints_comm (G : GroupScheme K) [IsCommMonObj G.X] :
    AddCommGroup (FiniteGroupPoints G) := inferInstance

/-- Actual rational points of a finite group scheme form a finite group. -/
instance finiteGroupPoints_finite (G : GroupScheme K) [IsFinite G.X.hom] :
    Finite (FiniteGroupPoints G) := by
  letI : Finite (SchemeHomOver
      ((Spec (CommRingCat.of K)).asOver (Spec (CommRingCat.of K))).hom G.X.hom) :=
    finite_schemeHomOver_of_isFinite G.X.hom K _
  apply Finite.of_injective (fun x : FiniteGroupPoints G =>
    (⟨x.toMul.left, x.toMul.w⟩ : SchemeHomOver
      ((Spec (CommRingCat.of K)).asOver (Spec (CommRingCat.of K))).hom G.X.hom))
  intro x y h
  apply congrArg Additive.ofMul
  apply Over.OverMorphism.ext
  exact congrArg Subtype.val h

/-- The actual Hopf presentation identifies convolution points with the
actual point group, including multiplication. -/
def hopfPointsEquiv {B : Type u} [CommRing B] [HopfAlgebra K B]
    {G : GroupScheme K} (e : hopfGroup (K := K) B ≅ G) :
    WithConv (B →ₐ[K] K) ≃ FiniteGroupPoints G where
  toFun φ := Additive.ofMul ((Spec.mapMulEquiv φ) ≫ e.hom.hom.hom)
  invFun x := Spec.mapMulEquiv.symm (x.toMul ≫ e.inv.hom.hom)
  left_inv φ := by
    apply Spec.mapMulEquiv.injective
    simp only [MulEquiv.apply_symm_apply]
    change ((Spec.mapMulEquiv φ) ≫ e.hom.hom.hom) ≫ e.inv.hom.hom = Spec.mapMulEquiv φ
    rw [Category.assoc]
    have h : e.hom.hom.hom ≫ e.inv.hom.hom = 𝟙 _ :=
      congrArg (fun f => f.hom.hom) e.hom_inv_id
    rw [h]
    apply Over.OverMorphism.ext
    exact Category.comp_id _
  right_inv x := by
    change Additive.ofMul ((Spec.mapMulEquiv (Spec.mapMulEquiv.symm
      (x.toMul ≫ e.inv.hom.hom))) ≫ e.hom.hom.hom) = x
    rw [MulEquiv.apply_symm_apply, Category.assoc]
    have h : e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 _ :=
      congrArg (fun f => f.hom.hom) e.inv_hom_id
    rw [h, Category.comp_id]
    rfl

theorem hopfPointsEquiv_mul {B : Type u} [CommRing B] [HopfAlgebra K B]
    {G : GroupScheme K} (e : hopfGroup (K := K) B ≅ G)
    (φ ψ : WithConv (B →ₐ[K] K)) :
    hopfPointsEquiv e (φ * ψ) = hopfPointsEquiv e φ + hopfPointsEquiv e ψ := by
  change Additive.ofMul ((Spec.mapMulEquiv (φ * ψ)) ≫ e.hom.hom.hom) = _
  rw [map_mul, MonObj.mul_comp]
  rfl

end SupersingularCurves.Geometry.ScalarFrobeniusTate
