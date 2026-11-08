/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.CechCurvePullback

/-!
# Curve pullback and the actual affine base-change charts

The maps on overlap sections are the maps induced by the scheme morphism.
Their compatibility with the tensor-product chart isomorphisms follows from
the two projections of the actual fiber product.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.CechCurveBaseChange
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.TwoAffineOpenCover
open scoped TensorProduct
open P2MW.S_AlgebraicGeometry_RelPicard_exists_trivialModDeformations_map_H1_tensor_natural

variable {K : Type u} [CommRing K] {X Y : Scheme.{u}}
variable {cX : X ⟶ Spec (CommRingCat.of K)} {cY : Y ⟶ Spec (CommRingCat.of K)}
variable (f : X ⟶ Y) (hf : f ≫ cY = cX)
variable (𝒰 : X.TwoAffineOpenCover) (𝒱 : Y.TwoAffineOpenCover)
variable (h0 : 𝒰.U0 ≤ f ⁻¹ᵁ 𝒱.U0) (h1 : 𝒰.U1 ≤ f ⁻¹ᵁ 𝒱.U1)

/-- The algebra map on the actual overlap rings. -/
def overlapAlgHom : (𝒱.cover cY).A01 →ₐ[K] (𝒰.cover cX).A01 :=
  CechCurvePullback.appAlgHom f hf (𝒱.U0 ⊓ 𝒱.U1) (𝒰.U0 ⊓ 𝒰.U1)
    (CechCurvePullback.overlap_le f 𝒰 𝒱 h0 h1)

theorem overlapAlgHom_toLinearMap :
    (overlapAlgHom f hf 𝒰 𝒱 h0 h1).toLinearMap =
      CechCurvePullback.overlap f hf 𝒰 𝒱 h0 h1 := rfl

/-- The curve-change map commutes with the projection to the curve. -/
theorem curveChange_fst {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) :
    RelPicard.curveChange f hf t ≫ pullback.fst cY t = pullback.fst cX t ≫ f := by
  simp only [RelPicard.curveChange, pullback.lift_fst]

variable (A : Type u) [CommRing A] [Algebra K A]

include h0 in
theorem baseChange_le0 :
    (𝒰.pullback cX A).U0 ≤
      RelPicard.curveChange f hf (specMap K A) ⁻¹ᵁ (𝒱.pullback cY A).U0 := by
  change pullback.fst cX (specMap K A) ⁻¹ᵁ 𝒰.U0 ≤
    RelPicard.curveChange f hf (specMap K A) ⁻¹ᵁ
      (pullback.fst cY (specMap K A) ⁻¹ᵁ 𝒱.U0)
  rw [← Scheme.Hom.comp_preimage, curveChange_fst, Scheme.Hom.comp_preimage]
  exact fun _ hx => h0 hx

include h1 in
theorem baseChange_le1 :
    (𝒰.pullback cX A).U1 ≤
      RelPicard.curveChange f hf (specMap K A) ⁻¹ᵁ (𝒱.pullback cY A).U1 := by
  change pullback.fst cX (specMap K A) ⁻¹ᵁ 𝒰.U1 ≤
    RelPicard.curveChange f hf (specMap K A) ⁻¹ᵁ
      (pullback.fst cY (specMap K A) ⁻¹ᵁ 𝒱.U1)
  rw [← Scheme.Hom.comp_preimage, curveChange_fst, Scheme.Hom.comp_preimage]
  exact fun _ hx => h1 hx

local notation "fA" => RelPicard.curveChange f hf (specMap K A)
local notation "hA" => RelPicard.curveChange_snd f hf (specMap K A)
local notation "gA" => overlapAlgHom fA hA (𝒰.pullback cX A) (𝒱.pullback cY A)
  (baseChange_le0 f hf 𝒰 𝒱 h0 A) (baseChange_le1 f hf 𝒰 𝒱 h1 A)

/-- Pullback of functions from the curve commutes with curve base change. -/
theorem curveChange_fst_app (s : (𝒱.cover cY).A01) :
    gA (((pullback.fst cY (specMap K A)).app (𝒱.U0 ⊓ 𝒱.U1)).hom s) =
      ((pullback.fst cX (specMap K A)).app (𝒰.U0 ⊓ 𝒰.U1)).hom
        (overlapAlgHom f hf 𝒰 𝒱 h0 h1 s) := by
  change ((fA).appLE _ _ _).hom
    (((pullback.fst cY (specMap K A)).app (𝒱.U0 ⊓ 𝒱.U1)).hom s) =
      ((pullback.fst cX (specMap K A)).app (𝒰.U0 ⊓ 𝒰.U1)).hom
        ((f.appLE _ _ _).hom s)
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply]
  congr 1
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE,
    Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
  exact congrArg CommRingCat.Hom.hom
    (P2mTJ2.appLE_congrHom (curveChange_fst f hf (specMap K A)) _ _ _ _)

/-- The actual map of basechanged overlap rings is the tensor product of the
identity on the coefficient ring with the original curve pullback. -/
theorem curveChange_E01 (z : A ⊗[K] (𝒱.cover cY).A01) :
    gA (P2mTJ2.E01 𝒱 cY A z) =
      P2mTJ2.E01 𝒰 cX A
        (Algebra.TensorProduct.map (AlgHom.id K A) (overlapAlgHom f hf 𝒰 𝒱 h0 h1) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a s =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      P2mTJ2.tmul_eq_mul A a s,
      P2mTJ2.tmul_eq_mul A a (overlapAlgHom f hf 𝒰 𝒱 h0 h1 s),
      map_mul, map_mul, map_mul, P2mTJ2.E01_tmul_one, P2mTJ2.E01_tmul_one,
      AlgHom.commutes, P2mTJ2.E01_tmul, P2mTJ2.E01_tmul, curveChange_fst_app]

/-- The chart compatibility also holds for invertible transition functions. -/
theorem curveChange_E01_units (τ : (A ⊗[K] (𝒱.cover cY).A01)ˣ) :
    Units.map (gA).toMonoidHom (Units.mapEquiv (P2mTJ2.E01 𝒱 cY A) τ) =
      Units.mapEquiv (P2mTJ2.E01 𝒰 cX A)
        (Units.map (Algebra.TensorProduct.map (AlgHom.id K A)
          (overlapAlgHom f hf 𝒰 𝒱 h0 h1)).toMonoidHom τ) := by
  apply Units.ext
  exact curveChange_E01 f hf 𝒰 𝒱 h0 h1 A (τ : A ⊗[K] (𝒱.cover cY).A01)

end SupersingularCurves.Geometry.CechCurveBaseChange
