/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.CechCurvePullback

/-!
# Naturality of the linear part of a transition function

Changing the overlap ring acts on the curve factor of the square-zero tensor
product. The first-order coefficient then descends by the actual Cech map.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.CechCocycleNaturality
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
open InfinitesimalPicard

variable {K : Type u} [Field K]
variable (V : Type u) [AddCommGroup V] [Module K V]
  [Module Kᵐᵒᵖ V] [IsCentralScalar K V]
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]

/-- Reduction of a square-zero tensor commutes with an overlap algebra map. -/
theorem reduction_map (g : R →ₐ[K] S) (x : TrivSqZeroExt K V ⊗[K] R) :
    Algebra.TensorProduct.lift
      ((Algebra.ofId K S).comp (TrivSqZeroExt.fstHom K K V))
      (AlgHom.id K S) (fun _ _ => Commute.all _ _)
      (Algebra.TensorProduct.map (AlgHom.id K (TrivSqZeroExt K V)) g x) =
    g (Algebra.TensorProduct.lift
      ((Algebra.ofId K R).comp (TrivSqZeroExt.fstHom K K V))
      (AlgHom.id K R) (fun _ _ => Commute.all _ _) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a r =>
    simp only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul,
      AlgHom.id_apply, AlgHom.comp_apply, map_mul]
    change algebraMap K S a.fst * g r = g (algebraMap K R a.fst) * g r
    rw [g.commutes]

/-- Taking the linear part commutes with changing the overlap ring. -/
theorem linearPart_map (g : R →ₐ[K] S) (x : TrivSqZeroExt K V ⊗[K] R) :
    TensorProduct.comm K V S
      (TensorProduct.map (TrivSqZeroExt.sndHom K V) LinearMap.id
        (Algebra.TensorProduct.map (AlgHom.id K (TrivSqZeroExt K V)) g x)) =
    g.toLinearMap.rTensor V (TensorProduct.comm K V R
      (TensorProduct.map (TrivSqZeroExt.sndHom K V) LinearMap.id x)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a r =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.comm_tmul,
      LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply]

variable {X Y : Scheme.{u}}
variable {cX : X ⟶ Spec (CommRingCat.of K)} {cY : Y ⟶ Spec (CommRingCat.of K)}
variable (f : X ⟶ Y) (hf : f ≫ cY = cX)
variable (𝒰 : X.TwoAffineOpenCover) (𝒱 : Y.TwoAffineOpenCover)
variable (h0 : 𝒰.U0 ≤ f ⁻¹ᵁ 𝒱.U0) (h1 : 𝒰.U1 ≤ f ⁻¹ᵁ 𝒱.U1)

/-- The actual curve pullback, viewed on the overlap rings. -/
def overlapAlgHom : (𝒱.cover cY).A01 →ₐ[K] (𝒰.cover cX).A01 :=
  CechCurvePullback.appAlgHom f hf (𝒱.U0 ⊓ 𝒱.U1) (𝒰.U0 ⊓ 𝒰.U1)
    (CechCurvePullback.overlap_le f 𝒰 𝒱 h0 h1)

omit [Module Kᵐᵒᵖ V] [IsCentralScalar K V] in
/-- Quotienting a pulled-back linear coefficient gives the pulled-back class. -/
theorem class_map (x : (𝒱.cover cY).A01 ⊗[K] V) :
    (LinearMap.range (𝒰.cover cX).structureSheaf.cechDiff).mkQ.rTensor V
      ((overlapAlgHom f hf 𝒰 𝒱 h0 h1).toLinearMap.rTensor V x) =
    (CechCurvePullback.onH1 f hf 𝒰 𝒱 h0 h1).rTensor V
      ((LinearMap.range (𝒱.cover cY).structureSheaf.cechDiff).mkQ.rTensor V x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r v => rfl

/-- The specified normalized transition-unit formula is natural under curve
pullback on the overlap factor, with coefficients unchanged. -/
theorem cocycleClass_map (τ : (TrivSqZeroExt K V ⊗[K] (𝒱.cover cY).A01)ˣ) :
    cocycleClass cX 𝒰 V
      (Units.map (Algebra.TensorProduct.map (AlgHom.id K (TrivSqZeroExt K V))
        (overlapAlgHom f hf 𝒰 𝒱 h0 h1)).toMonoidHom τ) =
    (CechCurvePullback.onH1 f hf 𝒰 𝒱 h0 h1).rTensor V
      (cocycleClass cY 𝒱 V τ) := by
  unfold cocycleClass
  change (LinearMap.range (𝒰.cover cX).structureSheaf.cechDiff).mkQ.rTensor V
    (TensorProduct.comm K V (𝒰.cover cX).A01
      (TensorProduct.map (TrivSqZeroExt.sndHom K V) LinearMap.id
        (Algebra.TensorProduct.map (AlgHom.id K (TrivSqZeroExt K V))
          (overlapAlgHom f hf 𝒰 𝒱 h0 h1) (τ : TrivSqZeroExt K V ⊗[K] (𝒱.cover cY).A01)))) = _
  rw [linearPart_map, class_map]

end SupersingularCurves.Geometry.CechCocycleNaturality
