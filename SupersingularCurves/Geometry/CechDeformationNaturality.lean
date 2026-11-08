/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.CechGluingPullback
import SupersingularCurves.Geometry.CechCurveBaseChange
import SupersingularCurves.Geometry.CechCocycleNaturality

/-!
# Curve-morphism naturality of the actual deformation cocycle

The geometric pullback of an invertible sheaf pulls back its normalized
transition unit. Taking its linear coefficient and quotienting by actual
coboundaries therefore gives the structure-sheaf Cech pullback constructed
independently from the scheme morphism's maps on sections.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.InfinitesimalPicard
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open AlgebraicGeometry.RelPicard
open scoped TensorProduct
open P2MW.S_AlgebraicGeometry_RelPicard_exists_trivialModDeformations_map_H1_tensor_natural
open CechCurveBaseChange

variable {K : Type u} [Field K] {X Y : Scheme.{u}}
variable {cX : X ⟶ Spec (CommRingCat.of K)} {cY : Y ⟶ Spec (CommRingCat.of K)}
variable {sX : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) cX}
  {sY : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) cY}
variable (f : X ⟶ Y) (hf : f ≫ cY = cX) (hs : sX.1 ≫ f = sY.1)
variable (𝒰 : X.TwoAffineOpenCover) (𝒱 : Y.TwoAffineOpenCover)
variable (h0 : 𝒰.U0 ≤ f ⁻¹ᵁ 𝒱.U0) (h1 : 𝒰.U1 ≤ f ⁻¹ᵁ 𝒱.U1)
variable (W : Type u) [AddCommGroup W] [Module K W]
  [Module Kᵐᵒᵖ W] [IsCentralScalar K W]

/-- The normalized transition unit of a deformation pulls back by the actual
curve morphism on its overlap factor. -/
theorem normalizedTransition_pullback (L : TrivialModDeformations cY sY W)
    (τ : (TrivSqZeroExt K W ⊗[K] (𝒱.cover cY).A01)ˣ)
    (hτ : τ ∈ P2mTJ2.Nset 𝒱 cY W L.1.L) :
    Units.map (Algebra.TensorProduct.map (AlgHom.id K (TrivSqZeroExt K W))
      (overlapAlgHom f hf 𝒰 𝒱 h0 h1)).toMonoidHom τ ∈
        P2mTJ2.Nset 𝒰 cX W (pullbackDeformation f hf hs L).1.L := by
  let A := TrivSqZeroExt K W
  let fA := curveChange f hf (Scheme.TwoAffineOpenCover.specMap K A)
  let hA := curveChange_snd f hf (Scheme.TwoAffineOpenCover.specMap K A)
  let 𝒰A := 𝒰.pullback cX A
  let 𝒱A := 𝒱.pullback cY A
  let h0A := baseChange_le0 f hf 𝒰 𝒱 h0 A
  let h1A := baseChange_le1 f hf 𝒰 𝒱 h1 A
  let τ' := Units.map (Algebra.TensorProduct.map (AlgHom.id K A)
    (overlapAlgHom f hf 𝒰 𝒱 h0 h1)).toMonoidHom τ
  constructor
  · change Algebra.TensorProduct.lift _ _ _
      (Algebra.TensorProduct.map (AlgHom.id K A) (overlapAlgHom f hf 𝒰 𝒱 h0 h1)
        (τ : A ⊗[K] (𝒱.cover cY).A01)) = 1
    rw [CechCocycleNaturality.reduction_map, hτ.1, map_one]
  · have hg := CechGluingPullback.gluedBy_pullback fA hA 𝒰A 𝒱A h0A h1A
      L.1.isInvertible (Units.mapEquiv (P2mTJ2.E01 𝒱 cY A).toMulEquiv τ) hτ.2
    have hu : Units.map (overlapAlgHom fA hA 𝒰A 𝒱A h0A h1A).toMonoidHom
        (Units.mapEquiv (P2mTJ2.E01 𝒱 cY A).toMulEquiv τ) =
        Units.mapEquiv (P2mTJ2.E01 𝒰 cX A).toMulEquiv τ' := by
      apply Units.ext
      exact curveChange_E01 f hf 𝒰 𝒱 h0 h1 A (τ : A ⊗[K] (𝒱.cover cY).A01)
    change P2mTJ2.GluedBy 𝒰A (pullback.snd cX (Scheme.TwoAffineOpenCover.specMap K A))
      ((Scheme.Modules.pullback fA).obj L.1.L)
      (Units.map (overlapAlgHom fA hA 𝒰A 𝒱A h0A h1A).toMonoidHom
        (Units.mapEquiv (P2mTJ2.E01 𝒱 cY A).toMulEquiv τ)) at hg
    rw [hu] at hg
    exact hg

/-- The actual deformation cocycle commutes with pullback along a pointed
curve morphism, for every square-zero coefficient module. -/
theorem deformationCechEquiv_pullbackDeformation (L : TrivialModDeformations cY sY W) :
    deformationCechEquiv cX sX 𝒰 W
        (deformationClass cX sX W (pullbackDeformation f hf hs L)) =
      (CechCurvePullback.onH1 f hf 𝒰 𝒱 h0 h1).rTensor W
        (deformationCechEquiv cY sY 𝒱 W (deformationClass cY sY W L)) := by
  obtain ⟨τ, hτ⟩ := P2mTJ2.nonempty_Nset 𝒱 cY sY W L
  rw [deformationCechEquiv_of_cocycle _ _ _ _ _ _
    (normalizedTransition_pullback f hf hs 𝒰 𝒱 h0 h1 W L τ hτ),
    deformationCechEquiv_of_cocycle _ _ _ _ L τ hτ]
  exact CechCocycleNaturality.cocycleClass_map W f hf 𝒰 𝒱 h0 h1 τ

/-- Naturality on all deformation classes, independent of representatives. -/
theorem deformationCechEquiv_pullback (q : DeformationClasses cY sY W) :
    deformationCechEquiv cX sX 𝒰 W (pullbackClasses f hf hs q) =
      (CechCurvePullback.onH1 f hf 𝒰 𝒱 h0 h1).rTensor W
        (deformationCechEquiv cY sY 𝒱 W q) := by
  induction q using Quotient.inductionOn with
  | h L => exact deformationCechEquiv_pullbackDeformation f hf hs 𝒰 𝒱 h0 h1 W L

end SupersingularCurves.Geometry.InfinitesimalPicard
