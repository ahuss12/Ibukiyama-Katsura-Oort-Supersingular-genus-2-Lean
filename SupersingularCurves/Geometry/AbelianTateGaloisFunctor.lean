/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.AbelianTateGalois
import SupersingularCurves.Geometry.AbelianTateFunctor

/-! # Actual abelian morphisms intertwine the geometric Tate actions -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SupersingularCurves.Geometry.AbelianTate
open CategoryTheory AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open RelativeGroupLaw FrobeniusFactorGroup ScalarFrobeniusTate
open scoped TensorProduct
variable {k K : Type} [Field k] [Field K] [Algebra k K] {g h j : ℕ}

/-- The map on actual geometric field-valued points induced by a group-scheme morphism. -/
def geometricPointsMap {A : AbelianVariety k g} {B : AbelianVariety k h}
    (f : A.group ⟶ B.group) : GeometricPoints A K →+ GeometricPoints B K :=
  AddMonoidHom.mk' (fun x => AlgPoints.ofPoint
    (pointMap (underlyingScheme.map f) f.hom.hom.w (AlgPoints.toPoint x))) (by
      intro x y
      apply AlgPoints.toPoint_injective
      exact pointMap_mul f _ _ _)

/-- The actual geometric point map is Galois equivariant. -/
theorem geometricPointsMap_smul {A : AbelianVariety k g} {B : AbelianVariety k h}
    (f : A.group ⟶ B.group) (σ : K ≃ₐ[k] K) (x : GeometricPoints A K) :
    geometricPointsMap f (σ • x) = σ • geometricPointsMap f x := by
  apply AlgPoints.toPoint_injective
  apply Subtype.ext
  exact Category.assoc _ _ _

/-- The actual homomorphism on compatible geometric torsion systems. -/
def geometricIntegralMap (ℓ : ℕ) [Fact ℓ.Prime]
    {A : AbelianVariety k g} {B : AbelianVariety k h} (f : A.group ⟶ B.group) :
    GeometricIntegral ℓ A K →ₗ[ℤ_[ℓ]] GeometricIntegral ℓ B K where
  toFun x := ⟨fun n => geometricPointsMap f (x.1 n), fun n =>
    ⟨by rw [← map_zsmul, TateModule.torsion, map_zero],
      by rw [← map_zsmul, TateModule.compat]⟩⟩
  map_add' x y := Subtype.ext (funext fun n => (geometricPointsMap f).map_add _ _)
  map_smul' a x := Subtype.ext (funext fun n => (geometricPointsMap f).map_zsmul _ _)

/-- Scalar extension of the actual map on geometric integral Tate modules. -/
def geometricRationalMap (ℓ : ℕ) [Fact ℓ.Prime]
    {A : AbelianVariety k g} {B : AbelianVariety k h} (f : A.group ⟶ B.group) :
    GeometricRational ℓ A K →ₗ[ℚ_[ℓ]] GeometricRational ℓ B K :=
  (geometricIntegralMap ℓ f).baseChange ℚ_[ℓ]

/-- Every actual morphism intertwines the actual integral Galois actions. -/
theorem geometricIntegralMap_galois (ℓ : ℕ) [Fact ℓ.Prime]
    {A : AbelianVariety k g} {B : AbelianVariety k h} (f : A.group ⟶ B.group)
    (σ : K ≃ₐ[k] K) :
    (geometricIntegralMap ℓ f).comp (integralGaloisRep ℓ A σ) =
      (integralGaloisRep ℓ B σ).comp (geometricIntegralMap ℓ f) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext n
  exact geometricPointsMap_smul f σ (x.1 n)

/-- Every actual morphism intertwines the actual rational Galois actions. -/
theorem geometricRationalMap_galois (ℓ : ℕ) [Fact ℓ.Prime]
    {A : AbelianVariety k g} {B : AbelianVariety k h} (f : A.group ⟶ B.group)
    (σ : K ≃ₐ[k] K) :
    (geometricRationalMap ℓ f).comp (rationalGaloisRep ℓ A σ) =
      (rationalGaloisRep ℓ B σ).comp (geometricRationalMap ℓ f) := by
  change ((geometricIntegralMap ℓ f).baseChange ℚ_[ℓ]).comp
      ((integralGaloisRep ℓ A σ).baseChange ℚ_[ℓ]) =
    ((integralGaloisRep ℓ B σ).baseChange ℚ_[ℓ]).comp
      ((geometricIntegralMap ℓ f).baseChange ℚ_[ℓ])
  rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, geometricIntegralMap_galois]

end SupersingularCurves.Geometry.AbelianTate
