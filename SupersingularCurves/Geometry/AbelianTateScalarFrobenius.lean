/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.AbelianTateGaloisFunctor
import SupersingularCurves.Geometry.FrobeniusFiniteFieldGroupDescentPoint

/-! # Scalar Frobenius on the genuine geometric Tate representation -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SupersingularCurves.Geometry.AbelianTate
open CategoryTheory AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open RelativeGroupLaw FrobeniusDescent SchemeFrobenius
open scoped TensorProduct
variable {K : Type} [Field K] [IsAlgClosed K]
variable (p : ℕ) [Fact p.Prime] [CharP K p] {g : ℕ}

/-- The actual p²-power automorphism fixing the literal p²-element subfield. -/
def frobeniusSquare : K ≃ₐ[fixedField K p 2] K :=
  { iterateFrobeniusEquiv K p 2 with commutes' := fun a => a.property }

@[simp] theorem frobeniusSquare_apply (a : K) : frobeniusSquare (K := K) p a = a ^ (p ^ 2) := rfl

/-- The geometric Frobenius-square action agrees with actual [p] on points. -/
theorem geometricPoints_frobeniusSquare
    (A : AbelianVariety (fixedField K p 2) g)
    (hA : absolute p A.group.X.hom ≫ absolute p A.group.X.hom =
      (GroupScheme.law A.group).schemeNsmul p)
    (x : GeometricPoints A K) : frobeniusSquare (K := K) p • x = p • x := by
  apply AlgPoints.toPoint_injective
  apply Subtype.ext
  rw [AlgPoints.toPoint_smul_coe, AlgPoints.toPoint_nsmul,
    SchemeFrobenius.nsmul_point, ← hA]
  have hb : Spec.map (CommRingCat.ofHom (frobeniusSquare (K := K) p : K →ₐ[fixedField K p 2] K).toRingHom) =
      baseMap p K ≫ baseMap p K := by
    unfold baseMap
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    ext a
    change a ^ (p ^ 2) = (a ^ p) ^ p
    rw [pow_two, pow_mul]
  have H := Scheme.frobenius_comp (AlgPoints.toPoint x).1 p 1 (Fact.out : p.Prime)
    (Scheme.natCast_eq_zero_ΓSpec (CharP.cast_eq_zero K p)) (globalChar p A.group.X.hom)
  rw [baseMap_eq_absolute p] at H
  change baseMap p K ≫ (AlgPoints.toPoint x).1 =
    (AlgPoints.toPoint x).1 ≫ absolute p A.group.X.hom at H
  rw [hb, Category.assoc, H, ← Category.assoc, H, Category.assoc]

/-- Frobenius acts by the integer p on the actual integral Tate module. -/
theorem integralGaloisRep_frobeniusSquare (ℓ : ℕ) [Fact ℓ.Prime]
    (A : AbelianVariety (fixedField K p 2) g)
    (hA : absolute p A.group.X.hom ≫ absolute p A.group.X.hom =
      (GroupScheme.law A.group).schemeNsmul p) :
    integralGaloisRep ℓ A (frobeniusSquare (K := K) p) = (p : ℤ_[ℓ]) • LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext n
  change frobeniusSquare (K := K) p • x.1 n = (((p : ℤ_[ℓ]) • x).1 n)
  rw [TateModule.natCast_padicInt_smul_apply, natCast_zsmul]
  exact geometricPoints_frobeniusSquare (K := K) p A hA (x.1 n)

/-- The genuine rational geometric Tate representation has scalar p Frobenius. -/
theorem rationalGaloisRep_frobeniusSquare (ℓ : ℕ) [Fact ℓ.Prime]
    (A : AbelianVariety (fixedField K p 2) g)
    (hA : absolute p A.group.X.hom ≫ absolute p A.group.X.hom =
      (GroupScheme.law A.group).schemeNsmul p) :
    rationalGaloisRep ℓ A (frobeniusSquare (K := K) p) = (p : ℚ_[ℓ]) • LinearMap.id := by
  change (integralGaloisRep ℓ A (frobeniusSquare (K := K) p)).baseChange ℚ_[ℓ] = _
  rw [integralGaloisRep_frobeniusSquare (K := K) p ℓ A hA,
    LinearMap.baseChange_smul, LinearMap.baseChange_id]
  apply LinearMap.ext
  intro x
  change (p : ℤ_[ℓ]) • x = (p : ℚ_[ℓ]) • x
  simpa only [map_natCast] using (IsScalarTower.algebraMap_smul ℚ_[ℓ] (p : ℤ_[ℓ]) x).symm

end SupersingularCurves.Geometry.AbelianTate
