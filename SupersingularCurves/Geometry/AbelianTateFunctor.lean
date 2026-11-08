/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.AbelianTateModule
import SupersingularCurves.Geometry.ScalarFrobeniusTateQuotientDescent

/-! # Functoriality and actual multiplication on Tate modules -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SupersingularCurves.Geometry.AbelianTate
open CategoryTheory AlgebraicGeometry GoodReductionJacobian NeronModelInfra ScalarFrobeniusTate
open scoped TensorProduct
variable {K : Type} [Field K] {g h j : ℕ}
variable (ℓ : ℕ) [Fact ℓ.Prime]

@[simp] theorem integralMap_id (A : AbelianVariety K g) :
    integralMap ℓ (𝟙 A.group) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext n
  change Additive.ofMul ((x.1 n).toMul ≫ 𝟙 A.group.X) = x.1 n
  rw [Category.comp_id]
  rfl

@[simp] theorem integralMap_comp {A : AbelianVariety K g} {B : AbelianVariety K h}
    {C : AbelianVariety K j} (f : A.group ⟶ B.group) (q : B.group ⟶ C.group) :
    integralMap ℓ (f ≫ q) = (integralMap ℓ q).comp (integralMap ℓ f) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext n
  change Additive.ofMul ((x.1 n).toMul ≫ (f.hom.hom ≫ q.hom.hom)) =
    Additive.ofMul (((x.1 n).toMul ≫ f.hom.hom) ≫ q.hom.hom)
  rw [Category.assoc]

/-- Multiplication on the actual abelian variety induces literal scalar multiplication. -/
@[simp] theorem integralMap_multiplication (A : AbelianVariety K g) (m : ℕ) :
    integralMap ℓ (multiplication A m) = (m : ℤ_[ℓ]) • LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext n
  change pointsMap (multiplication A m) (x.1 n) = (((m : ℤ_[ℓ]) • x).1 n)
  rw [TateModule.natCast_padicInt_smul_apply, natCast_zsmul]
  change Additive.ofMul ((x.1 n).toMul ≫ (multiplication A m).hom.hom) =
    Additive.ofMul ((x.1 n).toMul ^ m)
  apply congrArg Additive.ofMul
  apply Over.OverMorphism.ext
  have H := congrArg Subtype.val (GroupScheme.nsmul_eq_pow A.group (𝟙 _) m (x.1 n).toMul)
  rw [SchemeFrobenius.nsmul_point] at H
  exact H

@[simp] theorem rationalMap_id (A : AbelianVariety K g) :
    rationalMap ℓ (𝟙 A.group) = LinearMap.id := by
  simp only [rationalMap, integralMap_id, LinearMap.baseChange_id]

@[simp] theorem rationalMap_comp {A : AbelianVariety K g} {B : AbelianVariety K h}
    {C : AbelianVariety K j} (f : A.group ⟶ B.group) (q : B.group ⟶ C.group) :
    rationalMap ℓ (f ≫ q) = (rationalMap ℓ q).comp (rationalMap ℓ f) := by
  simp only [rationalMap, integralMap_comp, LinearMap.baseChange_comp]

@[simp] theorem rationalMap_multiplication (A : AbelianVariety K g) (m : ℕ) :
    rationalMap ℓ (multiplication A m) = (m : ℚ_[ℓ]) • LinearMap.id := by
  rw [rationalMap, integralMap_multiplication, LinearMap.baseChange_smul,
    LinearMap.baseChange_id]
  apply LinearMap.ext
  intro x
  change (m : ℤ_[ℓ]) • x = (m : ℚ_[ℓ]) • x
  simpa only [map_natCast] using (IsScalarTower.algebraMap_smul ℚ_[ℓ] (m : ℤ_[ℓ]) x).symm

/-- Actual mutually inverse isogenies up to [n] induce inverse rational Tate maps. -/
def rationalEquivOfQuasiInverse {A : AbelianVariety K g} {B : AbelianVariety K h}
    (f : A.group ⟶ B.group) (q : B.group ⟶ A.group) (n : ℕ) (hn : n ≠ 0)
    (hf : f ≫ q = multiplication A n) (hq : q ≫ f = multiplication B n) :
    Rational ℓ A ≃ₗ[ℚ_[ℓ]] Rational ℓ B :=
  LinearEquiv.ofLinear (rationalMap ℓ f) ((n : ℚ_[ℓ])⁻¹ • rationalMap ℓ q)
    (by
      apply LinearMap.ext
      intro x
      change rationalMap ℓ f ((n : ℚ_[ℓ])⁻¹ • rationalMap ℓ q x) = x
      rw [map_smul, ← LinearMap.comp_apply, ← rationalMap_comp, hq,
        rationalMap_multiplication, LinearMap.smul_apply, LinearMap.id_apply,
        smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn), one_smul])
    (by rw [LinearMap.smul_comp, ← rationalMap_comp, hf,
      rationalMap_multiplication, smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn), one_smul])

@[simp] theorem rationalEquivOfQuasiInverse_apply
    {A : AbelianVariety K g} {B : AbelianVariety K h}
    (f : A.group ⟶ B.group) (q : B.group ⟶ A.group) (n : ℕ) (hn : n ≠ 0)
    (hf : f ≫ q = multiplication A n) (hq : q ≫ f = multiplication B n)
    (x : Rational ℓ A) :
    rationalEquivOfQuasiInverse ℓ f q n hn hf hq x = rationalMap ℓ f x := rfl

/-- The actual quotient map is invertible on rational Tate modules whenever its
finite subgroup is killed by a positive integer. -/
def quotientRationalEquiv {A : AbelianVariety K g} {H : FiniteSubgroup A}
    (D : Quotient A H) (n : ℕ) (hn : n ≠ 0)
    (hk : H.inclusion ≫ (GroupScheme.law A.group).schemeNsmul n =
      (H.inclusion ≫ A.group.X.hom) ≫ ((GroupScheme.law A.group).one (𝟙 _)).1) :
    Rational ℓ A ≃ₗ[ℚ_[ℓ]] Rational ℓ D.variety :=
  rationalEquivOfQuasiInverse ℓ D.map (D.multiplicationFactor n hk) n hn
    (D.map_multiplicationFactor n hk) (D.multiplicationFactor_map n hk)

end SupersingularCurves.Geometry.AbelianTate
