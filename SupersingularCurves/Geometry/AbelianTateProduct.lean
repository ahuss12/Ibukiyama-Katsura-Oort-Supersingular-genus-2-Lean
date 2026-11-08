/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.AbelianVarietyProductMaps
import SupersingularCurves.Geometry.AbelianTateFunctor
import Mathlib.LinearAlgebra.TensorProduct.Prod

/-! # Tate modules of genuine binary products -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SupersingularCurves.Geometry.AbelianTate
open CategoryTheory AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open scoped TensorProduct
variable {K : Type} [Field K] {g h : ℕ}
variable (ℓ : ℕ) [Fact ℓ.Prime] (A : AbelianVariety K g) (B : AbelianVariety K h)

/-- The actual compatible torsion sequences of a product decompose componentwise. -/
def integralProdEquiv : Integral ℓ (A.prod B) ≃ₗ[ℤ_[ℓ]] Integral ℓ A × Integral ℓ B where
  toFun x := (integralMap ℓ (A.prodFst B) x, integralMap ℓ (A.prodSnd B) x)
  invFun x := ⟨fun n => (A.additivePointsProdEquiv B).symm (x.1.1 n, x.2.1 n), fun n =>
    ⟨by
      rw [← map_zsmul]
      change (A.additivePointsProdEquiv B).symm
        (((ℓ ^ n : ℕ) : ℤ) • x.1.1 n, ((ℓ ^ n : ℕ) : ℤ) • x.2.1 n) = 0
      rw [TateModule.torsion, TateModule.torsion]
      exact map_zero _,
     by
      rw [← map_zsmul]
      change (A.additivePointsProdEquiv B).symm
        ((ℓ : ℤ) • x.1.1 (n + 1), (ℓ : ℤ) • x.2.1 (n + 1)) = _
      rw [TateModule.compat, TateModule.compat]⟩⟩
  left_inv x := by
    apply Subtype.ext
    funext n
    exact (A.additivePointsProdEquiv B).symm_apply_apply (x.1 n)
  right_inv x := by
    apply Prod.ext
    · apply Subtype.ext
      funext n
      exact congrArg Prod.fst ((A.additivePointsProdEquiv B).apply_symm_apply (x.1.1 n, x.2.1 n))
    · apply Subtype.ext
      funext n
      exact congrArg Prod.snd ((A.additivePointsProdEquiv B).apply_symm_apply (x.1.1 n, x.2.1 n))
  map_add' x y := Prod.ext (map_add _ _ _) (map_add _ _ _)
  map_smul' a x := Prod.ext (map_smul _ _ _) (map_smul _ _ _)

/-- Rational Tate decomposition, by scalar extension of the genuine integral one. -/
def rationalProdEquiv : Rational ℓ (A.prod B) ≃ₗ[ℚ_[ℓ]] Rational ℓ A × Rational ℓ B :=
  (LinearEquiv.baseChange ℤ_[ℓ] ℚ_[ℓ] _ _ (integralProdEquiv ℓ A B)).trans
    (TensorProduct.prodRight ℤ_[ℓ] ℚ_[ℓ] ℚ_[ℓ] (Integral ℓ A) (Integral ℓ B))

@[simp] theorem integralProdEquiv_fst (x : Integral ℓ (A.prod B)) :
    (integralProdEquiv ℓ A B x).1 = integralMap ℓ (A.prodFst B) x := rfl

@[simp] theorem integralProdEquiv_snd (x : Integral ℓ (A.prod B)) :
    (integralProdEquiv ℓ A B x).2 = integralMap ℓ (A.prodSnd B) x := rfl

@[simp] theorem rationalProdEquiv_fst (x : Rational ℓ (A.prod B)) :
    (rationalProdEquiv ℓ A B x).1 = rationalMap ℓ (A.prodFst B) x := by
  induction x using TensorProduct.induction_on with
  | zero =>
      change ((rationalProdEquiv ℓ A B).toLinearMap 0).1 = rationalMap ℓ (A.prodFst B) 0
      simp only [map_zero, Prod.fst_zero, Prod.snd_zero]
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, Prod.fst_add, hx, hy]

@[simp] theorem rationalProdEquiv_snd (x : Rational ℓ (A.prod B)) :
    (rationalProdEquiv ℓ A B x).2 = rationalMap ℓ (A.prodSnd B) x := by
  induction x using TensorProduct.induction_on with
  | zero =>
      change ((rationalProdEquiv ℓ A B).toLinearMap 0).2 = rationalMap ℓ (A.prodSnd B) 0
      simp only [map_zero, Prod.fst_zero, Prod.snd_zero]
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, Prod.snd_add, hx, hy]

end SupersingularCurves.Geometry.AbelianTate
