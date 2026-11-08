/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.AbelianTateProduct

/-! # Actual inclusions and projections in the product Tate decomposition -/
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SupersingularCurves.Geometry.AbelianTate
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
variable {K : Type} [Field K] {g h : ℕ}
variable (ℓ : ℕ) [Fact ℓ.Prime] (A : AbelianVariety K g) (B : AbelianVariety K h)

@[simp] theorem integralMap_trivialHom : integralMap ℓ (A.trivialHom B) = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext n
  change Additive.ofMul ((x.1 n).toMul ≫ (1 : A.group.X ⟶ B.group.X)) = 0
  rw [MonObj.comp_one]
  rfl

@[simp] theorem rationalMap_trivialHom : rationalMap ℓ (A.trivialHom B) = 0 := by
  rw [rationalMap, integralMap_trivialHom, LinearMap.baseChange_zero]

@[simp] theorem integralProdEquiv_inl (x : Integral ℓ A) :
    integralProdEquiv ℓ A B (integralMap ℓ (A.prodInl B) x) = (x, 0) := by
  apply Prod.ext
  · rw [integralProdEquiv_fst, ← LinearMap.comp_apply, ← integralMap_comp,
      AbelianVariety.prodInl_fst, integralMap_id, LinearMap.id_apply]
  · rw [integralProdEquiv_snd, ← LinearMap.comp_apply, ← integralMap_comp,
      AbelianVariety.prodInl_snd, integralMap_trivialHom, LinearMap.zero_apply]

@[simp] theorem integralProdEquiv_inr (x : Integral ℓ B) :
    integralProdEquiv ℓ A B (integralMap ℓ (A.prodInr B) x) = (0, x) := by
  apply Prod.ext
  · rw [integralProdEquiv_fst, ← LinearMap.comp_apply, ← integralMap_comp,
      AbelianVariety.prodInr_fst, integralMap_trivialHom, LinearMap.zero_apply]
  · rw [integralProdEquiv_snd, ← LinearMap.comp_apply, ← integralMap_comp,
      AbelianVariety.prodInr_snd, integralMap_id, LinearMap.id_apply]

@[simp] theorem rationalProdEquiv_inl (x : Rational ℓ A) :
    rationalProdEquiv ℓ A B (rationalMap ℓ (A.prodInl B) x) = (x, 0) := by
  apply Prod.ext
  · rw [rationalProdEquiv_fst, ← LinearMap.comp_apply, ← rationalMap_comp,
      AbelianVariety.prodInl_fst, rationalMap_id, LinearMap.id_apply]
  · rw [rationalProdEquiv_snd, ← LinearMap.comp_apply, ← rationalMap_comp,
      AbelianVariety.prodInl_snd, rationalMap_trivialHom, LinearMap.zero_apply]

@[simp] theorem rationalProdEquiv_inr (x : Rational ℓ B) :
    rationalProdEquiv ℓ A B (rationalMap ℓ (A.prodInr B) x) = (0, x) := by
  apply Prod.ext
  · rw [rationalProdEquiv_fst, ← LinearMap.comp_apply, ← rationalMap_comp,
      AbelianVariety.prodInr_fst, rationalMap_trivialHom, LinearMap.zero_apply]
  · rw [rationalProdEquiv_snd, ← LinearMap.comp_apply, ← rationalMap_comp,
      AbelianVariety.prodInr_snd, rationalMap_id, LinearMap.id_apply]

end SupersingularCurves.Geometry.AbelianTate
