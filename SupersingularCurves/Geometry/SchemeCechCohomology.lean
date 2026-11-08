/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.PicardCech
import Theorems.Thm_AlgebraicCurve_nonempty_linearEquiv_cechH0_and_cechH1

/-!
# The specified generic-restriction map on structure-sheaf Cech cohomology

The pinned upstream proof of `nonempty_linearEquiv_cechH0_and_cechH1`
constructs this cochain equivalence, but its public conclusion only records
existence. We expose that construction and its formula on quotient classes.
The affine generic-restriction equivalences and the cokernel bijectivity
lemma are reused from that proof. No choice of an unspecified vector-space
isomorphism is made.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.SchemeCech
open CategoryTheory AlgebraicGeometry AlgebraicCurve Opposite TopologicalSpace
open InfinitesimalPicard
open P2MW.S_AlgebraicCurve_nonempty_linearEquiv_cechH0_and_cechH1.AlgebraicCurve

variable {K : Type u} [Field K] {C : Scheme.{u}}
variable (c : C ⟶ Spec (CommRingCat.of K)) [IsIntegral C]
variable [IsSeparated c] [SmoothOfRelativeDimension 1 c]

/-- The particular affine-section equivalence induced by the generic germ. -/
def affineGermEquiv (U : C.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI := (baseToFunctionField c).toAlgebra
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    Γ(C, U) ≃ₗ[K] lSpaceOn (placesOf c U) (0 : Divisor K C.functionField) :=
  letI := (baseToFunctionField c).toAlgebra
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
  germEquiv c U (range_algebraMap_functionField_eq_iInf_of_isAffineOpen c U hU)

theorem affineGermEquiv_apply (U : C.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (f : Γ(C, U)) :
    (affineGermEquiv c U hU f : C.functionField) = (C.germToFunctionField U).hom f := rfl

variable (𝒱 : C.TwoAffineOpenCover) [Nonempty 𝒱.U0] [Nonempty 𝒱.U1]

local instance overlapNonempty : Nonempty (𝒱.U0 ⊓ 𝒱.U1 : C.Opens) :=
  (nonempty_preirreducible_inter 𝒱.U0.isOpen 𝒱.U1.isOpen
    (Set.nonempty_coe_sort.mp (inferInstance : Nonempty 𝒱.U0))
    (Set.nonempty_coe_sort.mp (inferInstance : Nonempty 𝒱.U1))).to_subtype

/-- Generic restriction of both degree-zero cochains. -/
def degreeZeroGermEquiv :
    letI := (baseToFunctionField c).toAlgebra
    ((𝒱.structureSheafSections c).M0 × (𝒱.structureSheafSections c).M1) ≃ₗ[K]
      (lSpaceOn (placesOf c 𝒱.U0) (0 : Divisor K C.functionField) ×
        lSpaceOn (placesOf c 𝒱.U1) (0 : Divisor K C.functionField)) :=
  letI := (baseToFunctionField c).toAlgebra
  (affineGermEquiv c 𝒱.U0 𝒱.isAffineOpen_U0).prodCongr
    (affineGermEquiv c 𝒱.U1 𝒱.isAffineOpen_U1)

/-- Generic restriction on the overlap, with the proved equality of place sets. -/
def overlapGermEquiv :
    letI := (baseToFunctionField c).toAlgebra
    (𝒱.structureSheafSections c).M01 ≃ₗ[K]
    lSpaceOn (placesOf c 𝒱.U0 ∩ placesOf c 𝒱.U1) (0 : Divisor K C.functionField) :=
  letI := (baseToFunctionField c).toAlgebra
  (affineGermEquiv c (𝒱.U0 ⊓ 𝒱.U1) 𝒱.isAffineOpen_inf).trans
    (LinearEquiv.ofEq _ _ (by rw [placesOf_inf c 𝒱.U0 𝒱.U1]))

theorem overlapGermEquiv_apply (f : (𝒱.structureSheafSections c).M01) :
    (overlapGermEquiv c 𝒱 f : C.functionField) =
      (C.germToFunctionField (𝒱.U0 ⊓ 𝒱.U1)).hom f := rfl

/-- Actual restriction commutes with the Cech differential, including its sign. -/
theorem germ_cechDiff_comm :
    letI := (baseToFunctionField c).toAlgebra
    cechDiff (placesOf c 𝒱.U0) (placesOf c 𝒱.U1) 0 ∘ₗ
        (degreeZeroGermEquiv c 𝒱).toLinearMap =
      (overlapGermEquiv c 𝒱).toLinearMap ∘ₗ (𝒱.structureSheafSections c).cechDiff := by
  letI := (baseToFunctionField c).toAlgebra
  apply LinearMap.ext
  intro p
  apply Subtype.ext
  have lhs : ((cechDiff (placesOf c 𝒱.U0) (placesOf c 𝒱.U1) 0 ∘ₗ
      (degreeZeroGermEquiv c 𝒱).toLinearMap) p : C.functionField) =
      (C.germToFunctionField 𝒱.U1).hom p.2 - (C.germToFunctionField 𝒱.U0).hom p.1 := by
    rw [LinearMap.comp_apply, coe_cechDiff_apply]
    rfl
  rw [lhs]
  change _ = (C.germToFunctionField (𝒱.U0 ⊓ 𝒱.U1)).hom
    ((𝒱.structureSheafSections c).cechDiff p)
  rw [TwoChartCech.Sections.cechDiff_apply, TwoChartCech.Cover.lineBundle_r1_apply,
    TwoChartCech.Cover.lineBundle_r0_apply, Units.val_one, one_mul]
  change _ = (C.germToFunctionField (𝒱.U0 ⊓ 𝒱.U1)).hom
    (((C.presheaf.map (homOfLE inf_le_right).op).hom p.2 : Γ(C, 𝒱.U0 ⊓ 𝒱.U1)) -
      (C.presheaf.map (homOfLE inf_le_left).op).hom p.1)
  rw [map_sub, germToFunctionField_map (C := C) inf_le_right,
    germToFunctionField_map (C := C) inf_le_left]

/-- The Cech comparison is induced by the specified generic-restriction cochain map. -/
def functionFieldCechEquiv :
    letI := (baseToFunctionField c).toAlgebra
    CechH1 c 𝒱 ≃ₗ[K]
    cechH1 (placesOf c 𝒱.U0) (placesOf c 𝒱.U1) (0 : Divisor K C.functionField) :=
  letI := (baseToFunctionField c).toAlgebra
  LinearEquiv.ofBijective
    (TwoChartCech.cokerMap (𝒱.structureSheafSections c).cechDiff
      (cechDiff (placesOf c 𝒱.U0) (placesOf c 𝒱.U1) 0)
      (degreeZeroGermEquiv c 𝒱).toLinearMap (overlapGermEquiv c 𝒱).toLinearMap
      (germ_cechDiff_comm c 𝒱))
    (P2MW.S_AlgebraicCurve_nonempty_linearEquiv_cechH0_and_cechH1.TwoChartCech.cokerMap_bijective_of_bijective
      _ _ _ _ (germ_cechDiff_comm c 𝒱)
      (degreeZeroGermEquiv c 𝒱).surjective (overlapGermEquiv c 𝒱).bijective)

/-- Every overlap section maps to the class of its actual generic germ. -/
theorem functionFieldCechEquiv_mk (f : (𝒱.structureSheafSections c).M01) :
    letI := (baseToFunctionField c).toAlgebra
    functionFieldCechEquiv c 𝒱 (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (overlapGermEquiv c 𝒱 f) := rfl

/-- The representative formula determines the comparison uniquely. -/
theorem functionFieldCechEquiv_unique :
    letI := (baseToFunctionField c).toAlgebra
    ∀ e : CechH1 c 𝒱 →ₗ[K]
      cechH1 (placesOf c 𝒱.U0) (placesOf c 𝒱.U1) (0 : Divisor K C.functionField),
    (∀ f : (𝒱.structureSheafSections c).M01,
      e (Submodule.Quotient.mk f) = Submodule.Quotient.mk (overlapGermEquiv c 𝒱 f)) →
    e = (functionFieldCechEquiv c 𝒱).toLinearMap := by
  letI := (baseToFunctionField c).toAlgebra
  intro e he
  apply LinearMap.ext
  intro q
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  exact he f

end SupersingularCurves.Geometry.SchemeCech
