/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.CechCurvePullback
import SupersingularCurves.Geometry.FrobeniusPicardCohomology

/-!
# The actual relative Frobenius on Cech cochains

The source of the cohomology pullback is the actual Frobenius-twisted curve.
No identification of this map with the deformation cocycle is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.SchemeFrobenius
open CategoryTheory AlgebraicGeometry Opposite InfinitesimalPicard

variable (p : ℕ) [Fact p.Prime] {K : Type u} [Field K] [CharP K p]
variable {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))

/-- Relative Frobenius pulls back the base-changed open to the original open. -/
theorem relative_preimage_projection (U : C.Opens) :
    relative p c ⁻¹ᵁ (projection p c ⁻¹ᵁ U) = U := by
  rw [← Scheme.Hom.comp_preimage, relative_projection]
  rfl

variable (𝒱 : C.TwoAffineOpenCover)

theorem relative_preimage_U0 :
    relative p c ⁻¹ᵁ (twistedCover p c 𝒱).U0 = 𝒱.U0 :=
  relative_preimage_projection p c 𝒱.U0

theorem relative_preimage_U1 :
    relative p c ⁻¹ᵁ (twistedCover p c 𝒱).U1 = 𝒱.U1 :=
  relative_preimage_projection p c 𝒱.U1

/-- The actual section pullback on the intersection of the two charts. -/
def cechOverlap :
    ((twistedCover p c 𝒱).structureSheafSections (toBase p c)).M01 →ₗ[K]
      (𝒱.structureSheafSections c).M01 :=
  CechCurvePullback.overlap (relative p c) (relative_toBase p c)
    𝒱 (twistedCover p c 𝒱) (relative_preimage_U0 p c 𝒱).ge
      (relative_preimage_U1 p c 𝒱).ge

/-- The K-linear relative Frobenius pullback, with its twist retained. -/
def cechPullback : CechH1 (toBase p c) (twistedCover p c 𝒱) →ₗ[K] CechH1 c 𝒱 :=
  CechCurvePullback.onH1 (relative p c) (relative_toBase p c)
    𝒱 (twistedCover p c 𝒱) (relative_preimage_U0 p c 𝒱).ge
      (relative_preimage_U1 p c 𝒱).ge

theorem cechPullback_mk
    (a : ((twistedCover p c 𝒱).structureSheafSections (toBase p c)).M01) :
    cechPullback p c 𝒱 (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk (cechOverlap p c 𝒱 a) := rfl

/-- Pulling a section through the projection and relative Frobenius gives
its p-th power in the original section ring. -/
theorem relative_app_projection (U : C.Opens) (a : Γ(C, U)) :
    ((relative p c).appLE (projection p c ⁻¹ᵁ U) U
      (relative_preimage_projection p c U).ge).hom
      (((projection p c).app U).hom a) = a ^ p := by
  rw [← (projection p c).appLE_eq_app, ← CommRingCat.comp_apply,
    Scheme.Hom.appLE_comp_appLE]
  simp only [relative_projection]
  change ((absolute p c).appLE U ((absolute p c) ⁻¹ᵁ U) le_rfl).hom a = a ^ p
  rw [Scheme.Hom.appLE_eq_app]
  change a ^ p ^ 1 = a ^ p
  rw [pow_one]

/-- On sections coming from the projection to the original curve, the actual
relative Frobenius overlap map is the p-th-power map. The domain still carries
the Frobenius-twisted scalar structure. -/
theorem cechOverlap_projection (a : (𝒱.structureSheafSections c).M01) :
    cechOverlap p c 𝒱 (((projection p c).app (𝒱.U0 ⊓ 𝒱.U1)).hom a) = a ^ p := by
  exact relative_app_projection p c (𝒱.U0 ⊓ 𝒱.U1) a

/-- The coefficient is unchanged under the relative, K-linear pullback. -/
theorem cechOverlap_smul_projection (b : K)
    (a : (𝒱.structureSheafSections c).M01) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (toBase p c)
      (projection p c ⁻¹ᵁ (𝒱.U0 ⊓ 𝒱.U1))
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c (𝒱.U0 ⊓ 𝒱.U1)
    cechOverlap p c 𝒱
      (b • (((projection p c).app (𝒱.U0 ⊓ 𝒱.U1)).hom a :
        ((twistedCover p c 𝒱).structureSheafSections (toBase p c)).M01)) =
      b • (a ^ p : (𝒱.structureSheafSections c).M01) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (toBase p c)
    (projection p c ⁻¹ᵁ (𝒱.U0 ⊓ 𝒱.U1))
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c (𝒱.U0 ⊓ 𝒱.U1)
  rw [map_smul, cechOverlap_projection]

/-- The p-th-power formula descends to actual Cech cohomology classes. -/
theorem cechPullback_projection_mk (a : (𝒱.structureSheafSections c).M01) :
    cechPullback p c 𝒱
      (Submodule.Quotient.mk
        (((projection p c).app (𝒱.U0 ⊓ 𝒱.U1)).hom a)) =
      Submodule.Quotient.mk (a ^ p : (𝒱.structureSheafSections c).M01) := by
  rw [cechPullback_mk, cechOverlap_projection]

/-- Scalar multiples retain their coefficient, as required for the relative
Frobenius with source the twisted curve. -/
theorem cechPullback_smul_projection_mk (b : K)
    (a : (𝒱.structureSheafSections c).M01) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (toBase p c)
      (projection p c ⁻¹ᵁ (𝒱.U0 ⊓ 𝒱.U1))
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c (𝒱.U0 ⊓ 𝒱.U1)
    cechPullback p c 𝒱
      (b • Submodule.Quotient.mk
        (((projection p c).app (𝒱.U0 ⊓ 𝒱.U1)).hom a)) =
      b • Submodule.Quotient.mk (a ^ p : (𝒱.structureSheafSections c).M01) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (toBase p c)
    (projection p c ⁻¹ᵁ (𝒱.U0 ⊓ 𝒱.U1))
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c (𝒱.U0 ⊓ 𝒱.U1)
  rw [map_smul, cechPullback_projection_mk]

end SupersingularCurves.Geometry.SchemeFrobenius
