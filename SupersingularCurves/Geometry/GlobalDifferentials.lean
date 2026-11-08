/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.CurveModels
import SupersingularCurves.Geometry.DifferentialTransport
import Theorems.Thm_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_twoAffineOpenCover_mem_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_kaehlerSectionsH0_regularDifferentials_apply_eq_kaehlerToFunctionField
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver

/-!
# Global differentials on the actual smooth proper curve

Global sections are represented by pairs of Kaehler forms on an affine cover,
agreeing on the intersection: the degree-zero Cech kernel. The equivalence with
regular function-field differentials is proved to be restriction to the generic
point followed by the specified function-field isomorphism.
-/
set_option autoImplicit false
noncomputable section
universe u v

namespace SupersingularCurves.Geometry
open CategoryTheory AlgebraicGeometry AlgebraicCurve KaehlerDifferential
variable {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]

/-- Both affine charts are nonempty, so their generic-point restriction is defined. -/
structure DifferentialChart (M : AlgebraicCurve.CurveModel K F) where
  cover : M.C.TwoAffineOpenCover
  [nonempty0 : Nonempty cover.U0]
  [nonempty1 : Nonempty cover.U1]
attribute [instance] DifferentialChart.nonempty0 DifferentialChart.nonempty1

theorem differentialChart_nonempty [IsAlgClosed K] (M : AlgebraicCurve.CurveModel K F) :
    Nonempty (DifferentialChart M) := by
  letI : GeometricallyIntegral M.toBase := geometricallyIntegral_of_isAlgClosed M.toBase
  obtain ⟨V, hP⟩ := SmoothProperCurve.exists_twoAffineOpenCover_mem_of_isAlgClosed
    K M.toBase (genericPoint M.C)
  have h0 : Nonempty V.U0 := ⟨⟨genericPoint M.C, hP⟩⟩
  by_cases h1 : Nonempty V.U1
  · exact ⟨{ cover := V, nonempty0 := h0, nonempty1 := h1 }⟩
  · have he : V.U1 = ⊥ := by
      apply le_antisymm
      · intro x hx
        exact (h1 ⟨⟨x, hx⟩⟩).elim
      · exact bot_le
    have ht : V.U0 = ⊤ := by simpa [he] using V.sup_eq_top
    let W : M.C.TwoAffineOpenCover :=
      { U0 := V.U0
        U1 := V.U0
        isAffineOpen_U0 := V.isAffineOpen_U0
        isAffineOpen_U1 := V.isAffineOpen_U0
        sup_eq_top := by simpa using ht
        isAffineOpen_inf := by simpa using V.isAffineOpen_U0 }
    exact ⟨{ cover := W, nonempty0 := h0, nonempty1 := h0 }⟩

def differentialChart [IsAlgClosed K] (M : AlgebraicCurve.CurveModel K F) :
    DifferentialChart M := Classical.choice (differentialChart_nonempty M)

namespace DifferentialChart
variable {M : AlgebraicCurve.CurveModel K F} (V : DifferentialChart M)

/-- Actual compatible sections of the differential sheaf on the affine cover. -/
abbrev GlobalForms := (V.cover.kaehlerSections M.toBase).H0

variable [PerfectField K]

def schemeRegularEquiv :
    letI := M.functionFieldAlgebra
    V.GlobalForms ≃ₗ[K] regularDifferentials K M.C.functionField :=
  Classical.choose (V.cover.exists_linearEquiv_kaehlerSectionsH0_regularDifferentials_apply_eq_kaehlerToFunctionField M.toBase)

theorem schemeRegularEquiv_generic_restriction (ω : V.GlobalForms) :
    letI := M.functionFieldAlgebra
    (V.schemeRegularEquiv ω : Ω[M.C.functionField⁄K]) =
      kaehlerToFunctionField M.toBase V.cover.U0 ω.val.1 :=
  Classical.choose_spec (V.cover.exists_linearEquiv_kaehlerSectionsH0_regularDifferentials_apply_eq_kaehlerToFunctionField M.toBase) ω

variable [Algebra.EssFiniteType K F] [IsCurveOver K F]

/-- Global forms identified with the original, independently constructed field's
regular forms through generic restriction and differential pullback. -/
def regularEquiv : V.GlobalForms ≃ₗ[K] regularDifferentials K F := by
  letI := M.functionFieldAlgebra
  letI : Algebra.EssFiniteType K M.C.functionField :=
    Algebra.EssFiniteType.of_surjective M.ffAlgEquiv.toAlgHom M.ffAlgEquiv.surjective
  letI : IsCurveOver K M.C.functionField :=
    isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
      M.toBase (RingEquiv.refl _) (fun _ => rfl)
  letI : ∀ v : Place K F, v.DCoordGenerates := dCoordGenerates_of_isCurveOver
  letI : ∀ v : Place K M.C.functionField, v.DCoordGenerates := dCoordGenerates_of_isCurveOver
  exact V.schemeRegularEquiv.trans (regularDifferentialCongr M.ffAlgEquiv.symm)

theorem regularEquiv_generic_restriction (ω : V.GlobalForms) :
    letI := M.functionFieldAlgebra
    (V.regularEquiv ω : Ω[F⁄K]) =
      Differential.pullbackAlong M.ffAlgEquiv.symm.toAlgHom
        (kaehlerToFunctionField M.toBase V.cover.U0 ω.val.1) := by
  letI := M.functionFieldAlgebra
  change Differential.pullbackAlong M.ffAlgEquiv.symm.toAlgHom
    (V.schemeRegularEquiv ω).val = _
  rw [V.schemeRegularEquiv_generic_restriction]

end DifferentialChart
end SupersingularCurves.Geometry
