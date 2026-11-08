/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.ResiduePairing

/-!
# Residue duality for the actual smooth proper curve

All function-field, residue and constants hypotheses of the residue-normalized
duality are supplied from the actual scheme over an algebraically closed field.
In particular, the residue theorem is proved, not supplied by the caller.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.SchemeResidue
open CategoryTheory AlgebraicGeometry AlgebraicCurve KaehlerDifferential
open InfinitesimalPicard

variable {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}}
variable (c : C ⟶ Spec (CommRingCat.of K)) [IsIntegral C]
variable [IsProper c] [SmoothOfRelativeDimension 1 c]

/-- The actual local residues of the scheme's function field, constructed by
completion and coefficient fields in the pinned upstream development. -/
@[instance_reducible] def residueData :
    letI := (baseToFunctionField c).toAlgebra
    HasCanonicalLocalResidueKStar K C.functionField := by
  letI := (baseToFunctionField c).toAlgebra
  letI : IsCurveOver K C.functionField :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one c
      (RingEquiv.refl _) (fun _ => rfl)
  exact ResidueDuality.canonicalResidues

/-- The explicit trace-of-local-residues sum with the specified residue data. -/
def residueSum :
    letI := (baseToFunctionField c).toAlgebra
    Ω[C.functionField⁄K] → (Place K C.functionField → C.functionField) → K :=
  letI := (baseToFunctionField c).toAlgebra
  letI := residueData c
  fun ω a => ∑ᶠ v, kaehlerResidueTerm ω a v

variable (𝒱 : C.TwoAffineOpenCover)

/-- Actual regular forms and dual repartition cohomology, with every geometric
and residue hypothesis discharged from the curve and its base field. -/
def regularDualEquiv :
    letI := (baseToFunctionField c).toAlgebra
    regularDifferentials K C.functionField ≃ₗ[K]
      Module.Dual K (SchemeCech.RepartitionH1 c) := by
  letI := (baseToFunctionField c).toAlgebra
  letI : IsCurveOver K C.functionField :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one c
      (RingEquiv.refl _) (fun _ => rfl)
  letI : Algebra.EssFiniteType K C.functionField := essFiniteType_functionField c
  letI : HasCanonicalDivisor (K := K) (F := C.functionField) :=
    hasCanonicalDivisor_of_isCurveOver
  letI : ∀ v : Place K C.functionField, v.DCoordGenerates :=
    dCoordGenerates_of_isCurveOver
  letI := residueData c
  exact ResidueDuality.regularDualEquiv (SchemeCech.constantsAreBase c 𝒱)
    ResidueDuality.residueTheorem_of_isAlgClosed

/-- The actual curve comparison has the residue formula on every repartition. -/
theorem regularDualEquiv_mk :
    letI := (baseToFunctionField c).toAlgebra
    ∀ (ω : regularDifferentials K C.functionField)
      (a : ↥(repartitions K C.functionField)),
    regularDualEquiv c 𝒱 ω (Submodule.Quotient.mk a) =
      residueSum c ω a := by
  letI := (baseToFunctionField c).toAlgebra
  letI : IsCurveOver K C.functionField :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one c
      (RingEquiv.refl _) (fun _ => rfl)
  letI : Algebra.EssFiniteType K C.functionField := essFiniteType_functionField c
  letI : HasCanonicalDivisor (K := K) (F := C.functionField) :=
    hasCanonicalDivisor_of_isCurveOver
  letI : ∀ v : Place K C.functionField, v.DCoordGenerates :=
    dCoordGenerates_of_isCurveOver
  letI := residueData c
  intro ω a
  exact ResidueDuality.regularDualEquiv_mk (SchemeCech.constantsAreBase c 𝒱)
    ResidueDuality.residueTheorem_of_isAlgClosed ω a

/-- Compatibility on actual overlap sections of the curve's structure sheaf. -/
theorem regularDualEquiv_cech_mk :
    letI := (baseToFunctionField c).toAlgebra
    letI := SchemeCech.properCover_overlap_nonempty c 𝒱
    ∀ (ω : regularDifferentials K C.functionField)
      (f : (𝒱.structureSheafSections c).M01),
    regularDualEquiv c 𝒱 ω
        (SchemeCech.toRepartition c 𝒱 (Submodule.Quotient.mk f)) =
      residueSum c ω (extendOffChart K (placesOf c 𝒱.U0)
        ((C.germToFunctionField (𝒱.U0 ⊓ 𝒱.U1)).hom f)) := by
  letI := (baseToFunctionField c).toAlgebra
  letI := SchemeCech.properCover_overlap_nonempty c 𝒱
  intro ω f
  rw [SchemeCech.toRepartition_mk, regularDualEquiv_mk]

/-- The representative residue formula determines the comparison uniquely. -/
theorem regularDualEquiv_unique :
    letI := (baseToFunctionField c).toAlgebra
    ∀ e : regularDifferentials K C.functionField →ₗ[K]
      Module.Dual K (SchemeCech.RepartitionH1 c),
    (∀ (ω : regularDifferentials K C.functionField)
      (a : ↥(repartitions K C.functionField)),
      e ω (Submodule.Quotient.mk a) = residueSum c ω a) →
    e = (regularDualEquiv c 𝒱).toLinearMap := by
  letI := (baseToFunctionField c).toAlgebra
  intro e he
  apply LinearMap.ext
  intro ω
  apply LinearMap.ext
  intro q
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  exact (he ω a).trans (regularDualEquiv_mk c 𝒱 ω a).symm

end SupersingularCurves.Geometry.SchemeResidue
