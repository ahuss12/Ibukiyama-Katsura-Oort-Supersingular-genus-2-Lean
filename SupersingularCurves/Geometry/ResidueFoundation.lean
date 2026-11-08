/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.CechRepartition
import Theorems.Thm_AlgebraicCurve_residueTheoremK_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_isCurveOver_ratFunc
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalLocalResidueInstanceV2
import Definitions.Def_AlgebraicCurve_WeilOfKaehler

/-!
# Supplying the residue theorem for the actual chosen residue family

The existing `ResidueTheoremK` quantifies over all canonical local-residue
families. We specialize it to exactly the family used in `weilOfKaehler`.
The algebraically closed application supplies a separating rational-function
subfield using the established finite separable extension construction.
This setup adapts the same field-transport argument used upstream in
`RegularDifferentialsFinrank.riemannRoch_and_constantsAreBase`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace SupersingularCurves.Geometry.ResidueDuality
open AlgebraicCurve KaehlerDifferential IntermediateField

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]

/-- The existing local-residue construction by completion and coefficient field. -/
@[instance_reducible] def canonicalResidues [PerfectField K] :
    HasCanonicalLocalResidueKStar K F :=
  AlgebraicCurve.instHasCanonicalLocalResidueKStar

variable [HasCanonicalLocalResidueKStar K F]
variable [HasCanonicalDivisor (K := K) (F := F)]
variable [∀ v : Place K F, v.DCoordGenerates]

/-- The residue theorem for all canonical families applies to the precise
family defining the differential/repartition pairing. -/
theorem residueTheorem_of_K (hRT : ResidueTheoremK K F) : ResidueTheorem K F := by
  intro _ ω hω f
  exact hRT (fun v => HasCanonicalLocalResidueKStar.dataKStar v) hω f

/-- Over an algebraically closed field all separating-extension hypotheses
of the existing residue theorem are supplied, not postulated. -/
theorem residueTheorem_of_isAlgClosed [IsAlgClosed K] [Algebra.EssFiniteType K F] :
    ResidueTheorem K F := by
  classical
  obtain ⟨t, ht, htfd, htsep⟩ :=
    IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  letI := htfd
  letI := htsep
  let e : RatFunc K ≃ₐ[K] K⟮t⟯ := RatFunc.algEquivOfTranscendental t ht
  letI : Algebra (RatFunc K) F :=
    ((algebraMap K⟮t⟯ F).comp e.toAlgHom.toRingHom).toAlgebra
  have hsq : RingHom.comp (algebraMap (RatFunc K) F)
        (e.symm.toRingEquiv : K⟮t⟯ →+* RatFunc K) =
      RingHom.comp (RingEquiv.refl F : F →+* F) (algebraMap K⟮t⟯ F) := by
    refine RingHom.ext fun a => ?_
    show algebraMap K⟮t⟯ F (e (e.symm a)) = algebraMap K⟮t⟯ F a
    rw [e.apply_symm_apply]
  letI : IsScalarTower K (RatFunc K) F :=
    IsScalarTower.of_algebraMap_eq fun a => by
      show algebraMap K F a = algebraMap K⟮t⟯ F (e (algebraMap K (RatFunc K) a))
      rw [e.commutes, ← IsScalarTower.algebraMap_apply]
  letI : FiniteDimensional (RatFunc K) F :=
    Module.Finite.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  letI : Algebra.IsSeparable (RatFunc K) F :=
    Algebra.IsSeparable.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  letI : Algebra.IsIntegral (RatFunc K) F := Algebra.IsIntegral.of_finite (RatFunc K) F
  letI : IsCurveOver K (RatFunc K) := isCurveOver_ratFunc K
  letI : FiniteDimensional (IntermediateField.adjoin K ({RatFunc.X} : Set (RatFunc K)))
      (RatFunc K) := by
    refine Module.Finite.of_surjective
      (Algebra.linearMap (IntermediateField.adjoin K ({RatFunc.X} : Set (RatFunc K)))
        (RatFunc K)) fun y => ?_
    refine ⟨⟨y, ?_⟩, rfl⟩
    rw [RatFunc.adjoin_X]
    exact IntermediateField.mem_top
  letI : Algebra.EssFiniteType K (RatFunc K) :=
    essFiniteType_of_transcendental_of_finiteDimensional
      (RatFunc.transcendental_X (K := K)) inferInstance
  letI : ∀ v : Place K (RatFunc K), v.DCoordGenerates := dCoordGenerates_of_isCurveOver
  letI : HasCanonicalLocalResidueK K F :=
    instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar
  letI : HasLocalResidue K F := instHasLocalResidue_of_hasCanonicalLocalResidueK
  intro _ ω hω f
  exact residueTheorem_of_K (residueTheoremK_of_isAlgClosed (K := K) (F := F)) hω f

end SupersingularCurves.Geometry.ResidueDuality
