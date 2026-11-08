/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.ResidueFoundation
import Theorems.Thm_AlgebraicCurve_finite_H1_and_exists_linearEquiv_dual_H1_omegaSpace
import Theorems.Thm_AlgebraicCurve_exists_linearEquiv_regularDifferentials_omegaSpace_zero
import Theorems.Thm_AlgebraicCurve_mem_adeleSpace_iff_mem_repartitions
import Definitions.Def_AlgebraicCurve_SerrePairing

/-!
# Residue-normalized duality for the actual repartition quotient

The existing two equivalences through Weil differentials each have a
specified evaluation formula. We compose these equivalences, prove the
residue-sum formula on every repartition (including the zero differential),
and use that formula to characterize the map uniquely. The compatibility
with the actual Cech/off-chart pairing is proved on quotient representatives.
The deep duality and residue results are reused from the pinned FLT sources.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace SupersingularCurves.Geometry.ResidueDuality
open AlgebraicCurve KaehlerDifferential

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F]
variable [HasCanonicalDivisor (K := K) (F := F)]
variable [∀ v : Place K F, v.DCoordGenerates]
variable [HasCanonicalLocalResidueKStar K F]

/-- A repartition as the same function in the adelic space. -/
def adeleOfRepartition (a : ↥(repartitions K F)) : adeleSpace K F :=
  ⟨a, mem_adeleSpace_iff_mem_repartitions.mpr a.2⟩

variable (hC : ConstantsAreBase K F) (hRT : ResidueTheorem K F)

/-- The existing regular/Weil equivalence, chosen with its residue formula. -/
def regularOmegaEquiv : regularDifferentials K F ≃ₗ[K]
    omegaSpace (K := K) (F := F) (0 : Divisor K F) :=
  Classical.choose (exists_linearEquiv_regularDifferentials_omegaSpace_zero hC hRT)

/-- The existing dual-H1/Weil equivalence, with its quotient evaluation formula. -/
def dualOmegaEquiv : Module.Dual K (H1 (0 : Divisor K F)) ≃ₗ[K]
    omegaSpace (K := K) (F := F) (0 : Divisor K F) :=
  Classical.choose (finite_H1_and_exists_linearEquiv_dual_H1_omegaSpace hC 0).2

theorem regularOmegaEquiv_nonzero (ω : regularDifferentials K F)
    (hω : (ω : Ω[F⁄K]) ≠ 0) :
    (regularOmegaEquiv hC hRT ω : Module.Dual K (adeleSpace K F)) =
      weilOfKaehler K F hω :=
  Classical.choose_spec (exists_linearEquiv_regularDifferentials_omegaSpace_zero hC hRT) ω hω

theorem dualOmegaEquiv_apply (φ : Module.Dual K (H1 (0 : Divisor K F)))
    (a : ↥(repartitions K F)) :
    (dualOmegaEquiv hC φ : Module.Dual K (adeleSpace K F)) (adeleOfRepartition a) =
      φ (Submodule.Quotient.mk a) :=
  Classical.choose_spec (finite_H1_and_exists_linearEquiv_dual_H1_omegaSpace hC 0).2
    φ (adeleOfRepartition a) a.2

/-- Regular differentials as the dual of actual repartition H1. The map is
specified by residues, not by choosing equal-dimensional vector spaces. -/
def regularDualEquiv : regularDifferentials K F ≃ₗ[K]
    Module.Dual K (H1 (0 : Divisor K F)) :=
  (regularOmegaEquiv hC hRT).trans (dualOmegaEquiv hC).symm

/-- The defining residue formula, valid for every differential and repartition. -/
theorem regularDualEquiv_mk (ω : regularDifferentials K F) (a : ↥(repartitions K F)) :
    regularDualEquiv hC hRT ω (Submodule.Quotient.mk a) =
      ∑ᶠ v, kaehlerResidueTerm (ω : Ω[F⁄K]) (a : Place K F → F) v := by
  rcases eq_or_ne (ω : Ω[F⁄K]) 0 with hω | hω
  · have hz : ω = 0 := Subtype.ext hω
    rw [hz, map_zero, LinearMap.zero_apply]
    exact (finsum_eq_zero_of_forall_eq_zero fun v => kaehlerResidueTerm_zero_left _ v).symm
  · have he := dualOmegaEquiv_apply hC (regularDualEquiv hC hRT ω) a
    have hi : dualOmegaEquiv hC (regularDualEquiv hC hRT ω) = regularOmegaEquiv hC hRT ω :=
      (dualOmegaEquiv hC).apply_symm_apply _
    rw [hi, regularOmegaEquiv_nonzero hC hRT ω hω] at he
    exact he.symm

/-- Quotient representatives determine the residue comparison uniquely. -/
theorem regularDualEquiv_unique
    (e : regularDifferentials K F →ₗ[K] Module.Dual K (H1 (0 : Divisor K F)))
    (he : ∀ (ω : regularDifferentials K F) (a : ↥(repartitions K F)),
      e ω (Submodule.Quotient.mk a) =
        ∑ᶠ v, kaehlerResidueTerm (ω : Ω[F⁄K]) (a : Place K F → F) v) :
    e = (regularDualEquiv hC hRT).toLinearMap := by
  apply LinearMap.ext
  intro ω
  apply LinearMap.ext
  intro q
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  exact (he ω a).trans (regularDualEquiv_mk hC hRT ω a).symm

/-- Compatibility with the actual Cech-to-repartition map and residue pairing. -/
theorem regularDualEquiv_cech {S₀ S₁ : Set (Place K F)}
    (hcover : S₀ ∪ S₁ = Set.univ) (ω : regularDifferentials K F)
    (q : cechH1 S₀ S₁ (0 : Divisor K F)) :
    regularDualEquiv hC hRT ω (cechH1ToH1 hcover 0 q) =
      serrePairing hRT hcover ω q := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [cechH1ToH1_mk, regularDualEquiv_mk, serrePairing_apply_mk, residueSumOffChart_def]

end SupersingularCurves.Geometry.ResidueDuality
