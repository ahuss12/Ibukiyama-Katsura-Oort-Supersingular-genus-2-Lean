/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.CartierResidueLocal
import SupersingularCurves.Geometry.GlobalCartier
import SupersingularCurves.Geometry.JacobianResidue
import SupersingularCurves.Geometry.FrobeniusCechSemilinear

/-! # Cartier adjointness for the actual residue pairing

Local residue adjointness is summed and applied to actual overlap sections.
The resulting identity relates the existing global Cartier operator to the
structure-sheaf pullback by the actual absolute Frobenius of the curve.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

namespace SupersingularCurves.Geometry
open AlgebraicCurve KaehlerDifferential
open SupersingularCurves.Differentials

namespace CartierResidue
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable [IsCurveOver K F] [PerfectField K] [IsAlgClosed K]
variable (p : ℕ) [hp : Fact p.Prime] [CharP K p]
variable (x : F) [FiniteDimensional (IntermediateField.adjoin K {x}) F]
variable [∀ w : Place K F, w.DCoordGenerates]
variable [HasCanonicalLocalResidueKStar K F]

/-- Summed Cartier/Frobenius adjointness, with the canonical local residues.
The equality holds for arbitrary input functions; the Frobenius equivalence
commutes with the finite-support sum, including its infinite-support convention. -/
theorem residueSum_cartier_pow (ω : Ω[F⁄K]) (a : Place K F → F) :
    (∑ᶠ w, kaehlerResidueTerm (cartier p x ω) a w) ^ p =
      ∑ᶠ w, kaehlerResidueTerm ω (fun w => a w ^ p) w := by
  have h := (frobeniusEquiv K p).toAddEquiv.map_finsum
    (fun w => kaehlerResidueTerm (cartier p x ω) a w)
  change (∑ᶠ w, kaehlerResidueTerm (cartier p x ω) a w) ^ p =
    ∑ᶠ w, kaehlerResidueTerm (cartier p x ω) a w ^ p at h
  rw [h]
  apply finsum_congr
  intro w
  exact kaehlerResidueTerm_cartier_pow p x w ω a

omit [PerfectField K] [IsAlgClosed K] [CharP K p]
  [∀ w : Place K F, w.DCoordGenerates] [HasCanonicalLocalResidueKStar K F] in
theorem extendOffChart_pow (S : Set (Place K F)) (f : F) :
    (fun w => (extendOffChart K S f : Place K F → F) w ^ p) =
      (extendOffChart K S (f ^ p) : Place K F → F) := by
  classical
  funext w
  simp only [coe_extendOffChart_apply]
  split_ifs <;> simp [hp.out.ne_zero]

/-- The summed identity on the actual off-chart repartition representative. -/
theorem residueSum_cartier_offChart (ω : Ω[F⁄K]) (S : Set (Place K F)) (f : F) :
    (∑ᶠ w, kaehlerResidueTerm (cartier p x ω) (extendOffChart K S f) w) ^ p =
      ∑ᶠ w, kaehlerResidueTerm ω (extendOffChart K S (f ^ p)) w := by
  rw [residueSum_cartier_pow, extendOffChart_pow]

end CartierResidue

namespace DifferentialChart
open CategoryTheory AlgebraicGeometry NeronModelInfra InfinitesimalPicard

variable {K : Type u} [Field K] [IsAlgClosed K]
variable {F : Type v} [Field F] [Algebra K F]
variable [Algebra.EssFiniteType K F] [IsCurveOver K F]
variable {M : CurveModel K F} (V : DifferentialChart M)
variable (p : ℕ) [Fact p.Prime] [CharP K p]
variable (x : F) [FiniteDimensional (IntermediateField.adjoin K {x}) F]

/-- Cartier on actual global differential sections is adjoint, under the
residue-normalized pairing, to actual absolute Frobenius on Cech H1. -/
theorem globalCartier_residue_adjoint
    (ω : V.GlobalForms) (q : CechH1 M.toBase V.cover) :
    V.globalDualRepartitionEquiv (V.globalCartier p x ω)
        (SchemeCech.toRepartition M.toBase V.cover q) ^ p =
      V.globalDualRepartitionEquiv ω
        (SchemeCech.toRepartition M.toBase V.cover
          (SchemeFrobenius.absoluteCech p M.toBase V.cover q)) := by
  letI := M.functionFieldAlgebra
  letI : IsCurveOver K M.C.functionField :=
    isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
      M.toBase (RingEquiv.refl _) (fun _ => rfl)
  letI : Algebra.EssFiniteType K M.C.functionField :=
    Algebra.EssFiniteType.of_surjective M.ffAlgEquiv.toAlgHom M.ffAlgEquiv.surjective
  letI : ∀ w : Place K M.C.functionField, w.DCoordGenerates :=
    dCoordGenerates_of_isCurveOver
  letI := SchemeResidue.residueData M.toBase
  letI := SchemeCech.properCover_overlap_nonempty M.toBase V.cover
  obtain ⟨y, _, hy, _⟩ :=
    IsCurveOver.exists_separating_transcendental (K := K) (F := M.C.functionField)
  letI := hy
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [SchemeFrobenius.absoluteCech_mk,
    V.globalDualRepartitionEquiv_cech_mk, V.globalDualRepartitionEquiv_cech_mk,
    V.generic_restriction_globalCartier p x ω y]
  change (∑ᶠ w, kaehlerResidueTerm
      (cartier p y (kaehlerToFunctionField M.toBase V.cover.U0 ω.val.1))
      (extendOffChart K (placesOf M.toBase V.cover.U0)
        ((M.C.germToFunctionField (V.cover.U0 ⊓ V.cover.U1)).hom f)) w) ^ p =
    ∑ᶠ w, kaehlerResidueTerm
      (kaehlerToFunctionField M.toBase V.cover.U0 ω.val.1)
      (extendOffChart K (placesOf M.toBase V.cover.U0)
        ((M.C.germToFunctionField (V.cover.U0 ⊓ V.cover.U1)).hom (f ^ p))) w
  rw [map_pow]
  exact CartierResidue.residueSum_cartier_offChart p y _ _ _

end DifferentialChart
end SupersingularCurves.Geometry
