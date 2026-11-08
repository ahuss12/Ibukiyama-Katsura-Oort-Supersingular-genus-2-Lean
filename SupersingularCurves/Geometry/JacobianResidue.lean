/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.SchemeResidueDuality
import SupersingularCurves.Geometry.GlobalDifferentials
import SupersingularCurves.Geometry.JacobianRepartition

/-!
# Actual Jacobian cotangent space and global differentials via residues

The comparison composes the Poincare-normalized cotangent/dual-cohomology
map with the inverse of the residue-normalized duality for the actual curve.
The evaluation formulas specify the resulting map and prove its uniqueness.
The Frobenius-deformation evaluation is transported along this comparison;
it is not yet the Cartier/Verschiebung compatibility theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

namespace SupersingularCurves.Geometry
open CategoryTheory AlgebraicGeometry AlgebraicCurve KaehlerDifferential NeronModelInfra
open InfinitesimalPicard

variable {K : Type u} [Field K] [IsAlgClosed K]
variable {F : Type v} [Field F] [Algebra K F] {M : CurveModel K F}

namespace DifferentialChart
variable (V : DifferentialChart M)

/-- Global sheaf differentials as the dual of actual repartition cohomology,
by generic restriction followed by the specified residue pairing. -/
def globalDualRepartitionEquiv :
    letI := M.functionFieldAlgebra
    V.GlobalForms ≃ₗ[K] Module.Dual K (SchemeCech.RepartitionH1 M.toBase) :=
  letI := M.functionFieldAlgebra
  V.schemeRegularEquiv.trans (SchemeResidue.regularDualEquiv M.toBase V.cover)

/-- The global-form comparison evaluates by the actual generic differential
and the trace-of-local-residues sum on every repartition. -/
theorem globalDualRepartitionEquiv_mk (ω : V.GlobalForms) :
    letI := M.functionFieldAlgebra
    ∀ a : ↥(repartitions K M.C.functionField),
    V.globalDualRepartitionEquiv ω (Submodule.Quotient.mk a) =
      SchemeResidue.residueSum M.toBase
        (kaehlerToFunctionField M.toBase V.cover.U0 ω.val.1) a := by
  letI := M.functionFieldAlgebra
  intro a
  change SchemeResidue.regularDualEquiv M.toBase V.cover
    (V.schemeRegularEquiv ω) (Submodule.Quotient.mk a) = _
  rw [SchemeResidue.regularDualEquiv_mk, V.schemeRegularEquiv_generic_restriction]

/-- Evaluation on an actual structure-sheaf overlap section. -/
theorem globalDualRepartitionEquiv_cech_mk (ω : V.GlobalForms)
    (f : (V.cover.structureSheafSections M.toBase).M01) :
    letI := M.functionFieldAlgebra
    letI := SchemeCech.properCover_overlap_nonempty M.toBase V.cover
    V.globalDualRepartitionEquiv ω
        (SchemeCech.toRepartition M.toBase V.cover (Submodule.Quotient.mk f)) =
      SchemeResidue.residueSum M.toBase
        (kaehlerToFunctionField M.toBase V.cover.U0 ω.val.1)
        (extendOffChart K (placesOf M.toBase V.cover.U0)
          ((M.C.germToFunctionField (V.cover.U0 ⊓ V.cover.U1)).hom f)) := by
  letI := M.functionFieldAlgebra
  letI := SchemeCech.properCover_overlap_nonempty M.toBase V.cover
  rw [SchemeCech.toRepartition_mk, V.globalDualRepartitionEquiv_mk]

/-- A global differential is determined by all its residue evaluations. -/
theorem eq_iff_residue_evaluations_eq (ω η : V.GlobalForms) :
    letI := M.functionFieldAlgebra
    ω = η ↔ ∀ a : ↥(repartitions K M.C.functionField),
      SchemeResidue.residueSum M.toBase
        (kaehlerToFunctionField M.toBase V.cover.U0 ω.val.1) a =
      SchemeResidue.residueSum M.toBase
        (kaehlerToFunctionField M.toBase V.cover.U0 η.val.1) a := by
  letI := M.functionFieldAlgebra
  constructor
  · rintro rfl a
    rfl
  · intro h
    apply V.globalDualRepartitionEquiv.injective
    apply LinearMap.ext
    intro q
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [V.globalDualRepartitionEquiv_mk, V.globalDualRepartitionEquiv_mk]
    exact h a

end DifferentialChart

namespace Jacobian
variable {s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase}
variable (J : Jacobian M s) (V : DifferentialChart M)

/-- The actual cotangent/global-differential comparison, specified by the
Poincare and residue pairings, with no duality hypothesis left to the caller. -/
def cotangentGlobalEquiv : J.Cotangent ≃ₗ[K] V.GlobalForms :=
  (J.cotangentDualRepartitionEquiv V.cover).trans V.globalDualRepartitionEquiv.symm

/-- Compatibility with the prescribed dual cohomology comparison. -/
theorem globalDualRepartitionEquiv_cotangentGlobalEquiv (x : J.Cotangent) :
    V.globalDualRepartitionEquiv (J.cotangentGlobalEquiv V x) =
      J.cotangentDualRepartitionEquiv V.cover x :=
  V.globalDualRepartitionEquiv.apply_symm_apply _

/-- Explicit residue normalization on every repartition representative. -/
theorem cotangentGlobalEquiv_residue_mk (x : J.Cotangent) :
    letI := M.functionFieldAlgebra
    ∀ a : ↥(repartitions K M.C.functionField),
    SchemeResidue.residueSum M.toBase
        (kaehlerToFunctionField M.toBase V.cover.U0
          (J.cotangentGlobalEquiv V x).val.1) a =
      J.cotangentDualRepartitionEquiv V.cover x (Submodule.Quotient.mk a) := by
  letI := M.functionFieldAlgebra
  intro a
  rw [← V.globalDualRepartitionEquiv_mk,
    J.globalDualRepartitionEquiv_cotangentGlobalEquiv]

/-- Explicit compatibility with the Poincare-normalized Cech comparison. -/
theorem cotangentGlobalEquiv_residue_cech (x : J.Cotangent)
    (f : (V.cover.structureSheafSections M.toBase).M01) :
    letI := M.functionFieldAlgebra
    letI := SchemeCech.properCover_overlap_nonempty M.toBase V.cover
    SchemeResidue.residueSum M.toBase
        (kaehlerToFunctionField M.toBase V.cover.U0
          (J.cotangentGlobalEquiv V x).val.1)
        (extendOffChart K (placesOf M.toBase V.cover.U0)
          ((M.C.germToFunctionField (V.cover.U0 ⊓ V.cover.U1)).hom f)) =
      J.cotangentDualCechEquiv V.cover x (Submodule.Quotient.mk f) := by
  letI := M.functionFieldAlgebra
  letI := SchemeCech.properCover_overlap_nonempty M.toBase V.cover
  rw [J.cotangentGlobalEquiv_residue_mk, J.cotangentDualRepartitionEquiv_mk]

/-- Poincare tangent evaluation fixes the normalization of the global form. -/
theorem cotangentGlobalEquiv_tangent (x : J.Cotangent)
    (l : Module.Dual K J.Cotangent) :
    V.globalDualRepartitionEquiv (J.cotangentGlobalEquiv V x)
        (J.tangentRepartitionEquiv V.cover l) = l x := by
  rw [J.globalDualRepartitionEquiv_cotangentGlobalEquiv,
    J.cotangentDualRepartitionEquiv_tangent]

/-- Uniqueness of the cotangent/global-form comparison with this normalization. -/
theorem cotangentGlobalEquiv_unique (e : J.Cotangent →ₗ[K] V.GlobalForms)
    (he : ∀ x l, V.globalDualRepartitionEquiv (e x)
      (J.tangentRepartitionEquiv V.cover l) = l x) :
    e = (J.cotangentGlobalEquiv V).toLinearMap := by
  apply LinearMap.ext
  intro x
  apply V.globalDualRepartitionEquiv.injective
  apply LinearMap.ext
  intro q
  obtain ⟨l, rfl⟩ := (J.tangentRepartitionEquiv V.cover).surjective q
  exact (he x l).trans (J.cotangentGlobalEquiv_tangent V x l).symm

variable (p : ℕ) [Fact p.Prime] [CharP K p]

/-- The global differential evaluates the actual Frobenius-pulled-back
Poincare deformation by the independently constructed Verschiebung map.
The source of the functional remains the Frobenius-twisted cotangent space. -/
theorem cotangentGlobalEquiv_frobeniusDeformation (x : J.Cotangent)
    (l : Module.Dual K (J.TwistedCotangent p)) :
    V.globalDualRepartitionEquiv (J.cotangentGlobalEquiv V x)
        (J.frobeniusRepartitionClass V.cover p l) =
      l (J.verschiebungCotangent p x) := by
  rw [J.globalDualRepartitionEquiv_cotangentGlobalEquiv,
    J.cotangentDualRepartitionEquiv_frobeniusDeformation]

end Jacobian
end SupersingularCurves.Geometry
