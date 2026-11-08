/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.CartierResidueAdjoint

/-!
# Square-zero Cartier and actual Čech Frobenius

Applying the established residue adjointness twice identifies the square of
Cartier with the square of actual absolute Frobenius under the nondegenerate
pairing of global differential forms and Čech cohomology.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

namespace SupersingularCurves.Geometry.DifferentialChart
open AlgebraicGeometry AlgebraicCurve InfinitesimalPicard

variable {K : Type u} [Field K] [IsAlgClosed K]
variable {F : Type v} [Field F] [Algebra K F]
variable [Algebra.EssFiniteType K F] [IsCurveOver K F]
variable {M : CurveModel K F} (V : DifferentialChart M)
variable (p : ℕ) [Fact p.Prime] [CharP K p]
variable (x : F) [FiniteDimensional (IntermediateField.adjoin K {x}) F]

/-- Two applications of the actual Cartier/residue adjointness identity. -/
theorem globalCartier_square_residue_adjoint
    (ω : V.GlobalForms) (q : CechH1 M.toBase V.cover) :
    (V.globalDualRepartitionEquiv
      (V.globalCartier p x (V.globalCartier p x ω))
        (SchemeCech.toRepartition M.toBase V.cover q) ^ p) ^ p =
      V.globalDualRepartitionEquiv ω
        (SchemeCech.toRepartition M.toBase V.cover
          (SchemeFrobenius.absoluteCech p M.toBase V.cover
            (SchemeFrobenius.absoluteCech p M.toBase V.cover q))) := by
  rw [V.globalCartier_residue_adjoint p x, V.globalCartier_residue_adjoint p x]

/-- Vanishing of Cartier squared forces the square of actual absolute
Frobenius to vanish on every Čech cohomology class. -/
theorem absoluteCech_square_zero_of_globalCartier_square_zero
    (h : ∀ ω : V.GlobalForms, V.globalCartier p x (V.globalCartier p x ω) = 0)
    (q : CechH1 M.toBase V.cover) :
    SchemeFrobenius.absoluteCech p M.toBase V.cover
      (SchemeFrobenius.absoluteCech p M.toBase V.cover q) = 0 := by
  let := M.functionFieldAlgebra
  let : Module.Free K (SchemeCech.RepartitionH1 M.toBase) :=
    Module.Free.of_divisionRing K _
  let : Module.Projective K (SchemeCech.RepartitionH1 M.toBase) := Module.Projective.of_free
  apply (SchemeCech.repartitionEquivOfAlgClosed M.toBase V.cover).injective
  change SchemeCech.toRepartition M.toBase V.cover
      (SchemeFrobenius.absoluteCech p M.toBase V.cover
        (SchemeFrobenius.absoluteCech p M.toBase V.cover q)) =
    SchemeCech.toRepartition M.toBase V.cover 0
  rw [map_zero]
  apply (Module.forall_dual_apply_eq_zero_iff K _).mp
  intro φ
  obtain ⟨ω, rfl⟩ := V.globalDualRepartitionEquiv.surjective φ
  rw [← V.globalCartier_square_residue_adjoint p x, h ω]
  simp only [map_zero, LinearMap.zero_apply, zero_pow (Fact.out : p.Prime).ne_zero]

end SupersingularCurves.Geometry.DifferentialChart
