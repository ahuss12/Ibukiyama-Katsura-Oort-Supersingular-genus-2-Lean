/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.CartierResidueAdjoint
import SupersingularCurves.Geometry.JacobianFrobeniusUntwist

/-!
# Cartier and the independently constructed Jacobian Verschiebung

The cotangent comparison is normalized by Poincare cocycles and residues.
The scalar untwist is independently specified by actual curve projection on
cohomology. Residue adjointness proves equality with the existing Cartier
operator. In particular, actual Verschiebung cotangent vanishing is equivalent
to Cartier vanishing. No superspeciality or isogeny classification is assumed.

Identifying the cohomological untwist with the cotangent pullback of the
Jacobian scheme projection is a further naturality statement, not asserted here.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

namespace SupersingularCurves.Geometry.Jacobian
open CategoryTheory AlgebraicGeometry AlgebraicCurve InfinitesimalPicard NeronModelInfra

variable {K : Type u} [Field K] [IsAlgClosed K]
variable {F : Type v} [Field F] [Algebra K F]
variable {M : CurveModel K F}
  {s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase}
variable (J : Jacobian M s) (V : DifferentialChart M)

/-- The two independent normalizations agree on every actual Cech class. -/
theorem cotangentGlobalEquiv_cech_eval (z : J.Cotangent)
    (q : CechH1 M.toBase V.cover) :
    V.globalDualRepartitionEquiv (J.cotangentGlobalEquiv V z)
        (SchemeCech.toRepartition M.toBase V.cover q) =
      J.cotangentDualCechEquiv V.cover z q := by
  rw [J.globalDualRepartitionEquiv_cotangentGlobalEquiv,
    J.cotangentDualRepartitionEquiv_cech]

variable [Algebra.EssFiniteType K F] [IsCurveOver K F]
variable (p : ℕ) [Fact p.Prime] [CharP K p]
variable (x : F) [FiniteDimensional (IntermediateField.adjoin K {x}) F]

/-- The existing Cartier operator agrees with actual Jacobian Verschiebung
after the separately constructed, cohomologically normalized scalar untwist. -/
theorem cotangentGlobalEquiv_verschiebung (z : J.Cotangent) :
    J.cotangentGlobalEquiv V
        (J.cotangentCohomologicalUntwist V.cover p (J.verschiebungCotangent p z)) =
      V.globalCartier p x (J.cotangentGlobalEquiv V z) := by
  letI := M.functionFieldAlgebra
  apply V.globalDualRepartitionEquiv.injective
  apply LinearMap.ext
  intro r
  obtain ⟨q, rfl⟩ := (SchemeCech.repartitionEquivOfAlgClosed M.toBase V.cover).surjective r
  change V.globalDualRepartitionEquiv _
      (SchemeCech.toRepartition M.toBase V.cover q) =
    V.globalDualRepartitionEquiv _ (SchemeCech.toRepartition M.toBase V.cover q)
  apply (frobenius K p).injective
  change (_ : K) ^ p = (_ : K) ^ p
  rw [J.cotangentGlobalEquiv_cech_eval,
    J.cotangentCohomologicalUntwist_verschiebung_eval_pow,
    V.globalCartier_residue_adjoint p x,
    J.cotangentGlobalEquiv_cech_eval]

/-- Vanishing for a single actual cotangent vector is detected by Cartier. -/
theorem verschiebungCotangent_apply_eq_zero_iff (z : J.Cotangent) :
    J.verschiebungCotangent p z = 0 ↔
      V.globalCartier p x (J.cotangentGlobalEquiv V z) = 0 := by
  rw [← J.cotangentGlobalEquiv_verschiebung V p x z]
  constructor
  · intro h
    simp only [h, map_zero]
  · intro h
    apply (J.cotangentCohomologicalUntwist V.cover p).injective
    apply (J.cotangentGlobalEquiv V).injective
    simpa only [map_zero] using h

/-- Equality with zero concerns the actual Verschiebung cotangent map and
the independently defined Cartier operator on all global differential forms. -/
theorem verschiebungCotangent_eq_zero_iff :
    J.verschiebungCotangent p = 0 ↔ V.globalCartier p x = 0 := by
  constructor
  · intro h
    apply AddMonoidHom.ext
    intro ω
    obtain ⟨z, rfl⟩ := (J.cotangentGlobalEquiv V).surjective ω
    exact (J.verschiebungCotangent_apply_eq_zero_iff V p x z).mp
      (by rw [h]; rfl)
  · intro h
    apply LinearMap.ext
    intro z
    exact (J.verschiebungCotangent_apply_eq_zero_iff V p x z).mpr
      (by rw [h]; rfl)

/-- Pointwise form convenient for previously proved matrix and family criteria. -/
theorem verschiebungCotangent_eq_zero_iff_forall :
    J.verschiebungCotangent p = 0 ↔ ∀ ω : V.GlobalForms, V.globalCartier p x ω = 0 := by
  rw [J.verschiebungCotangent_eq_zero_iff V p x]
  exact ⟨fun h ω => by rw [h]; rfl, fun h => AddMonoidHom.ext h⟩

end SupersingularCurves.Geometry.Jacobian
