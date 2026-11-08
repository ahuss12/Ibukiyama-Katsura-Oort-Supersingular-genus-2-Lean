/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.JacobianIsogenyTorsion
import SupersingularCurves.Geometry.JacobianIndependence

/-!
# Supersingular curves have Jacobian p-rank zero

The existential curve predicate uses an actual geometric product isogeny.
The point-group correspondence transfers its p-rank consequence to every
representing Jacobian, independently of the choice of base point.
-/

set_option autoImplicit false
noncomputable section
universe u v

namespace SupersingularCurves.Geometry
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open NeronModelInfra GoodReductionJacobian

variable {K : Type u} [Field K] [IsAlgClosed K]
  {F : Type v} [Field F] [Algebra K F] [IsCurveOver K F]
  {M : AlgebraicCurve.CurveModel K F}

/-- Geometric supersingularity forces p-rank zero for every representing
Jacobian, with no isogeny or classification supplied as an extra hypothesis. -/
theorem CurveModel.IsSupersingular.hasPRankOver_zero
    {p : ℕ} [Fact p.Prime] [CharP K p]
    (h : CurveModel.IsSupersingular p M)
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    {s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase}
    (J : Jacobian M s) : J.abelianVariety.HasPRankOver p 0 := by
  obtain ⟨s', J', hJ'⟩ := h
  exact (J'.hasPRankOver_iff J p 0).mp
    (Jacobian.IsSupersingular.hasPRankOver_zero hJ' hfg)

end SupersingularCurves.Geometry
