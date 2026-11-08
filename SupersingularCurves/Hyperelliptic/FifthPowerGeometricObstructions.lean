/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Hyperelliptic.GenusTwoSuperspecial
import SupersingularCurves.Hyperelliptic.FifthPowerClassification

/-!
# Geometric non-superspeciality of the fifth-power curves

The newly proved general geometric-to-Cartier implication rules out an
actual supersingular elliptic product isomorphism when p is two or three
modulo five. In these cases Cartier has square zero and the actual Jacobian
has p-rank zero, but geometric supersingularity is not asserted here.
-/

set_option autoImplicit false
noncomputable section

namespace SupersingularCurves.Hyperelliptic.FifthPowerClassification
open AlgebraicCurve

variable {K : Type*} [Field K] [IsAlgClosed K] [NeZero (2 : K)]
variable (p : ℕ) [Fact p.Prime] [CharP K p] (hp5 : p ≠ 5) (hp : p % 2 = 1)

include hp

/-- Genuine geometric superspeciality of the explicit curve can occur
only in residue class four. This is a necessary condition, not a converse. -/
theorem isSuperspecial_imp_mod_four
    (h : Geometry.CurveModel.IsSuperspecial p (model (K := K) p hp5).curveModel) :
    p % 5 = 4 :=
  (global_cartier_zero_iff p hp5 hp).mp
    ((model p hp5).isSuperspecial_imp_globalCartier_zero p
      (quintic_separable p hp5) (Or.inl quintic_degree) hp h)

/-- The residue-two curve is not geometrically superspecial, using the
independent product-isomorphism definition. -/
theorem not_isSuperspecial_of_mod_two (hmod : p % 5 = 2) :
    ¬ Geometry.CurveModel.IsSuperspecial p (model (K := K) p hp5).curveModel := by
  intro h
  have hfour := isSuperspecial_imp_mod_four p hp5 hp h
  omega

/-- The residue-three curve is not geometrically superspecial. -/
theorem not_isSuperspecial_of_mod_three (hmod : p % 5 = 3) :
    ¬ Geometry.CurveModel.IsSuperspecial p (model (K := K) p hp5).curveModel := by
  intro h
  have hfour := isSuperspecial_imp_mod_four p hp5 hp h
  omega

end SupersingularCurves.Hyperelliptic.FifthPowerClassification
