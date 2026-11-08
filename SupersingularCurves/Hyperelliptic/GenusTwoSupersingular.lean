/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.SupersingularJacobian
import SupersingularCurves.Hyperelliptic.GenusTwoPRank

/-!
# The forward geometric supersingularity criterion in genus two

For every separable quintic or sextic in odd characteristic, geometric
supersingularity implies square-zero Cartier and the twisted matrix equation.
Supersingularity retains its independent actual product-isogeny definition.
The reverse implication is not proved here.
-/

set_option autoImplicit false
noncomputable section

namespace SupersingularCurves.Hyperelliptic.SimpleRootModel
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open NeronModelInfra GoodReductionJacobian
open SupersingularCurves.Geometry SupersingularCurves.Differentials
open SupersingularCurves.IKO

variable {K : Type*} [Field K] [IsAlgClosed K] [NeZero (2 : K)]
  (a : SimpleRootModel K) (p : ℕ) [Fact p.Prime] [CharP K p]
  (hf : a.f.Separable) (hd : a.f.natDegree = 5 ∨ a.f.natDegree = 6)
  (hp : p % 2 = 1)

include hf hd hp

/-- IKO Lemma 1.1(i), geometric-to-matrix direction, for any representing
Jacobian of any presented separable quintic or sextic. -/
theorem jacobian_isSupersingular_imp_matrix
    {s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) a.curveModel.toBase}
    (J : Jacobian a.curveModel s) (h : J.IsSupersingular p) :
    (coefficientMatrix p a.f).map (fun c => c ^ p) *
      coefficientMatrix p a.f = 0 :=
  (a.jacobian_hasPRankOver_zero_iff_matrix p hf hd hp J).mp
    (Jacobian.IsSupersingular.hasPRankOver_zero h
      ⟨a.x, a.transcendental_x, a.finiteDimensional_coordinate⟩)

/-- The existential geometric curve predicate forces the twisted equation. -/
theorem isSupersingular_imp_matrix
    (h : Geometry.CurveModel.IsSupersingular p a.curveModel) :
    (coefficientMatrix p a.f).map (fun c => c ^ p) *
      coefficientMatrix p a.f = 0 := by
  obtain ⟨s, J, hJ⟩ := h
  exact a.jacobian_isSupersingular_imp_matrix p hf hd hp J hJ

/-- Actual geometric supersingularity forces square-zero Cartier on the
entire space of regular differentials. -/
theorem isSupersingular_imp_cartier_square_zero
    (h : Geometry.CurveModel.IsSupersingular p a.curveModel) :
    ∀ ω : regularDifferentials K a.FunctionField,
      regularCartier p a.x (regularCartier p a.x ω) = 0 :=
  (a.all_regularCartier_square_zero_iff hf hd p hp).mpr
    (a.isSupersingular_imp_matrix p hf hd hp h)

/-- The same implication on actual scheme-global differential forms. -/
theorem isSupersingular_imp_globalCartier_square_zero
    (h : Geometry.CurveModel.IsSupersingular p a.curveModel) :
    ∀ ω : a.GlobalForms, a.globalCartier p (a.globalCartier p ω) = 0 :=
  (a.all_globalCartier_square_zero_iff hf hd p hp).mpr
    (a.isSupersingular_imp_matrix p hf hd hp h)

end SupersingularCurves.Hyperelliptic.SimpleRootModel
