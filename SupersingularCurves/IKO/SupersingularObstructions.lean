/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.SupersingularJacobian
import SupersingularCurves.IKO.GeometricObstructions

/-!
# Necessary geometric supersingularity criteria for the IKO families

An actual product isogeny forces the parameter polynomial to vanish.
For these two special families this implies Cartier itself vanishes.
The polynomial-root-to-product-isogeny converse remains open.
-/

set_option autoImplicit false
noncomputable section

namespace SupersingularCurves.IKO
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open NeronModelInfra GoodReductionJacobian
open SupersingularCurves.Geometry SupersingularCurves.Differentials

variable {K : Type*} [Field K] [IsAlgClosed K] [NeZero (2 : K)]
  (p : ℕ) [Fact p.Prime] [CharP K p]

theorem familyA_isSupersingular_imp_root (hp5 : 5 ≤ p) (t : K)
    (h3 : (3 : K) ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (h : Geometry.CurveModel.IsSupersingular p (familyACurve t h3 ht0 ht1)) :
    (gPolynomial p).eval t = 0 :=
  (familyAJacobian_pRank_zero_iff p hp5 t h3 ht0 ht1).mp
    (h.hasPRankOver_zero
      ⟨(familyAModel t h3 ht1).x, (familyAModel t h3 ht1).transcendental_x,
        (familyAModel t h3 ht1).finiteDimensional_coordinate⟩
      (familyAJacobian t h3 ht0 ht1).jacobian)

theorem familyB_isSupersingular_imp_root (hp3 : 3 ≤ p) (t : K)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (h : Geometry.CurveModel.IsSupersingular p (familyBCurve t ht0 ht1)) :
    (hPolynomial p).eval t = 0 :=
  (familyBJacobian_pRank_zero_iff p hp3 t ht0 ht1).mp
    (h.hasPRankOver_zero
      ⟨(familyBModel t ht0).x, (familyBModel t ht0).transcendental_x,
        (familyBModel t ht0).finiteDimensional_coordinate⟩
      (familyBJacobian t ht0 ht1).jacobian)

theorem familyA_isSupersingular_imp_globalCartier_zero (hp5 : 5 ≤ p) (t : K)
    (h3 : (3 : K) ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (h : Geometry.CurveModel.IsSupersingular p (familyACurve t h3 ht0 ht1)) :
    ∀ ω, familyAGlobalCartier p t h3 ht0 ht1 ω = 0 :=
  (familyA_all_globalCartier_zero_iff p hp5 t h3 ht0 ht1).mpr
    (familyA_isSupersingular_imp_root p hp5 t h3 ht0 ht1 h)

theorem familyB_isSupersingular_imp_globalCartier_zero (hp3 : 3 ≤ p) (t : K)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (h : Geometry.CurveModel.IsSupersingular p (familyBCurve t ht0 ht1)) :
    ∀ ω, familyBGlobalCartier p t ht0 ht1 ω = 0 :=
  (familyB_all_globalCartier_zero_iff p hp3 t ht0 ht1).mpr
    (familyB_isSupersingular_imp_root p hp3 t ht0 ht1 h)

/-- In characteristic three no admissible family-B curve has a Jacobian
geometrically isogenous to a product of supersingular elliptic curves. -/
theorem familyB_not_isSupersingular_char_three [CharP K 3]
    (t : K) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    ¬ Geometry.CurveModel.IsSupersingular 3 (familyBCurve t ht0 ht1) := by
  intro h
  have hr := familyB_isSupersingular_imp_root 3 (by decide) t ht0 ht1 h
  simpa [hPolynomial_three] using hr

end SupersingularCurves.IKO
