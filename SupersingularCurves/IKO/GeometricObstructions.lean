/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.JacobianIndependence
import SupersingularCurves.IKO.Jacobians
import SupersingularCurves.IKO.GlobalForms

/-!
# Necessary geometric superspeciality criteria for the IKO curves

These statements use the independent geometric product-isomorphism predicate.
They apply to every representing Jacobian and to the existential curve
predicate. The implications are one-way: the superspecial classification
needed for the converse is not an assumption or a theorem of this module.
-/

set_option autoImplicit false
noncomputable section

namespace SupersingularCurves.IKO
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open NeronModelInfra GoodReductionJacobian
open SupersingularCurves.Geometry SupersingularCurves.Differentials

variable {K : Type*} [Field K] [IsAlgClosed K] [NeZero (2 : K)]
  (p : ℕ) [Fact p.Prime] [CharP K p]

/-- The root criterion holds for every family-A Jacobian and every base point. -/
theorem familyA_anyJacobian_pRank_zero_iff (hp5 : 5 ≤ p) (t : K)
    (h3 : (3 : K) ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    {s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (familyACurve t h3 ht0 ht1).toBase}
    (J : Jacobian (familyACurve t h3 ht0 ht1) s) :
    J.abelianVariety.HasPRankOver p 0 ↔ (gPolynomial p).eval t = 0 :=
  (J.hasPRankOver_iff (familyAJacobian t h3 ht0 ht1).jacobian p 0).trans
    (familyAJacobian_pRank_zero_iff p hp5 t h3 ht0 ht1)

theorem familyB_anyJacobian_pRank_zero_iff (hp3 : 3 ≤ p) (t : K)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    {s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (familyBCurve t ht0 ht1).toBase}
    (J : Jacobian (familyBCurve t ht0 ht1) s) :
    J.abelianVariety.HasPRankOver p 0 ↔ (hPolynomial p).eval t = 0 :=
  (J.hasPRankOver_iff (familyBJacobian t ht0 ht1).jacobian p 0).trans
    (familyBJacobian_pRank_zero_iff p hp3 t ht0 ht1)

/-- Geometric superspeciality of the curve forces the IKO polynomial to vanish. -/
theorem familyA_isSuperspecial_imp_root (hp5 : 5 ≤ p) (t : K)
    (h3 : (3 : K) ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (h : Geometry.CurveModel.IsSuperspecial p (familyACurve t h3 ht0 ht1)) :
    (gPolynomial p).eval t = 0 :=
  (familyAJacobian_pRank_zero_iff p hp5 t h3 ht0 ht1).mp
    (h.hasPRankOver_zero (familyAJacobian t h3 ht0 ht1).jacobian)

theorem familyB_isSuperspecial_imp_root (hp3 : 3 ≤ p) (t : K)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (h : Geometry.CurveModel.IsSuperspecial p (familyBCurve t ht0 ht1)) :
    (hPolynomial p).eval t = 0 :=
  (familyBJacobian_pRank_zero_iff p hp3 t ht0 ht1).mp
    (h.hasPRankOver_zero (familyBJacobian t ht0 ht1).jacobian)

theorem familyA_isSuperspecial_imp_cartier_zero (hp5 : 5 ≤ p) (t : K)
    (h3 : (3 : K) ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (h : Geometry.CurveModel.IsSuperspecial p (familyACurve t h3 ht0 ht1)) :
    ∀ ω : regularDifferentials K (familyAModel t h3 ht1).FunctionField,
      regularCartier p (familyAModel t h3 ht1).x ω = 0 :=
  (familyA_all_regularCartier_zero_iff p hp5 t h3 ht0 ht1).mpr
    (familyA_isSuperspecial_imp_root p hp5 t h3 ht0 ht1 h)

theorem familyB_isSuperspecial_imp_cartier_zero (hp3 : 3 ≤ p) (t : K)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (h : Geometry.CurveModel.IsSuperspecial p (familyBCurve t ht0 ht1)) :
    ∀ ω : regularDifferentials K (familyBModel t ht0).FunctionField,
      regularCartier p (familyBModel t ht0).x ω = 0 :=
  (familyB_all_regularCartier_zero_iff p hp3 t ht0 ht1).mpr
    (familyB_isSuperspecial_imp_root p hp3 t ht0 ht1 h)

theorem familyA_isSuperspecial_imp_globalCartier_zero (hp5 : 5 ≤ p) (t : K)
    (h3 : (3 : K) ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (h : Geometry.CurveModel.IsSuperspecial p (familyACurve t h3 ht0 ht1)) :
    ∀ ω, familyAGlobalCartier p t h3 ht0 ht1 ω = 0 :=
  (familyA_all_globalCartier_zero_iff p hp5 t h3 ht0 ht1).mpr
    (familyA_isSuperspecial_imp_root p hp5 t h3 ht0 ht1 h)

theorem familyB_isSuperspecial_imp_globalCartier_zero (hp3 : 3 ≤ p) (t : K)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (h : Geometry.CurveModel.IsSuperspecial p (familyBCurve t ht0 ht1)) :
    ∀ ω, familyBGlobalCartier p t ht0 ht1 ω = 0 :=
  (familyB_all_globalCartier_zero_iff p hp3 t ht0 ht1).mpr
    (familyB_isSuperspecial_imp_root p hp3 t ht0 ht1 h)

theorem familyA_not_isSuperspecial_of_nonroot (hp5 : 5 ≤ p) (t : K)
    (h3 : (3 : K) ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (ht : (gPolynomial p).eval t ≠ 0) :
    ¬ Geometry.CurveModel.IsSuperspecial p (familyACurve t h3 ht0 ht1) :=
  fun h => ht (familyA_isSuperspecial_imp_root p hp5 t h3 ht0 ht1 h)

theorem familyB_not_isSuperspecial_of_nonroot (hp3 : 3 ≤ p) (t : K)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) (ht : (hPolynomial p).eval t ≠ 0) :
    ¬ Geometry.CurveModel.IsSuperspecial p (familyBCurve t ht0 ht1) :=
  fun h => ht (familyB_isSuperspecial_imp_root p hp3 t ht0 ht1 h)

/-- In characteristic three the whole admissible family B is excluded. -/
theorem familyB_not_isSuperspecial_char_three [CharP K 3]
    (t : K) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    ¬ Geometry.CurveModel.IsSuperspecial 3 (familyBCurve t ht0 ht1) := by
  apply familyB_not_isSuperspecial_of_nonroot 3 (by decide) t ht0 ht1
  simp [hPolynomial_three]

end SupersingularCurves.IKO
