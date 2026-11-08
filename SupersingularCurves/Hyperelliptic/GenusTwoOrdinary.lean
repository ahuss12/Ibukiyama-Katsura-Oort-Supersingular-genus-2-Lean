/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Hyperelliptic.GenusTwoJacobian
import SupersingularCurves.IKO.TorsionCriteria
import SupersingularCurves.IKO.GenusTwoOrdinaryFixedVectors

/-!
# The general genus-two ordinary criterion

For every separable quintic or sextic over an algebraically closed field
of odd characteristic, any representing Jacobian is ordinary exactly when
the IKO coefficient matrix has nonzero determinant.

The proof counts actual Jacobian p-torsion through its Picard correspondence,
the logarithmic equivalence with regular Cartier-fixed differentials, and
the verified full genus-two basis. The genus is proved independently by
Riemann--Hurwitz; ordinarity retains its geometric p-rank definition.
-/

set_option autoImplicit false
noncomputable section

namespace SupersingularCurves.Hyperelliptic.SimpleRootModel
open CategoryTheory AlgebraicGeometry AlgebraicCurve KaehlerDifferential
open AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open SupersingularCurves.Geometry SupersingularCurves.Differentials
open SupersingularCurves.IKO SupersingularCurves.PicardTorsion

variable {K : Type*} [Field K] [IsAlgClosed K] [NeZero (2 : K)]
  (a : SimpleRootModel K)
  (p : ℕ) [Fact p.Prime] [CharP K p]
  (hf : a.f.Separable) (hd : a.f.natDegree = 5 ∨ a.f.natDegree = 6)
  (hp : p % 2 = 1)

include hf hd hp

/-- Actual divisor-class p-torsion is additively equivalent to the fixed
vectors in the full genus-two Cartier coordinates. -/
def genusTwoTorsionEquiv :
    Pic0.torsion K a.FunctionField p ≃+
      fixedVectors p (coefficientMatrix p a.f) := by
  classical
  exact (logarithmEquiv p a.x (constantsAreBase_of_isAlgClosed K a.FunctionField)).trans
    (regularFixedCoordinatesEquiv p a.x (a.regularEquiv hf hd) _
      (a.regularCartier_coordinates hf hd p hp))

/-- The fixed-vector count is the p-torsion count of any actual
representing Jacobian, independently of the chosen base point. -/
theorem jacobian_card_torsionPoints_eq_fixedVectors
    {s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) a.curveModel.toBase}
    (J : Jacobian a.curveModel s) :
    Nat.card (J.abelianVariety.torsionPoints p) =
      Nat.card (fixedVectors p (coefficientMatrix p a.f)) := by
  rw [card_torsionPoints_eq_picard _ J.picardPoints p]
  exact Nat.card_congr (a.genusTwoTorsionEquiv p hf hd hp).toEquiv

/-- An invertible coefficient matrix is equivalent to geometric p-rank two,
with finiteness proved from the nonzero cardinality in the reverse direction. -/
theorem jacobian_hasPRankOver_two_iff_det_ne_zero
    {s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) a.curveModel.toBase}
    (J : Jacobian a.curveModel s) :
    J.abelianVariety.HasPRankOver p 2 ↔ (coefficientMatrix p a.f).det ≠ 0 := by
  have hcard : Nat.card (J.abelianVariety.torsionPoints p) = p ^ 2 ↔
      (coefficientMatrix p a.f).det ≠ 0 := by
    rw [a.jacobian_card_torsionPoints_eq_fixedVectors p hf hd hp J]
    exact card_fixedVectors_eq_prime_sq_iff_det_ne_zero p (coefficientMatrix p a.f)
  constructor
  · intro h
    exact hcard.mp h.2
  · intro h
    have hc := hcard.mpr h
    exact ⟨Nat.finite_of_card_ne_zero (by
      rw [hc]
      exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero), hc⟩

/-- IKO's ordinary criterion for every separable quintic or sextic:
the actual Jacobian is ordinary exactly when its Cartier matrix is invertible. -/
theorem jacobian_isOrdinaryOver_iff_det_ne_zero
    {s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) a.curveModel.toBase}
    (J : Jacobian a.curveModel s) :
    J.abelianVariety.IsOrdinaryOver p ↔ (coefficientMatrix p a.f).det ≠ 0 := by
  unfold AbelianVariety.IsOrdinaryOver
  have hr := congrArg (J.abelianVariety.HasPRankOver p) (a.genus_eq_two hf hd)
  rw [hr]
  exact a.jacobian_hasPRankOver_two_iff_det_ne_zero p hf hd hp J

end SupersingularCurves.Hyperelliptic.SimpleRootModel
