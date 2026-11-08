/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.CartierVerschiebung
import SupersingularCurves.Geometry.GlobalCartierModels
import SupersingularCurves.IKO.Jacobians
import SupersingularCurves.Hyperelliptic.CharacteristicThree

/-!
# The IKO equations detect actual Jacobian Verschiebung cotangent vanishing

The existing family Cartier equations now apply to the cotangent differential
of the independently constructed Jacobian Verschiebung. The general
hyperelliptic matrix criterion is included, together with the characteristic
three example where this differential is nonzero despite p-rank zero.
No product-isomorphism or product-isogeny classification is asserted.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SupersingularCurves
open CategoryTheory AlgebraicGeometry AlgebraicCurve NeronModelInfra SupersingularCurves.Geometry

namespace IKO
variable {K : Type*} [Field K] [IsAlgClosed K] [NeZero (2 : K)]
variable (p : ℕ) [Fact p.Prime] [CharP K p]

/-- Family A: the IKO polynomial detects vanishing of the actual Jacobian
Verschiebung cotangent differential. -/
theorem familyAJacobian_verschiebungCotangent_zero_iff (hp5 : 5 ≤ p) (t : K)
    (h3 : (3 : K) ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    (familyAJacobian t h3 ht0 ht1).jacobian.verschiebungCotangent p = 0 ↔
      (gPolynomial p).eval t = 0 := by
  have h := (familyAJacobian t h3 ht0 ht1).jacobian.verschiebungCotangent_eq_zero_iff_forall
    (differentialChart (familyACurve t h3 ht0 ht1)) p (familyAModel t h3 ht1).x
  exact h.trans (familyA_all_globalCartier_zero_iff p hp5 t h3 ht0 ht1)

/-- Family B: the IKO polynomial detects the same actual cotangent map. -/
theorem familyBJacobian_verschiebungCotangent_zero_iff (hp3 : 3 ≤ p) (t : K)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    (familyBJacobian t ht0 ht1).jacobian.verschiebungCotangent p = 0 ↔
      (hPolynomial p).eval t = 0 := by
  have h := (familyBJacobian t ht0 ht1).jacobian.verschiebungCotangent_eq_zero_iff_forall
    (differentialChart (familyBCurve t ht0 ht1)) p (familyBModel t ht0).x
  exact h.trans (familyB_all_globalCartier_zero_iff p hp3 t ht0 ht1)

/-- For this family, the already established geometric p-rank-zero locus is
also exactly the actual Verschiebung cotangent vanishing locus. -/
theorem familyAJacobian_pRank_zero_iff_verschiebungCotangent_zero
    (hp5 : 5 ≤ p) (t : K) (h3 : (3 : K) ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    (familyAJacobian t h3 ht0 ht1).jacobian.abelianVariety.HasPRankOver p 0 ↔
      (familyAJacobian t h3 ht0 ht1).jacobian.verschiebungCotangent p = 0 := by
  rw [familyAJacobian_pRank_zero_iff p hp5 t h3 ht0 ht1,
    familyAJacobian_verschiebungCotangent_zero_iff p hp5 t h3 ht0 ht1]

theorem familyBJacobian_pRank_zero_iff_verschiebungCotangent_zero
    (hp3 : 3 ≤ p) (t : K) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    (familyBJacobian t ht0 ht1).jacobian.abelianVariety.HasPRankOver p 0 ↔
      (familyBJacobian t ht0 ht1).jacobian.verschiebungCotangent p = 0 := by
  rw [familyBJacobian_pRank_zero_iff p hp3 t ht0 ht1,
    familyBJacobian_verschiebungCotangent_zero_iff p hp3 t ht0 ht1]

/-- Outside the zero locus, this family is ordinary. -/
theorem familyAJacobian_ordinary_iff_verschiebungCotangent_ne_zero
    (hp5 : 5 ≤ p) (t : K) (h3 : (3 : K) ≠ 0) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    (familyAJacobian t h3 ht0 ht1).jacobian.abelianVariety.IsOrdinaryOver p ↔
      (familyAJacobian t h3 ht0 ht1).jacobian.verschiebungCotangent p ≠ 0 := by
  exact (familyAJacobian_ordinary_iff p hp5 t h3 ht0 ht1).trans
    (not_congr (familyAJacobian_verschiebungCotangent_zero_iff p hp5 t h3 ht0 ht1)).symm

theorem familyBJacobian_ordinary_iff_verschiebungCotangent_ne_zero
    (hp3 : 3 ≤ p) (t : K) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    (familyBJacobian t ht0 ht1).jacobian.abelianVariety.IsOrdinaryOver p ↔
      (familyBJacobian t ht0 ht1).jacobian.verschiebungCotangent p ≠ 0 := by
  exact (familyBJacobian_ordinary_iff p hp3 t ht0 ht1).trans
    (not_congr (familyBJacobian_verschiebungCotangent_zero_iff p hp3 t ht0 ht1)).symm

end IKO

namespace Hyperelliptic.SimpleRootModel
variable {K : Type*} [Field K] [IsAlgClosed K] [NeZero (2 : K)]
variable (a : SimpleRootModel K) (p : ℕ) [Fact p.Prime] [CharP K p]

/-- The general genus-two coefficient matrix vanishes exactly when the
actual cotangent differential of Jacobian Verschiebung vanishes. -/
theorem jacobian_verschiebungCotangent_zero_iff_matrix
    (hf : a.f.Separable) (hd : a.f.natDegree = 5 ∨ a.f.natDegree = 6)
    (hp : p % 2 = 1)
    {s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) a.curveModel.toBase}
    (J : Jacobian a.curveModel s) :
    J.verschiebungCotangent p = 0 ↔ IKO.coefficientMatrix p a.f = 0 := by
  have h := J.verschiebungCotangent_eq_zero_iff_forall
    (differentialChart a.curveModel) p a.x
  exact h.trans (a.all_globalCartier_zero_iff hf hd p hp)

end Hyperelliptic.SimpleRootModel

namespace Hyperelliptic.CharacteristicThree
variable {K : Type*} [Field K] [IsAlgClosed K] [CharP K 3]
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : NeZero (2 : K) := two_ne_zero

/-- For y²=x⁵−1 in characteristic three, actual Verschiebung cotangent is
nonzero. This is stronger than the previously computed Cartier distinction. -/
theorem jacobian_verschiebungCotangent_ne_zero :
    (model (K := K)).jacobianRealization.jacobian.verschiebungCotangent 3 ≠ 0 := by
  intro hzero
  have h := ((model (K := K)).jacobianRealization.jacobian.verschiebungCotangent_eq_zero_iff_forall
      (differentialChart model.curveModel) 3 model.x).mp hzero
  exact (global_cartier_distinction (K := K)).1 h

/-- Actual p-rank zero does not imply actual Verschiebung cotangent zero:
the constructed smooth proper genus-two curve supplies both statements. -/
theorem jacobian_pRank_zero_and_verschiebungCotangent_ne_zero :
    (model (K := K)).jacobianRealization.jacobian.abelianVariety.HasPRankOver 3 0 ∧
      (model (K := K)).jacobianRealization.jacobian.verschiebungCotangent 3 ≠ 0 :=
  ⟨jacobian_hasPRankOver_zero, jacobian_verschiebungCotangent_ne_zero⟩

end Hyperelliptic.CharacteristicThree
end SupersingularCurves
