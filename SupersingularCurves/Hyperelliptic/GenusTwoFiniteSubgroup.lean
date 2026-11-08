/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroupDimension
import SupersingularCurves.Geometry.VerschiebungNaturality
import SupersingularCurves.Hyperelliptic.GenusTwoPRank
import SupersingularCurves.IKO.VerschiebungCriteria

/-!
# Cartier criteria for the actual simultaneous finite subgroup

For any represented separable genus-two quintic or sextic, square-zero but
nonzero Cartier gives cotangent dimension one for the actual subgroup
ker(F on the first Jacobian twist) ∩ ker(V). Cartier zero instead gives
cotangent dimension two. These are cotangent dimensions, not subgroup orders
or elliptic-product classification theorems.
-/
set_option autoImplicit false
noncomputable section

namespace SupersingularCurves.Hyperelliptic.SimpleRootModel
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open NeronModelInfra GoodReductionJacobian
open SupersingularCurves.Geometry SupersingularCurves.IKO
open FrobeniusVerschiebungSubgroup

variable {K : Type*} [Field K] [IsAlgClosed K] [NeZero (2 : K)]
  (a : SimpleRootModel K) (p : ℕ) [Fact p.Prime] [CharP K p]
  (hf : a.f.Separable) (hd : a.f.natDegree = 5 ∨ a.f.natDegree = 6)
  (hp : p % 2 = 1)
  {s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) a.curveModel.toBase}
  (J : Jacobian a.curveModel s)

include hf hd hp

/-- Twisted-square-zero but nonzero Cartier matrix gives cotangent dimension
one in the actual simultaneous Frobenius--Verschiebung subgroup. -/
theorem jacobian_subgroup_cotangent_finrank_one_of_matrix
    (hC2 : (coefficientMatrix p a.f).map (fun c => c ^ p) * coefficientMatrix p a.f = 0)
    (hC : coefficientMatrix p a.f ≠ 0) :
    Module.finrank K (PointedCotangent.Cotangent
      (fibreToBase p J.abelianVariety) (fibreIdentityPoint p J.abelianVariety)) = 1 := by
  apply cotangent_finrank_eq_one_of_dimension_two p J.abelianVariety (a.genus_eq_two hf hd)
    ((a.jacobian_hasPRankOver_zero_iff_matrix p hf hd hp J).mpr hC2)
  intro hV
  exact hC ((a.jacobian_verschiebungCotangent_zero_iff_matrix p hf hd hp J).mp
    ((J.groupScheme_verschiebungCotangent_eq_zero_iff p).mp hV))

/-- The full global Cartier formulation of the one-dimensional cotangent
result, with no matrix or differential hypothesis added by the caller. -/
theorem jacobian_subgroup_cotangent_finrank_one_of_globalCartier
    (hC2 : ∀ ω : a.GlobalForms, a.globalCartier p (a.globalCartier p ω) = 0)
    (hC : ¬ ∀ ω : a.GlobalForms, a.globalCartier p ω = 0) :
    Module.finrank K (PointedCotangent.Cotangent
      (fibreToBase p J.abelianVariety) (fibreIdentityPoint p J.abelianVariety)) = 1 :=
  a.jacobian_subgroup_cotangent_finrank_one_of_matrix p hf hd hp J
    ((a.all_globalCartier_square_zero_iff hf hd p hp).mp hC2)
    (fun h => hC ((a.all_globalCartier_zero_iff hf hd p hp).mpr h))

/-- Cartier zero gives cotangent dimension two in the actual simultaneous
finite subgroup. This does not assert an elliptic-product isomorphism. -/
theorem jacobian_subgroup_cotangent_finrank_two_of_matrix_zero
    (hC : coefficientMatrix p a.f = 0) :
    Module.finrank K (PointedCotangent.Cotangent
      (fibreToBase p J.abelianVariety) (fibreIdentityPoint p J.abelianVariety)) = 2 := by
  rw [cotangent_finrank_of_verschiebung_zero p J.abelianVariety
    ((J.groupScheme_verschiebungCotangent_eq_zero_iff p).mpr
      ((a.jacobian_verschiebungCotangent_zero_iff_matrix p hf hd hp J).mpr hC))]
  exact a.genus_eq_two hf hd

end SupersingularCurves.Hyperelliptic.SimpleRootModel
