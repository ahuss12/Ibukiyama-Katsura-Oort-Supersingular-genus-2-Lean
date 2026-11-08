/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusVerschiebungQuotientDegree
import SupersingularCurves.Hyperelliptic.GenusTwoSubgroupOrder

/-!
# The actual degree-p quotient from nonzero square-zero Cartier

The simultaneous-kernel quotient is an actual abelian variety. For every
represented separable genus-two quintic or sextic, its map from the first
Jacobian twist is an actual degree-p isogeny when Cartier is square zero and
nonzero. The quotient is not asserted to be superspecial here.
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

/-- The constructed quotient map has actual scheme degree p everywhere. -/
theorem jacobian_quotient_finrank_eq_prime_of_matrix
    (hC2 : (coefficientMatrix p a.f).map (fun c => c ^ p) * coefficientMatrix p a.f = 0)
    (hC : coefficientMatrix p a.f ≠ 0)
    (y : (quotientData p J.abelianVariety).carrier) :
    (quotientData p J.abelianVariety).quotientMap.finrank y = p := by
  rw [QuotientData.finrank_eq_subgroup]
  exact a.jacobian_subgroup_order_eq_prime_of_matrix p hf hd hp J hC2 hC

/-- Nonzero square-zero full global Cartier constructs an actual degree-p
isogeny from the first Jacobian twist to an actual abelian variety of the same genus. -/
theorem jacobian_exists_degree_prime_quotient_of_globalCartier
    (hC2 : ∀ ω : a.GlobalForms, a.globalCartier p (a.globalCartier p ω) = 0)
    (hC : ¬ ∀ ω : a.GlobalForms, a.globalCartier p ω = 0) :
    ∃ B : AbelianVariety K (genusFF K a.FunctionField),
      ∃ q : twistGroup p J.abelianVariety ⟶ B.group,
        IsIsogeny q ∧ ∀ y : B.group.X.left, q.hom.hom.left.finrank y = p := by
  let D := quotientData p J.abelianVariety
  refine ⟨D.abelianVariety, D.quotientHom, D.quotientHom_isIsogeny, ?_⟩
  change ∀ y : D.carrier, D.quotientMap.finrank y = p
  intro y
  rw [D.finrank_eq_subgroup]
  exact a.jacobian_subgroup_order_eq_prime_of_globalCartier p hf hd hp J hC2 hC

end SupersingularCurves.Hyperelliptic.SimpleRootModel
