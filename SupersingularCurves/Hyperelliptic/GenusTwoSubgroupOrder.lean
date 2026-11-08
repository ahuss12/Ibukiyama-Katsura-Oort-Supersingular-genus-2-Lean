/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroupOrder
import SupersingularCurves.Hyperelliptic.GenusTwoFiniteSubgroup

/-!
# Order p of the actual subgroup for nonzero square-zero Cartier

For every presented separable genus-two quintic or sextic in odd
characteristic, nonzero square-zero Cartier gives scheme-theoretic order p
for the actual simultaneous Frobenius--Verschiebung subgroup of every
representing Jacobian. No quotient or elliptic-product isogeny is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace SupersingularCurves.Hyperelliptic.SimpleRootModel
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open NeronModelInfra GoodReductionJacobian
open SupersingularCurves.Geometry SupersingularCurves.IKO SupersingularCurves.Differentials
open FrobeniusVerschiebungSubgroup

variable {K : Type*} [Field K] [IsAlgClosed K] [NeZero (2 : K)]
  (a : SimpleRootModel K) (p : ℕ) [Fact p.Prime] [CharP K p]
  (hf : a.f.Separable) (hd : a.f.natDegree = 5 ∨ a.f.natDegree = 6)
  (hp : p % 2 = 1)
  {s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) a.curveModel.toBase}
  (J : Jacobian a.curveModel s)

include hf hd hp

/-- Twisted-square-zero but nonzero matrix gives actual subgroup order p,
with the subgroup and all scheme-theoretic hypotheses already constructed. -/
theorem jacobian_subgroup_order_eq_prime_of_matrix
    (hC2 : (coefficientMatrix p a.f).map (fun c => c ^ p) * coefficientMatrix p a.f = 0)
    (hC : coefficientMatrix p a.f ≠ 0) :
    (toBase p J.abelianVariety).finrank (IsLocalRing.closedPoint K) = p :=
  finrank_eq_prime_of_fibre_cotangent_dimension_one p J.abelianVariety
    (a.jacobian_subgroup_cotangent_finrank_one_of_matrix p hf hd hp J hC2 hC)

/-- Full global Cartier square zero but nonzero implies order p of the
actual simultaneous subgroup in the first Jacobian Frobenius twist. -/
theorem jacobian_subgroup_order_eq_prime_of_globalCartier
    (hC2 : ∀ ω : a.GlobalForms, a.globalCartier p (a.globalCartier p ω) = 0)
    (hC : ¬ ∀ ω : a.GlobalForms, a.globalCartier p ω = 0) :
    (toBase p J.abelianVariety).finrank (IsLocalRing.closedPoint K) = p :=
  finrank_eq_prime_of_fibre_cotangent_dimension_one p J.abelianVariety
    (a.jacobian_subgroup_cotangent_finrank_one_of_globalCartier p hf hd hp J hC2 hC)


/-- The same actual order theorem using Cartier on the entire space of
regular function-field differentials. -/
theorem jacobian_subgroup_order_eq_prime_of_regularCartier
    (hC2 : ∀ ω : regularDifferentials K a.FunctionField,
      regularCartier p a.x (regularCartier p a.x ω) = 0)
    (hC : ¬ ∀ ω : regularDifferentials K a.FunctionField, regularCartier p a.x ω = 0) :
    (toBase p J.abelianVariety).finrank (IsLocalRing.closedPoint K) = p :=
  a.jacobian_subgroup_order_eq_prime_of_matrix p hf hd hp J
    ((a.all_regularCartier_square_zero_iff hf hd p hp).mp hC2)
    (fun h => hC ((a.all_regularCartier_zero_iff hf hd p hp).mpr h))

end SupersingularCurves.Hyperelliptic.SimpleRootModel
