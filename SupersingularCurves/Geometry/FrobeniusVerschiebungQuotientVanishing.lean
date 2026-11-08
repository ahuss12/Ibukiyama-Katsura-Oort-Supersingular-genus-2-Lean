/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusVerschiebungQuotientFactorCotangent
import SupersingularCurves.Geometry.RankOneFactorCancellation

/-!
# Vanishing on the constructed quotient from the actual cotangent factors

This step applies rank-one cancellation to the differentials of the actual
quotient and residual Verschiebung. The fourfold composite is the actual
successive Verschiebung differential, with all Frobenius twists retained.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

variable {K : Type u} [Field K] [IsAlgClosed K]
  {p : ℕ} [Fact p.Prime] [CharP K p] {g : ℕ} {A : AbelianVariety K g}
  (D : QuotientData p A)

local instance quotient_smooth : Smooth D.group.X.hom := D.smooth

/-- Rank-one actual quotient factors and a vanishing actual twofold
Verschiebung imply vanishing of the quotient's own Verschiebung differential. -/
theorem verschiebungCotangent_eq_zero_of_factor_ranks
    (hq : Module.finrank K (LinearMap.range D.quotientCotangent) = 1)
    (hψ : Module.finrank K (LinearMap.range D.verschiebungFactorTwistCotangent) = 1)
    (hV : GroupScheme.verschiebungCotangent p A.group
      (GroupScheme.law_commutative A.group) ≠ 0)
    (hVtw : D.verschiebungTwistCotangent ≠ 0)
    (hsquare : D.verschiebungTwistCotangent ∘ₗ
      GroupScheme.verschiebungCotangent p A.group
        (GroupScheme.law_commutative A.group) = 0) :
    GroupScheme.verschiebungCotangent p D.group
      (GroupScheme.law_commutative D.group) = 0 := by
  rw [D.verschiebungCotangent_eq_quotient_comp_factor] at hV hsquare
  rw [D.verschiebungTwistCotangent_eq_quotientTwist_comp_factorTwist] at hVtw hsquare
  rw [D.quotient_verschiebungCotangent_eq_factorTwist_comp_quotient]
  exact RankOneFactorCancellation.middle_comp_eq_zero D.verschiebungFactorCotangent
    D.quotientCotangent D.verschiebungFactorTwistCotangent D.quotientTwistCotangent
    hq hψ hV hVtw hsquare

end SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData
