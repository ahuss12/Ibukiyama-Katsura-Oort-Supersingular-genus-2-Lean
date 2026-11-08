/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroupGroup
import SupersingularCurves.Geometry.PRankZeroFiniteSubgroup

/-! # Identity comparisons for the actual simultaneous subgroup -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

variable {K : Type u} [Field K]
variable (p : ℕ) [Fact p.Prime] [CharP K p] [IsAlgClosed K]
variable {g : ℕ} (A : AbelianVariety K g)

theorem subgroupLaw_one_eq_identityPoint :
    (subgroupLaw p A).one (𝟙 (Spec (CommRingCat.of K))) = identityPoint p A := by
  simpa only [GroupScheme.zero, GroupScheme.law, subgroupGroup,
    relativeGroupLawOfGrpObj_grpObjOverMk_one] using subgroupGroup_zero p A

theorem structure_eq_fibreToBase : toBase p A = fibreToBase p A := structure_eq_snd p A

theorem identityPoint_coe_eq_fibreIdentityPoint :
    (identityPoint p A).1 = (fibreIdentityPoint p A).1 := by
  apply (cancel_mono (inclusion p A)).mp
  rw [identityPoint_inclusion]
  change twistZero p A = (fibreIdentityPoint p A).1 ≫
    pullback.fst (vInclusion p A ≫ F p A) (twiceTwistZero p A) ≫ vInclusion p A
  rw [← Category.assoc]
  dsimp only [fibreIdentityPoint, PointedCotangent.Fibre.point]
  rw [pullback.lift_fst, vIdentityPoint_inclusion]

end SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup
