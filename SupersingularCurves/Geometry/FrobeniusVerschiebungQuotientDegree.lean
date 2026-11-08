/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusVerschiebungQuotient
import SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroupOrder
import SupersingularCurves.Geometry.VerschiebungZeroKernel

/-!
# The degree of the actual simultaneous-kernel quotient

The quotient equivalence relation identifies its finite-flat degree with the
actual subgroup order. Thus it is p in the nonzero-Verschiebung p-rank-zero
surface case, and p^g in the zero-Verschiebung case.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open NeronModelInfra GoodReductionJacobian
variable {K : Type u} [Field K] [IsAlgClosed K]
  {p : ℕ} [Fact p.Prime] [CharP K p] {g : ℕ} {A : AbelianVariety K g}
  (D : QuotientData p A)

/-- Every actual quotient fibre has length equal to the actual subgroup order. -/
theorem finrank_eq_subgroup (y : D.carrier) :
    D.quotientMap.finrank y = (toBase p A).finrank (IsLocalRing.closedPoint K) := by
  let : IsFinite (inclusion p A ≫ base p A) := structure_isFinite p A
  let : Flat (inclusion p A ≫ base p A) := structure_flat p A
  obtain ⟨x, rfl⟩ := D.quotientMap.surjective y
  rw [← Scheme.Hom.finrank_of_isPullback _ _ _ _ D.relation.flip x,
    Scheme.Hom.finrank_pullback_snd]
  congr 1
  exact Subsingleton.elim _ _

/-- The quotient is an actual degree-p isogeny for a p-rank-zero surface
with nonzero actual Verschiebung differential. -/
theorem finrank_eq_prime_of_dimension_two (hg : g = 2)
    (hA : A.HasPRankOver p 0)
    (hV : GroupScheme.verschiebungCotangent p A.group
      (GroupScheme.law_commutative A.group) ≠ 0) (y : D.carrier) :
    D.quotientMap.finrank y = p := by
  rw [D.finrank_eq_subgroup]
  exact FrobeniusVerschiebungSubgroup.finrank_eq_prime_of_dimension_two p A hg hA hV

/-- In the zero-differential branch, the actual quotient has degree p^g. -/
theorem finrank_of_verschiebungCotangent_eq_zero
    (hV : GroupScheme.verschiebungCotangent p A.group
      (GroupScheme.law_commutative A.group) = 0) (y : D.carrier) :
    D.quotientMap.finrank y = p ^ g := by
  rw [D.finrank_eq_subgroup]
  exact simultaneousKernel_finrank_of_verschiebungCotangent_eq_zero p A hV

end SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData
