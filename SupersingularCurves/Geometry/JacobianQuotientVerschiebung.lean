/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.JacobianQuotientCotangent
import SupersingularCurves.Geometry.FrobeniusVerschiebungQuotientFactorCotangentRank
import SupersingularCurves.Geometry.FrobeniusVerschiebungQuotientVanishing

/-!
# The genus-two quotient has zero actual Verschiebung differential

For a p-rank-zero Jacobian surface with nonzero Cartier and Cartier squared
zero, the constructed quotient by the actual simultaneous F/V kernel has
zero actual Verschiebung differential. Its degree-p factor ranks, successive
Verschiebung square, and twisted nonvanishing are all proved independently.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

namespace SupersingularCurves.Geometry.Jacobian
open CategoryTheory AlgebraicGeometry AlgebraicCurve NeronModelInfra GoodReductionJacobian
open FrobeniusVerschiebungSubgroup

variable {K : Type u} [Field K] [IsAlgClosed K]
variable {F : Type v} [Field F] [Algebra K F]
variable {M : CurveModel K F}
  {s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase}
variable (J : Jacobian M s)
variable (p : ℕ) [Fact p.Prime] [CharP K p]
variable [Algebra.EssFiniteType K F] [IsCurveOver K F]
variable (D : QuotientData p J.abelianVariety)
variable (V : DifferentialChart M)
variable (x : F) [FiniteDimensional (IntermediateField.adjoin K {x}) F]

local instance quotient_smooth : Smooth D.group.X.hom := D.smooth

/-- The actual simultaneous-kernel quotient of a genus-two p-rank-zero
Jacobian with Cartier squared zero and nonzero V has zero V differential. -/
theorem quotient_verschiebungCotangent_eq_zero_of_globalCartier_square_zero
    (hg : genusFF K F = 2) (hA : J.abelianVariety.HasPRankOver p 0)
    (hV : J.verschiebungCotangent p ≠ 0)
    (hzero : ∀ ω : V.GlobalForms, V.globalCartier p x (V.globalCartier p x ω) = 0) :
    GroupScheme.verschiebungCotangent p D.group
      (GroupScheme.law_commutative D.group) = 0 := by
  have hVG : GroupScheme.verschiebungCotangent p J.abelianVariety.group
      (GroupScheme.law_commutative J.abelianVariety.group) ≠ 0 := by
    intro h
    exact hV ((J.groupScheme_verschiebungCotangent_eq_zero_iff p).mp h)
  exact D.verschiebungCotangent_eq_zero_of_factor_ranks
    (D.quotientCotangent_finrank_eq_one hg hA hVG)
    (D.verschiebungFactorTwistCotangent_finrank_eq_one hg hA hVG) hVG
    (J.quotient_twistedVerschiebungCotangent_ne_zero p D V.cover hV)
    (J.quotient_twistedVerschiebungCotangent_comp_eq_zero_of_globalCartier_square_zero
      p D V x hzero)

omit D in
/-- A genus-two p-rank-zero Jacobian with Cartier squared zero admits a
genuine isogeny to an actual abelian surface with zero V differential.
The target is the constructed finite quotient when the original V is nonzero. -/
theorem exists_isogeny_to_zero_verschiebungCotangent_of_globalCartier_square_zero
    (hg : genusFF K F = 2) (hA : J.abelianVariety.HasPRankOver p 0)
    (hzero : ∀ ω : V.GlobalForms, V.globalCartier p x (V.globalCartier p x ω) = 0) :
    ∃ (B : AbelianVariety K (genusFF K F)) (f : J.abelianVariety.group ⟶ B.group),
      IsIsogeny f ∧ GroupScheme.verschiebungCotangent p B.group
        (GroupScheme.law_commutative B.group) = 0 := by
  by_cases hV : J.verschiebungCotangent p = 0
  · refine ⟨J.abelianVariety, 𝟙 _, isIsogeny_of_isIso (𝟙 _), ?_⟩
    exact (J.groupScheme_verschiebungCotangent_eq_zero_iff p).mpr hV
  · let Q := quotientData p J.abelianVariety
    refine ⟨Q.abelianVariety, Q.isogenyFromOriginal, Q.isogenyFromOriginal_isIsogeny, ?_⟩
    exact J.quotient_verschiebungCotangent_eq_zero_of_globalCartier_square_zero
      p Q V x hg hA hV hzero

end SupersingularCurves.Geometry.Jacobian
