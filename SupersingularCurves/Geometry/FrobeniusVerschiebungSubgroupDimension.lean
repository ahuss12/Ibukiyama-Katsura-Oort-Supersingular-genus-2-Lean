/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.PRankZeroFiniteSubgroup
import SupersingularCurves.Geometry.PointedCotangentFibreExact

/-!
# The dimension of the actual simultaneous Frobenius--Verschiebung kernel

The actual finite subgroup `ker F ∩ ker V` has cotangent dimension equal to
the ambient abelian dimension minus the rank of the actual Verschiebung
differential. In dimension two, rank-one Verschiebung gives cotangent dimension
one. Neither a subgroup-order formula nor a classification theorem is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open GoodReductionJacobian SchemeFrobenius PerfectFieldVerschiebung

variable {K : Type u} [Field K]
variable (p : ℕ) [Fact p.Prime] [CharP K p] [IsAlgClosed K]
variable {g : ℕ} (A : AbelianVariety K g)

/-- The actual V-kernel cotangent dimension, computed by the actual fibre
cotangent exact sequence and smooth relative dimension. -/
theorem vKernel_cotangent_finrank :
    Module.finrank K (PointedCotangent.Cotangent (vToBase p A) (vIdentityPoint p A)) =
      g - Module.finrank K (LinearMap.range (GroupScheme.verschiebungCotangent p A.group
        (GroupScheme.law_commutative A.group))) := by
  let : SmoothOfRelativeDimension g (base p A) := by
    change SmoothOfRelativeDimension g (pullback.snd A.group.X.hom (baseMap p K))
    exact (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
      (IsPullback.of_hasPullback A.group.X.hom (baseMap p K)) A.smooth
  let : Smooth (base p A) := SmoothOfRelativeDimension.smooth g (base p A)
  let : Module.Finite K (PointedCotangent.Cotangent (base p A) ((law p A).one (𝟙 _))) :=
    PointedCotangent.finite_of_locallyOfFiniteType (base p A) ((law p A).one (𝟙 _))
  have h := PointedCotangent.Fibre.finrank_eq_sub_rank_differential (base p A)
    ((law p A).one (𝟙 _)) (V p A)
    (verschiebung_over p A.group.X.hom (GroupScheme.law A.group) A.groupScheme_law_commutative)
    (verschiebung_zero p A.group.X.hom (GroupScheme.law A.group) A.groupScheme_law_commutative)
  rw [PointedCotangent.finrank_eq_relativeDimension (base p A) ((law p A).one (𝟙 _)) g] at h
  exact h

/-- The actual simultaneous kernel has the same cotangent dimension as
ker V, because Frobenius has zero differential even on this finite scheme. -/
theorem cotangent_finrank_eq_vKernel :
    Module.finrank K (PointedCotangent.Cotangent (fibreToBase p A) (fibreIdentityPoint p A)) =
      Module.finrank K (PointedCotangent.Cotangent (vToBase p A) (vIdentityPoint p A)) :=
  (LinearEquiv.finrank_eq (LinearEquiv.ofBijective _ (cotangent_bijective p A))).symm

/-- The cotangent dimension formula for the actual finite subgroup. -/
theorem cotangent_finrank :
    Module.finrank K (PointedCotangent.Cotangent (fibreToBase p A) (fibreIdentityPoint p A)) =
      g - Module.finrank K (LinearMap.range (GroupScheme.verschiebungCotangent p A.group
        (GroupScheme.law_commutative A.group))) :=
  (cotangent_finrank_eq_vKernel p A).trans (vKernel_cotangent_finrank p A)

/-- Rank-one actual Verschiebung on a surface produces a one-dimensional
cotangent space of its actual simultaneous finite subgroup. -/
theorem cotangent_finrank_eq_one_of_surface_rank_one (A : AbelianVariety K 2)
    (hV : Module.finrank K (LinearMap.range (GroupScheme.verschiebungCotangent p A.group
      (GroupScheme.law_commutative A.group))) = 1) :
    Module.finrank K (PointedCotangent.Cotangent (fibreToBase p A) (fibreIdentityPoint p A)) = 1 := by
  rw [cotangent_finrank, hV]

/-- Vanishing actual Verschiebung gives the full ambient cotangent
dimension for the actual simultaneous finite subgroup. -/
theorem cotangent_finrank_of_verschiebung_zero
    (hV : GroupScheme.verschiebungCotangent p A.group (GroupScheme.law_commutative A.group) = 0) :
    Module.finrank K (PointedCotangent.Cotangent (fibreToBase p A) (fibreIdentityPoint p A)) = g := by
  rw [cotangent_finrank, hV, LinearMap.range_zero, finrank_bot, Nat.sub_zero]

/-- On a p-rank-zero surface, a nonzero actual Verschiebung differential
has rank one. This follows from the nontrivial actual kernel cotangent space. -/
theorem verschiebung_rank_eq_one_of_surface_pRank_zero (A : AbelianVariety K 2)
    (hA : A.HasPRankOver p 0)
    (hV : GroupScheme.verschiebungCotangent p A.group (GroupScheme.law_commutative A.group) ≠ 0) :
    Module.finrank K (LinearMap.range (GroupScheme.verschiebungCotangent p A.group
      (GroupScheme.law_commutative A.group))) = 1 := by
  let : Smooth (base p A) := by
    change Smooth (pullback.snd A.group.X.hom (baseMap p K))
    infer_instance
  let : Module.Finite K (PointedCotangent.Cotangent (base p A) ((law p A).one (𝟙 _))) :=
    PointedCotangent.finite_of_locallyOfFiniteType (base p A) ((law p A).one (𝟙 _))
  let : Module.Finite K (PointedCotangent.Cotangent (vToBase p A) (vIdentityPoint p A)) :=
    PointedCotangent.finite_of_locallyOfFiniteType (vToBase p A) (vIdentityPoint p A)
  let : Module.Finite K (PointedCotangent.Cotangent A.group.X.hom (GroupScheme.zero A.group)) :=
    PointedCotangent.finite_of_locallyOfFiniteType A.group.X.hom (GroupScheme.zero A.group)
  let : Nontrivial (PointedCotangent.Cotangent (vToBase p A) (vIdentityPoint p A)) :=
    not_subsingleton_iff_nontrivial.mp (vKernel_cotangent_not_subsingleton p A hA (by decide))
  have hpos := Module.finrank_pos (R := K)
    (M := PointedCotangent.Cotangent (vToBase p A) (vIdentityPoint p A))
  have hdim := vKernel_cotangent_finrank p A
  have hrank : Module.finrank K (LinearMap.range (GroupScheme.verschiebungCotangent p A.group
      (GroupScheme.law_commutative A.group))) ≠ 0 := by
    intro hr
    apply hV
    exact LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hr)
  omega

/-- The actual simultaneous subgroup of a p-rank-zero surface with
nonzero Verschiebung differential has cotangent dimension one. -/
theorem cotangent_finrank_eq_one_of_surface_pRank_zero (A : AbelianVariety K 2)
    (hA : A.HasPRankOver p 0)
    (hV : GroupScheme.verschiebungCotangent p A.group (GroupScheme.law_commutative A.group) ≠ 0) :
    Module.finrank K (PointedCotangent.Cotangent (fibreToBase p A) (fibreIdentityPoint p A)) = 1 :=
  cotangent_finrank_eq_one_of_surface_rank_one p A
    (verschiebung_rank_eq_one_of_surface_pRank_zero p A hA hV)

/-- The dimension-two conclusion with an explicit dimension equality, so
an actual Jacobian with its intrinsic genus index needs no external transport. -/
theorem cotangent_finrank_eq_one_of_dimension_two (hg : g = 2)
    (hA : A.HasPRankOver p 0)
    (hV : GroupScheme.verschiebungCotangent p A.group (GroupScheme.law_commutative A.group) ≠ 0) :
    Module.finrank K (PointedCotangent.Cotangent (fibreToBase p A) (fibreIdentityPoint p A)) = 1 := by
  subst g
  exact cotangent_finrank_eq_one_of_surface_pRank_zero p A hA hV

end SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup
