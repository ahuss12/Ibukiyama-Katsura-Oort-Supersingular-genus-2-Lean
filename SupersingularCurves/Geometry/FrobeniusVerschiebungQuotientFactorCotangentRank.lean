/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FiniteIsogenyCotangentRank
import SupersingularCurves.Geometry.FrobeniusVerschiebungQuotientFactorCotangent
import SupersingularCurves.Geometry.FrobeniusVerschiebungQuotientFactorPoints
import SupersingularCurves.Geometry.FrobeniusBaseChangeDegree

/-!
# Actual cotangent ranks in the degree-p quotient diagram

The quotient and residual Verschiebung, including its actual Frobenius
base change, have rank-one cotangent maps in the p-rank-zero nonzero-dV
surface branch. Each rank is deduced from the actual degree-p finite
kernel and its actual group law.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.SchemeFrobenius
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open FrobeniusFactorGroup
variable {K : Type u} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
  {X Y : Scheme.{u}} {c : X ⟶ Spec (CommRingCat.of K)}
  {d : Y ⟶ Spec (CommRingCat.of K)} (f : X ⟶ Y) (hf : f ≫ d = c)

/-- The actual point equivalence of Frobenius base change commutes with
an actual base-preserving morphism. -/
theorem twistPointsEquiv_pointMap {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x : SchemeHomOver t (toBase p c)) :
    twistPointsEquiv p d t (pointMap (map p f hf) (map_toBase p f hf) x) =
      pointMap f hf (twistPointsEquiv p c t x) := by
  apply Subtype.ext
  change (x.1 ≫ map p f hf) ≫ projection p d = (x.1 ≫ projection p c) ≫ f
  rw [Category.assoc, map_projection, Category.assoc]

/-- Frobenius base change preserves actual group multiplication on every
test scheme, using its actual pullback point equivalence. -/
theorem map_mul (L : RelativeGroupLaw K c) (M : RelativeGroupLaw K d)
    (hm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
      (x y : SchemeHomOver t c),
      pointMap f hf (L.mul t x y) = M.mul t (pointMap f hf x) (pointMap f hf y))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x y : SchemeHomOver t (toBase p c)) :
    pointMap (map p f hf) (map_toBase p f hf) ((twistLaw p c L).mul t x y) =
      (twistLaw p d M).mul t (pointMap (map p f hf) (map_toBase p f hf) x)
        (pointMap (map p f hf) (map_toBase p f hf) y) := by
  apply (twistPointsEquiv p d t).injective
  rw [twistPointsEquiv_pointMap, twistLaw_mul, hm, twistLaw_mul,
    twistPointsEquiv_pointMap, twistPointsEquiv_pointMap]

end SupersingularCurves.Geometry.SchemeFrobenius

namespace SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open SchemeFrobenius FrobeniusFactorGroup PointedCotangent
variable {K : Type u} [Field K] [IsAlgClosed K]
  {p : ℕ} [Fact p.Prime] [CharP K p] {g : ℕ} {A : AbelianVariety K g}
  (D : QuotientData p A)

/-- Rank one of the actual quotient differential, derived from its
degree-p one-point group kernel. -/
theorem quotientCotangent_finrank_eq_one (hg : g = 2)
    (hA : A.HasPRankOver p 0)
    (hV : GroupScheme.verschiebungCotangent p A.group
      (GroupScheme.law_commutative A.group) ≠ 0) :
    Module.finrank K (LinearMap.range D.quotientCotangent) = 1 := by
  subst g
  have : SmoothOfRelativeDimension 2 (base p A) :=
    (sourceAbelianVariety (p := p) (A := A)).smooth
  apply GroupHomFibre.differential_finrank_eq_one
    (law p A) (GroupScheme.law D.group) D.quotientMap D.over_base
    (fun t x y => by
      simpa only [GroupScheme.law, group, relativeGroupLawOfGrpObj_grpObjOverMk_mul]
        using D.map_mul t x y) p
  · intro x hx
    apply D.quotientPoint_kernel_trivial x
    simpa only [GroupScheme.law, group, relativeGroupLawOfGrpObj_grpObjOverMk_one] using hx
  · exact D.finrank_eq_prime_of_dimension_two rfl hA hV _

/-- Rank one of the actual descended Verschiebung differential. -/
theorem verschiebungFactorCotangent_finrank_eq_one (hg : g = 2)
    (hA : A.HasPRankOver p 0)
    (hV : GroupScheme.verschiebungCotangent p A.group
      (GroupScheme.law_commutative A.group) ≠ 0) :
    Module.finrank K (LinearMap.range D.verschiebungFactorCotangent) = 1 := by
  subst g
  have : SmoothOfRelativeDimension 2 D.group.X.hom := D.smoothOfRelativeDimension
  apply GroupHomFibre.differential_finrank_eq_one
    (GroupScheme.law D.group) (GroupScheme.law A.group)
    D.verschiebungFactor.1 D.verschiebungFactor.2
    (fun t x y => by
      simpa only [GroupScheme.law, group, relativeGroupLawOfGrpObj_grpObjOverMk_mul]
        using D.verschiebungFactor_mul t x y) p
  · intro x hx
    simpa only [GroupScheme.law, group, relativeGroupLawOfGrpObj_grpObjOverMk_one]
      using D.verschiebungFactorPoint_kernel_trivial hA x hx
  · exact D.verschiebungFactor_finrank_eq_prime rfl hA hV _

/-- Rank one of the actual Frobenius base change of the residual
Verschiebung differential; no untwisted cotangent identification is used. -/
theorem verschiebungFactorTwistCotangent_finrank_eq_one (hg : g = 2)
    (hA : A.HasPRankOver p 0)
    (hV : GroupScheme.verschiebungCotangent p A.group
      (GroupScheme.law_commutative A.group) ≠ 0) :
    Module.finrank K (LinearMap.range D.verschiebungFactorTwistCotangent) = 1 := by
  subst g
  have : SmoothOfRelativeDimension 2 (SchemeFrobenius.toBase p D.structureMap) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 2).of_isPullback
      (IsPullback.of_hasPullback D.structureMap (baseMap p K)) D.smoothOfRelativeDimension
  have hm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
      (x y : SchemeHomOver t (SchemeFrobenius.toBase p D.structureMap)),
      pointMap (SchemeFrobenius.map p D.verschiebungFactor.1 D.verschiebungFactor.2)
        (map_toBase p D.verschiebungFactor.1 D.verschiebungFactor.2)
        ((twistLaw p D.structureMap (GroupScheme.law D.group)).mul t x y) =
      (law p A).mul t
        (pointMap (SchemeFrobenius.map p D.verschiebungFactor.1 D.verschiebungFactor.2)
          (map_toBase p D.verschiebungFactor.1 D.verschiebungFactor.2) x)
        (pointMap (SchemeFrobenius.map p D.verschiebungFactor.1 D.verschiebungFactor.2)
          (map_toBase p D.verschiebungFactor.1 D.verschiebungFactor.2) y) := by
    intro T t x y
    exact SchemeFrobenius.map_mul p D.verschiebungFactor.1 D.verschiebungFactor.2
      (GroupScheme.law D.group) (GroupScheme.law A.group)
      (fun t x y => by
        simpa only [GroupScheme.law, group, relativeGroupLawOfGrpObj_grpObjOverMk_mul]
          using D.verschiebungFactor_mul t x y) t x y
  apply GroupHomFibre.differential_finrank_eq_one
    (twistLaw p D.structureMap (GroupScheme.law D.group)) (law p A)
    (SchemeFrobenius.map p D.verschiebungFactor.1 D.verschiebungFactor.2)
    (map_toBase p D.verschiebungFactor.1 D.verschiebungFactor.2) hm p
  · intro x hx
    apply D.verschiebungFactorTwistPoint_injective hA
    exact hx.trans (GroupHomFibre.map_one
      (twistLaw p D.structureMap (GroupScheme.law D.group)) (law p A)
      (SchemeFrobenius.map p D.verschiebungFactor.1 D.verschiebungFactor.2)
      (map_toBase p D.verschiebungFactor.1 D.verschiebungFactor.2) hm (𝟙 _)).symm
  · exact map_finrank_eq_const p D.verschiebungFactor.1 D.verschiebungFactor.2 p
      (D.verschiebungFactor_finrank_eq_prime rfl hA hV) _

end SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData
