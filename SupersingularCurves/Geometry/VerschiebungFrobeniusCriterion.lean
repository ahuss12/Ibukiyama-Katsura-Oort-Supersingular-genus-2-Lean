/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.RationalCotangentFrobenius
import SupersingularCurves.Geometry.FrobeniusCotangentVanishing
import SupersingularCurves.Geometry.FrobeniusFactorGroup

/-!
# A geometric Frobenius-factor criterion for zero Verschiebung differential

The criterion uses actual morphisms of schemes and the independently
constructed Verschiebung. It does not identify a double-twist isomorphism
with an elliptic-product decomposition.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

namespace SupersingularCurves.Geometry
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open SchemeFrobenius

namespace PointedCotangent
variable {K : Type u} [Field K] {X Y : Scheme.{u}}
  (c : X ⟶ Spec (CommRingCat.of K)) (d : Y ⟶ Spec (CommRingCat.of K))
  (p : ℕ) [Fact p.Prime] [CharP K p]
  (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)
  (z : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) d)
  (f : X ⟶ Y) (hf : f ≫ d = c) (hs : s.1 ≫ f = z.1)

/-- A morphism factoring through actual relative Frobenius has zero
actual cotangent differential at every pointed rational point. -/
theorem differential_eq_zero_of_relative_factor
    (W : Twist p c ⟶ Y) (hW : W ≫ d = toBase p c)
    (hfactor : relative p c ≫ W = f) :
    differential c s f hf hs = 0 := by
  have hz : (twistedSection p c s).1 ≫ W = z.1 := by
    rw [← section_relative p c s, Category.assoc, hfactor, hs]
  have hcomp := differential_comp c s (relative p c) (relative_toBase p c)
    (section_relative p c s) W hW hz
  rw [relative_differential_eq_zero, LinearMap.zero_comp] at hcomp
  simpa only [hfactor] using hcomp

end PointedCotangent

namespace AbelianVariety
open PerfectFieldVerschiebung
variable {K : Type u} [Field K] [IsAlgClosed K] {g : ℕ}
  (A : AbelianVariety K g) (p : ℕ) [Fact p.Prime] [CharP K p]

local instance : Smooth A.group.X.hom :=
  SmoothOfRelativeDimension.smooth g A.group.X.hom
local instance : Smooth (toBase p A.group.X.hom) := by
  change Smooth (CategoryTheory.Limits.pullback.snd A.group.X.hom (baseMap p K))
  infer_instance

/-- Actual Frobenius factorization is equivalent to zero actual
Verschiebung cotangent. The over-base identity is forced by the factorization. -/
theorem verschiebungCotangent_eq_zero_iff_exists_frobenius_factor :
    GroupScheme.verschiebungCotangent p A.group A.groupScheme_law_commutative = 0 ↔
      ∃ W : Twist p (toBase p A.group.X.hom) ⟶ A.group.X.left,
        relative p (toBase p A.group.X.hom) ≫ W =
          verschiebung p A.group.X.hom (GroupScheme.law A.group) A.groupScheme_law_commutative := by
  constructor
  · intro h
    obtain ⟨e, he, _⟩ := A.exists_frobenius_factor_iso_of_verschiebungCotangent_eq_zero p h
    exact ⟨e.hom, he⟩
  · rintro ⟨W, hfactor⟩
    have hF := finite_flat_surjective p (toBase p A.group.X.hom)
    have : IsFinite (relative p (toBase p A.group.X.hom)) := hF.1
    have : Flat (relative p (toBase p A.group.X.hom)) := hF.2.1
    have : Surjective (relative p (toBase p A.group.X.hom)) := hF.2.2.2
    have hW : W ≫ A.group.X.hom = toBase p (toBase p A.group.X.hom) := by
      apply (cancel_epi (relative p (toBase p A.group.X.hom))).mp
      rw [← Category.assoc, hfactor, verschiebung_over, relative_toBase]
    exact PointedCotangent.differential_eq_zero_of_relative_factor
      (toBase p A.group.X.hom) A.group.X.hom p (GroupScheme.twistZero p A.group)
      (GroupScheme.zero A.group)
      (verschiebung p A.group.X.hom (GroupScheme.law A.group) A.groupScheme_law_commutative)
      (verschiebung_over p A.group.X.hom (GroupScheme.law A.group) A.groupScheme_law_commutative)
      (verschiebung_zero p A.group.X.hom (GroupScheme.law A.group) A.groupScheme_law_commutative)
      W hW hfactor

/-- The same criterion with an actual isomorphism of schemes as residual
factor, rather than an unspecified residual morphism. -/
theorem verschiebungCotangent_eq_zero_iff_exists_frobenius_factor_iso :
    GroupScheme.verschiebungCotangent p A.group A.groupScheme_law_commutative = 0 ↔
      ∃ e : Twist p (toBase p A.group.X.hom) ≅ A.group.X.left,
        relative p (toBase p A.group.X.hom) ≫ e.hom =
          verschiebung p A.group.X.hom (GroupScheme.law A.group) A.groupScheme_law_commutative ∧
        e.hom ≫ A.group.X.hom = toBase p (toBase p A.group.X.hom) := by
  refine ⟨A.exists_frobenius_factor_iso_of_verschiebungCotangent_eq_zero p, ?_⟩
  rintro ⟨e, he, _⟩
  exact (A.verschiebungCotangent_eq_zero_iff_exists_frobenius_factor p).mpr ⟨e.hom, he⟩

/-- Zero actual Verschiebung cotangent is equivalent to a residual
isomorphism of the genuine double-twist group scheme, with actual factor identity. -/
theorem verschiebungCotangent_eq_zero_iff_exists_frobenius_factor_groupIso :
    GroupScheme.verschiebungCotangent p A.group A.groupScheme_law_commutative = 0 ↔
      ∃ e : A.doubleFrobeniusTwistGroup p ≅ A.group,
        relative p (toBase p A.group.X.hom) ≫ e.hom.hom.hom.left =
          verschiebung p A.group.X.hom (GroupScheme.law A.group) A.groupScheme_law_commutative := by
  constructor
  · intro h
    obtain ⟨W, hW⟩ := (A.verschiebungCotangent_eq_zero_iff_exists_frobenius_factor p).mp h
    exact ⟨A.frobeniusFactorGroupIso p W hW, by simpa using hW⟩
  · rintro ⟨e, he⟩
    exact (A.verschiebungCotangent_eq_zero_iff_exists_frobenius_factor p).mpr
      ⟨e.hom.hom.hom.left, he⟩

end AbelianVariety

namespace Jacobian
open AlgebraicCurve
variable {K : Type u} [Field K] [IsAlgClosed K]
  {F : Type v} [Field F] [Algebra K F]
  {M : CurveModel K F}
  {s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase}
  (J : Jacobian M s) (p : ℕ) [Fact p.Prime] [CharP K p]

/-- The geometric factor criterion uses the pre-existing actual Jacobian
cotangent Verschiebung, without replacing it by a matrix definition. -/
theorem verschiebungCotangent_eq_zero_iff_exists_frobenius_factor :
    J.verschiebungCotangent p = 0 ↔
      ∃ W : Twist p (J.twistToBase p) ⟶ J.designation.P,
        relative p (J.twistToBase p) ≫ W = J.verschiebung p := by
  rw [← J.groupScheme_verschiebungCotangent_eq_zero_iff p]
  exact J.abelianVariety.verschiebungCotangent_eq_zero_iff_exists_frobenius_factor p

/-- Zero Jacobian cotangent Verschiebung is equivalent to the actual
Frobenius factorization with residual scheme isomorphism. -/
theorem verschiebungCotangent_eq_zero_iff_exists_frobenius_factor_iso :
    J.verschiebungCotangent p = 0 ↔
      ∃ e : Twist p (J.twistToBase p) ≅ J.designation.P,
        relative p (J.twistToBase p) ≫ e.hom = J.verschiebung p ∧
        e.hom ≫ J.designation.toBase = toBase p (J.twistToBase p) := by
  rw [← J.groupScheme_verschiebungCotangent_eq_zero_iff p]
  exact J.abelianVariety.verschiebungCotangent_eq_zero_iff_exists_frobenius_factor_iso p

/-- The equivalent residual group-isomorphism criterion for the actual
Jacobian. Its group law is the independently constructed Picard group law. -/
theorem verschiebungCotangent_eq_zero_iff_exists_frobenius_factor_groupIso :
    J.verschiebungCotangent p = 0 ↔
      ∃ e : J.abelianVariety.doubleFrobeniusTwistGroup p ≅ J.abelianVariety.group,
        relative p (J.twistToBase p) ≫ e.hom.hom.hom.left = J.verschiebung p := by
  rw [← J.groupScheme_verschiebungCotangent_eq_zero_iff p]
  exact J.abelianVariety.verschiebungCotangent_eq_zero_iff_exists_frobenius_factor_groupIso p

end Jacobian
end SupersingularCurves.Geometry
