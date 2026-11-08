/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.CotangentDifferentialKernel
import SupersingularCurves.Geometry.SmoothDifferentialDetection
import SupersingularCurves.Geometry.GroupTranslationCotangent
import SupersingularCurves.Geometry.FrobeniusFactorIsomorphism

/-!
# Frobenius descent from actual pointed cotangent vanishing

For a morphism with smooth source over an algebraically closed field,
vanishing on all actual pointed cotangents implies an actual relative
Frobenius factorization. For a group homomorphism it suffices to check the
identity. Applied to the genuine Verschiebung of an abelian variety, the
residual factor is an isomorphism by its proven finite-flat degree.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

namespace SupersingularCurves.Geometry
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace PointedCotangent
variable {K : Type u} [Field K] [IsAlgClosed K] {X Y : Scheme.{u}}
  (c : X ⟶ Spec (CommRingCat.of K)) (d : Y ⟶ Spec (CommRingCat.of K))
  (p : ℕ) [Fact p.Prime] [CharP K p] [Smooth c]

/-- A morphism from a smooth scheme whose actual rational cotangent maps
vanish factors uniquely through the actual relative Frobenius. -/
theorem existsUnique_relative_factor_of_differential_eq_zero
    (f : X ⟶ Y) (hf : f ≫ d = c)
    (h : ∀ s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c,
      differential c s (z := imagePoint c d s f hf) f hf rfl = 0) :
    ∃! g : SchemeFrobenius.Twist p c ⟶ Y,
      SchemeFrobenius.relative p c ≫ g = f ∧
        g ≫ d = SchemeFrobenius.toBase p c := by
  apply SmoothDifferentialDetection.existsUnique_relative_factor_of_rational_stalk_D_mem
    c p f d hf
  intro s
  dsimp only
  intro b
  exact D_stalkMap_mem_maximalIdeal_smul_of_differential_eq_zero c d s f hf (h s) b

end PointedCotangent

namespace GroupTranslation
variable {K : Type u} [Field K] [IsAlgClosed K] {X Y : Scheme.{u}}
  {c : X ⟶ Spec (CommRingCat.of K)} {d : Y ⟶ Spec (CommRingCat.of K)}
  (p : ℕ) [Fact p.Prime] [CharP K p] [Smooth c]
  (L : RelativeGroupLaw K c) (M : RelativeGroupLaw K d)
  (f : X ⟶ Y) (hf : f ≫ d = c)
  (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x y : SchemeHomOver t c),
    mapPoint f hf (L.mul t x y) = M.mul t (mapPoint f hf x) (mapPoint f hf y))
  (hone : (L.one (𝟙 _)).1 ≫ f = (M.one (𝟙 _)).1)

include hmul in
/-- For an actual group morphism, zero differential at the identity
suffices for the unique scheme-theoretic relative Frobenius factorization. -/
theorem existsUnique_relative_factor_of_identity_differential_eq_zero
    (h : PointedCotangent.differential c (L.one (𝟙 _)) f hf hone = 0) :
    ∃! g : SchemeFrobenius.Twist p c ⟶ Y,
      SchemeFrobenius.relative p c ≫ g = f ∧
        g ≫ d = SchemeFrobenius.toBase p c := by
  apply PointedCotangent.existsUnique_relative_factor_of_differential_eq_zero c d p f hf
  intro s
  exact (differential_eq_zero_iff_at_point L M f hf hmul hone s).mp h

end GroupTranslation

namespace PerfectFieldVerschiebung
open SchemeFrobenius
variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
  (p : ℕ) [Fact p.Prime] [CharP K p]
  (c : X ⟶ Spec (CommRingCat.of K)) [Smooth c]
  (L : RelativeGroupLaw K c) (hc : L.IsCommutative)

/-- Actual Verschiebung factors uniquely through relative Frobenius of
its actual twist when its identity cotangent map is zero. -/
theorem existsUnique_relative_factor_of_differential_eq_zero
    (h : PointedCotangent.differential (toBase p c) ((twistLaw p c L).one (𝟙 _))
      (verschiebung p c L hc) (verschiebung_over p c L hc)
      (verschiebung_zero p c L hc) = 0) :
    ∃! g : Twist p (toBase p c) ⟶ X,
      relative p (toBase p c) ≫ g = verschiebung p c L hc ∧
        g ≫ c = toBase p (toBase p c) := by
  have : Smooth (toBase p c) := by
    change Smooth (CategoryTheory.Limits.pullback.snd c (baseMap p K))
    infer_instance
  exact GroupTranslation.existsUnique_relative_factor_of_identity_differential_eq_zero
    p (twistLaw p c L) L (verschiebung p c L hc) (verschiebung_over p c L hc)
    (fun t x y => verschiebung_mul p c L hc t x y) (verschiebung_zero p c L hc) h

end PerfectFieldVerschiebung

namespace AbelianVariety
open SchemeFrobenius PerfectFieldVerschiebung
variable {K : Type u} [Field K] [IsAlgClosed K] {g : ℕ}
  (A : AbelianVariety K g) (p : ℕ) [Fact p.Prime] [CharP K p]

local instance : Smooth A.group.X.hom :=
  SmoothOfRelativeDimension.smooth g A.group.X.hom

/-- Zero actual Verschiebung cotangent gives an actual scheme isomorphism
from the double Frobenius twist, with the genuine factorization identity. -/
theorem exists_frobenius_factor_iso_of_verschiebungCotangent_eq_zero
    (h : GroupScheme.verschiebungCotangent p A.group A.groupScheme_law_commutative = 0) :
    ∃ e : Twist p (toBase p A.group.X.hom) ≅ A.group.X.left,
      relative p (toBase p A.group.X.hom) ≫ e.hom =
        verschiebung p A.group.X.hom (GroupScheme.law A.group) A.groupScheme_law_commutative ∧
      e.hom ≫ A.group.X.hom = toBase p (toBase p A.group.X.hom) := by
  obtain ⟨W, hW, _⟩ :=
    PerfectFieldVerschiebung.existsUnique_relative_factor_of_differential_eq_zero
      p A.group.X.hom (GroupScheme.law A.group) A.groupScheme_law_commutative h
  let := A.isIso_of_frobenius_factor_verschiebung p W hW.1
  exact ⟨asIso W, hW⟩

end AbelianVariety

namespace Jacobian
open SchemeFrobenius AlgebraicCurve
variable {K : Type u} [Field K] [IsAlgClosed K]
  {F : Type v} [Field F] [Algebra K F]
  {M : CurveModel K F}
  {s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase}
  (J : Jacobian M s) (p : ℕ) [Fact p.Prime] [CharP K p]

/-- The same actual isomorphism theorem for the independently constructed
Jacobian and its pre-existing cotangent Verschiebung operator. -/
theorem exists_frobenius_factor_iso_of_verschiebungCotangent_eq_zero
    (h : J.verschiebungCotangent p = 0) :
    ∃ e : Twist p (J.twistToBase p) ≅ J.designation.P,
      relative p (J.twistToBase p) ≫ e.hom = J.verschiebung p ∧
        e.hom ≫ J.designation.toBase = toBase p (J.twistToBase p) := by
  exact J.abelianVariety.exists_frobenius_factor_iso_of_verschiebungCotangent_eq_zero p
    ((J.groupScheme_verschiebungCotangent_eq_zero_iff p).mpr h)

end Jacobian

end SupersingularCurves.Geometry
