/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.VerschiebungNaturality

/-!
# Translating the differential of a group morphism

Translations are genuine scheme isomorphisms constructed from the supplied
group law. Their naturality transports the zero differential at the identity
to every rational point, including for the independently constructed
Verschiebung morphism. This is a step toward Frobenius descent; it is not an
abelian-variety classification theorem or a Frobenius factorization theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

namespace SupersingularCurves.Geometry.GroupTranslation
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

variable {K : Type u} [Field K] {X Y : Scheme.{u}}
variable {c : X ⟶ Spec (CommRingCat.of K)}
  {d : Y ⟶ Spec (CommRingCat.of K)}
variable (L : RelativeGroupLaw K c)

/-- The constant test-scheme point defined by a rational point. -/
def constant {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c) : SchemeHomOver t c :=
  ⟨t ≫ a.1, by rw [Category.assoc, a.2, Category.comp_id]⟩

/-- Left translation by an actual rational point, as a scheme morphism. -/
def translate (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c) : X ⟶ X :=
  (L.mul c (constant c a) ⟨𝟙 X, Category.id_comp c⟩).1

theorem translate_over (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c) :
    translate L a ≫ c = c :=
  (L.mul c (constant c a) ⟨𝟙 X, Category.id_comp c⟩).2

/-- Translation acts on every test-scheme point by the original group law. -/
theorem translate_action
    (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (q : SchemeHomOver t c) :
    q.1 ≫ translate L a = (L.mul t (constant t a) q).1 := by
  have h := L.mul_natural c t q.1 q.2 (constant c a) ⟨𝟙 X, Category.id_comp c⟩
  have ha : schemeHomOverComp q.1 q.2 (constant c a) = constant t a := by
    apply Subtype.ext
    simp only [schemeHomOverComp_coe, constant, ← Category.assoc, q.2]
  have hq : schemeHomOverComp q.1 q.2
      (⟨𝟙 X, Category.id_comp c⟩ : SchemeHomOver c c) = q := by
    apply Subtype.ext
    exact Category.comp_id _
  rw [ha, hq] at h
  exact congrArg Subtype.val h

theorem translate_zero (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c) :
    (L.one (𝟙 _)).1 ≫ translate L a = a.1 := by
  rw [translate_action, L.mul_one]
  exact Category.id_comp _

theorem constant_inv {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c) :
    constant t (L.inv (𝟙 _) a) = L.inv t (constant t a) := by
  let := L.pointGroup t
  symm
  apply inv_eq_of_mul_eq_one_left
  change L.mul t (constant t (L.inv (𝟙 _) a)) (constant t a) = L.one t
  have h := L.mul_natural (𝟙 _) t t (Category.comp_id t) (L.inv (𝟙 _) a) a
  rw [L.inv_mul_cancel, L.one_natural] at h
  exact h.symm

theorem translate_comp_inv
    (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c) :
    translate L a ≫ translate L (L.inv (𝟙 _) a) = 𝟙 X := by
  rw [translate_action L _ c ⟨translate L a, translate_over L a⟩]
  change (L.mul c (constant c (L.inv (𝟙 _) a))
    (L.mul c (constant c a) ⟨𝟙 X, Category.id_comp c⟩)).1 = _
  rw [constant_inv, ← L.mul_assoc, L.inv_mul_cancel, L.one_mul]

theorem translate_inv_comp
    (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c) :
    translate L (L.inv (𝟙 _) a) ≫ translate L a = 𝟙 X := by
  rw [translate_action L _ c ⟨translate L (L.inv (𝟙 _) a), translate_over L _⟩]
  change (L.mul c (constant c a)
    (L.mul c (constant c (L.inv (𝟙 _) a)) ⟨𝟙 X, Category.id_comp c⟩)).1 = _
  rw [constant_inv, ← L.mul_assoc, L.mul_inv_cancel, L.one_mul]

/-- The scheme isomorphism underlying translation. -/
def translateIso (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c) : X ≅ X where
  hom := translate L a
  inv := translate L (L.inv (𝟙 _) a)
  hom_inv_id := translate_comp_inv L a
  inv_hom_id := translate_inv_comp L a

variable (M : RelativeGroupLaw K d)
variable (f : X ⟶ Y) (hf : f ≫ d = c)

/-- Composition on actual points induced by a base-preserving morphism. -/
def mapPoint {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    (q : SchemeHomOver t c) : SchemeHomOver t d :=
  ⟨q.1 ≫ f, by rw [Category.assoc, hf, q.2]⟩

variable (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
  (x y : SchemeHomOver t c),
  mapPoint f hf (L.mul t x y) = M.mul t (mapPoint f hf x) (mapPoint f hf y))

include hmul in
/-- Every genuine group morphism intertwines actual scheme translations. -/
theorem translate_natural
    (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c) :
    translate L a ≫ f = f ≫ translate M (mapPoint f hf a) := by
  rw [translate_action M _ c ⟨f, hf⟩]
  have h := hmul c (constant c a) ⟨𝟙 X, Category.id_comp c⟩
  have ha : mapPoint f hf (constant c a) = constant c (mapPoint f hf a) := by
    apply Subtype.ext
    exact Category.assoc _ _ _
  have hi : mapPoint f hf (⟨𝟙 X, Category.id_comp c⟩ : SchemeHomOver c c) =
      ⟨f, hf⟩ := by
    apply Subtype.ext
    exact Category.id_comp _
  rw [ha, hi] at h
  exact congrArg Subtype.val h

include hmul in
/-- The zero differential at the identity is equivalent to the zero
differential at each rational point. Both spaces are actual local cotangents. -/
theorem differential_eq_zero_iff_at_point
    (hone : (L.one (𝟙 _)).1 ≫ f = (M.one (𝟙 _)).1)
    (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c) :
    PointedCotangent.differential c (L.one (𝟙 _)) f hf hone = 0 ↔
      PointedCotangent.differential c a (z := mapPoint f hf a) f hf
        (rfl : a.1 ≫ f = (mapPoint f hf a).1) = 0 := by
  exact PointedCotangent.differential_eq_zero_iff_of_iso_square
    f hf hone f hf rfl
    (translateIso L a) (translate_over L a) (translate_zero L a)
    (translateIso M (mapPoint f hf a)) (translate_over M _)
    (translate_zero M _) (translate_natural L M f hf hmul a)

end SupersingularCurves.Geometry.GroupTranslation

namespace SupersingularCurves.Geometry.PerfectFieldVerschiebung
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open SchemeFrobenius

variable (p : ℕ) [Fact p.Prime]
variable {K : Type u} [Field K] [CharP K p] [PerfectField K]
variable {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of K)) [Smooth c]
variable (L : RelativeGroupLaw K c) (hc : L.IsCommutative)

/-- Vanishing of the genuine Verschiebung differential at the identity
propagates to every rational point of the actual Frobenius twist. -/
theorem differential_eq_zero_iff_at_point
    (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (toBase p c)) :
    PointedCotangent.differential (toBase p c) ((twistLaw p c L).one (𝟙 _))
        (verschiebung p c L hc) (verschiebung_over p c L hc)
        (verschiebung_zero p c L hc) = 0 ↔
      PointedCotangent.differential (toBase p c) a (z := verschiebungPoint p c L hc a)
        (verschiebung p c L hc) (verschiebung_over p c L hc)
        (rfl : a.1 ≫ verschiebung p c L hc = (verschiebungPoint p c L hc a).1) = 0 := by
  exact GroupTranslation.differential_eq_zero_iff_at_point
    (twistLaw p c L) L (verschiebung p c L hc) (verschiebung_over p c L hc)
    (fun t x y => verschiebung_mul p c L hc t x y)
    (verschiebung_zero p c L hc) a

end SupersingularCurves.Geometry.PerfectFieldVerschiebung

namespace SupersingularCurves.Geometry.Jacobian
open CategoryTheory AlgebraicGeometry AlgebraicCurve NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard

variable {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]
variable {M : CurveModel K F}
  {s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase}
variable (J : Jacobian M s)
variable (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectField K]

local instance smoothTranslationJacobian : Smooth J.designation.toBase :=
  SmoothOfRelativeDimension.smooth (genusFF K F) J.designation.toBase

/-- The existing actual-Jacobian cotangent condition is equivalent to
vanishing at any rational point of its genuine Frobenius twist. -/
theorem verschiebungCotangent_eq_zero_iff_at_point
    (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (J.twistToBase p)) :
    J.verschiebungCotangent p = 0 ↔
      PointedCotangent.differential (J.twistToBase p) a
        (z := GroupTranslation.mapPoint (J.verschiebung p) (J.verschiebung_over p) a)
        (J.verschiebung p) (J.verschiebung_over p) rfl = 0 := by
  rw [← J.groupScheme_verschiebungCotangent_eq_zero_iff p]
  exact PerfectFieldVerschiebung.differential_eq_zero_iff_at_point
    p J.designation.toBase J.groupLaw
    (J.represents.relativeGroupLaw_isCommutative (P := algEquivZeroGroupCut M.toBase s)) a

end SupersingularCurves.Geometry.Jacobian
