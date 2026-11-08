/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.PointedCotangentGroupAdd
import SupersingularCurves.Geometry.PointedCotangentDimension
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

/-! # Scalar differentiation of actual ring actions on one-dimensional groups -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
namespace SupersingularCurves.Geometry.PointedCotangent
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

variable {K : Type u} [Field K] {X Y : Scheme.{u}}
variable {c : X ⟶ Spec (CommRingCat.of K)} {d : Y ⟶ Spec (CommRingCat.of K)}

theorem differential_congr (s : SchemeHomOver (𝟙 _) c) (t : SchemeHomOver (𝟙 _) d)
    (f g : X ⟶ Y) (hf : f ≫ d = c) (hg : g ≫ d = c)
    (hsf : s.1 ≫ f = t.1) (hsg : s.1 ≫ g = t.1) (h : f = g) :
    differential c s f hf hsf = differential c s g hg hsg := by
  subst g
  rfl

variable (L : RelativeGroupLaw K c)

/-- Multiplication preservation gives actual preservation of the group identity. -/
theorem end_point_of_mul (f : SchemeHomOver c c)
    (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
      (x y : SchemeHomOver t c),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) f =
        L.mul t (NeronModelInfra.schemeHomOverComp x f)
          (NeronModelInfra.schemeHomOverComp y f)) :
    (L.one (𝟙 _)).1 ≫ f.1 = (L.one (𝟙 _)).1 := by
  letI := L.pointGroup (𝟙 (Spec (CommRingCat.of K)))
  have H := hmul (𝟙 _) (L.one (𝟙 _)) (L.one (𝟙 _))
  rw [L.one_mul] at H
  have HH : NeronModelInfra.schemeHomOverComp (L.one (𝟙 _)) f *
      NeronModelInfra.schemeHomOverComp (L.one (𝟙 _)) f =
      NeronModelInfra.schemeHomOverComp (L.one (𝟙 _)) f := H.symm
  exact congrArg Subtype.val (mul_eq_left.mp HH)

variable {R : Type v} [Semiring R]
variable (Φ : R → SchemeHomOver c c)
  (hpoint : ∀ a, (L.one (𝟙 _)).1 ≫ (Φ a).1 = (L.one (𝟙 _)).1)

/-- Differentiate each actual endomorphism in the action at its actual identity. -/
def actionDifferential (a : R) : Module.End K (Cotangent c (L.one (𝟙 _))) :=
  differential c (L.one (𝟙 _)) (Φ a).1 (Φ a).2 (hpoint a)

theorem actionDifferential_zero (hzero : Φ 0 = L.one c) :
    actionDifferential L Φ hpoint 0 = 0 := by
  exact (differential_congr (L.one (𝟙 _)) (L.one (𝟙 _)) _ _ _ _ _
    (law_one_point L (L.one (𝟙 _))) (congrArg Subtype.val hzero)).trans
      (differential_law_one L (L.one (𝟙 _)))

theorem actionDifferential_one (hone : Φ 1 = NeronModelInfra.schemeHomOverId c) :
    actionDifferential L Φ hpoint 1 = LinearMap.id := by
  exact (differential_congr (L.one (𝟙 _)) (L.one (𝟙 _)) _ _ _ _ _
    (Category.comp_id _) (congrArg Subtype.val hone)).trans
      (differential_id c (L.one (𝟙 _)))

theorem actionDifferential_add (hadd : ∀ a b, Φ (a + b) = L.mul c (Φ a) (Φ b))
    (a b : R) :
    actionDifferential L Φ hpoint (a + b) =
      actionDifferential L Φ hpoint a + actionDifferential L Φ hpoint b := by
  exact (differential_congr (L.one (𝟙 _)) (L.one (𝟙 _)) _ _ _ _ _
    (law_mul_point L (L.one (𝟙 _)) (Φ a) (Φ b) (hpoint a) (hpoint b))
    (congrArg Subtype.val (hadd a b))).trans
      (differential_law_mul L (L.one (𝟙 _)) (Φ a) (Φ b) (hpoint a) (hpoint b))

theorem actionDifferential_mul
    (hmul : ∀ a b, Φ (a * b) = NeronModelInfra.schemeHomOverComp (Φ b) (Φ a))
    (a b : R) :
    actionDifferential L Φ hpoint (a * b) =
      (actionDifferential L Φ hpoint b).comp (actionDifferential L Φ hpoint a) := by
  have hbase : ((Φ b).1 ≫ (Φ a).1) ≫ c = c := by
    rw [Category.assoc, (Φ a).2, (Φ b).2]
  have hzero : (L.one (𝟙 _)).1 ≫ ((Φ b).1 ≫ (Φ a).1) = (L.one (𝟙 _)).1 := by
    rw [← Category.assoc, hpoint b, hpoint a]
  exact (differential_congr (L.one (𝟙 _)) (L.one (𝟙 _)) _ _ _ hbase _ hzero
    (congrArg Subtype.val (hmul a b))).trans
      (differential_comp c (L.one (𝟙 _)) (Φ b).1 (Φ b).2 (hpoint b)
        (Φ a).1 (Φ a).2 (hpoint a))

variable (hdim : Module.finrank K (Cotangent c (L.one (𝟙 _))) = 1)

/-- The scalar determined by the actual local cotangent endomorphism. -/
def actionCotangentScalar (a : R) : K :=
  (LinearEquiv.smul_id_of_finrank_eq_one hdim).symm (actionDifferential L Φ hpoint a)

theorem actionDifferential_eq_scalar (a : R) :
    actionDifferential L Φ hpoint a = actionCotangentScalar L Φ hpoint hdim a • LinearMap.id := by
  exact ((LinearEquiv.smul_id_of_finrank_eq_one hdim).apply_symm_apply _).symm

/-- The derivative scalars of an actual ring action form a genuine ring homomorphism.
The contravariant order of composition disappears in the one-dimensional scalar field. -/
def cotangentScalarRingHom
    (hzero : Φ 0 = L.one c) (hone : Φ 1 = NeronModelInfra.schemeHomOverId c)
    (hadd : ∀ a b, Φ (a + b) = L.mul c (Φ a) (Φ b))
    (hmul : ∀ a b, Φ (a * b) = NeronModelInfra.schemeHomOverComp (Φ b) (Φ a)) : R →+* K where
  toFun := actionCotangentScalar L Φ hpoint hdim
  map_zero' := by
    unfold actionCotangentScalar
    rw [actionDifferential_zero L Φ hpoint hzero, map_zero]
  map_one' := by
    apply (LinearEquiv.smul_id_of_finrank_eq_one hdim).injective
    change actionCotangentScalar L Φ hpoint hdim 1 • LinearMap.id =
      (1 : K) • (LinearMap.id : Module.End K (Cotangent c (L.one (𝟙 _))))
    rw [← actionDifferential_eq_scalar L Φ hpoint hdim 1, one_smul,
      actionDifferential_one L Φ hpoint hone]
  map_add' a b := by
    unfold actionCotangentScalar
    rw [actionDifferential_add L Φ hpoint hadd, map_add]
  map_mul' a b := by
    apply (LinearEquiv.smul_id_of_finrank_eq_one hdim).injective
    change actionCotangentScalar L Φ hpoint hdim (a * b) •
      (LinearMap.id : Module.End K (Cotangent c (L.one (𝟙 _)))) =
      (actionCotangentScalar L Φ hpoint hdim a *
      actionCotangentScalar L Φ hpoint hdim b) • LinearMap.id
    rw [← actionDifferential_eq_scalar L Φ hpoint hdim (a * b),
      actionDifferential_mul L Φ hpoint hmul,
      actionDifferential_eq_scalar L Φ hpoint hdim b,
      actionDifferential_eq_scalar L Φ hpoint hdim a]
    ext x
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply, smul_smul]
    rw [mul_comm]

theorem cotangentScalarRingHom_action
    (hzero : Φ 0 = L.one c) (hone : Φ 1 = NeronModelInfra.schemeHomOverId c)
    (hadd : ∀ a b, Φ (a + b) = L.mul c (Φ a) (Φ b))
    (hmul : ∀ a b, Φ (a * b) = NeronModelInfra.schemeHomOverComp (Φ b) (Φ a)) (a : R) :
    actionDifferential L Φ hpoint a =
      cotangentScalarRingHom L Φ hpoint hdim hzero hone hadd hmul a • LinearMap.id :=
  actionDifferential_eq_scalar L Φ hpoint hdim a

end SupersingularCurves.Geometry.PointedCotangent
