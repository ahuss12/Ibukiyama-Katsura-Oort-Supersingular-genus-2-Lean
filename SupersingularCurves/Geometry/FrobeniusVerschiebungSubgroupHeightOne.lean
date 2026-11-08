/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup

/-!
# Actual height-one equations for the simultaneous Frobenius--Verschiebung kernel

The actual closed immersion and its Frobenius annihilation imply that absolute
Frobenius of the subgroup factors through its identity and base Frobenius.
Consequently every element of its actual local augmentation ideal has p-th
power zero. The power equation is proved from the actual scheme construction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.PointedCotangent
open CategoryTheory AlgebraicGeometry NeronModelInfra SchemeFrobenius

variable {K : Type u} [Field K] {X : Scheme.{u}}
  (c : X ⟶ Spec (CommRingCat.of K))
  (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)

/-- Evaluation of a global section at the pointed augmentation is the
actual pullback along the rational section. -/
theorem augmentation_globalGerm (a : Γ(X, ⊤)) :
    augmentation c s (X.presheaf.germ ⊤ (s.1 (IsLocalRing.closedPoint K)) trivial a) =
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom (s.1.appTop a) := by
  have h : X.presheaf.germ ⊤ (s.1 (IsLocalRing.closedPoint K)) trivial ≫
      Scheme.stalkClosedPointTo s.1 =
      s.1.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom := by
    rw [Scheme.stalkClosedPointTo, Scheme.Hom.germ_stalkMap_assoc]
    change s.1.appTop ≫
        ((Spec (CommRingCat.of K)).presheaf.germ ⊤ (IsLocalRing.closedPoint K) trivial ≫
          (stalkClosedPointIso (CommRingCat.of K)).hom) = _
    rw [germ_stalkClosedPointIso_hom]
  exact congrArg (fun f => f a) h

variable (p : ℕ) [Fact p.Prime] [CharP K p] [Subsingleton X]

/-- On an actual one-point scheme, Frobenius factoring through the identity
forces every element of the actual augmentation ideal to have p-th power zero. -/
theorem pow_eq_zero_of_absolute_eq_constant
    (hF : absolute p c = c ≫ baseMap p K ≫ s.1)
    (b : Stalk c s) (hb : b ∈ IsLocalRing.maximalIdeal (Stalk c s)) : b ^ p = 0 := by
  obtain ⟨a, rfl⟩ := (FiniteGeometricPoints.globalGerm_bijective X
    (s.1 (IsLocalRing.closedPoint K))).surjective b
  have hb0 : augmentation c s
      (X.presheaf.germ ⊤ (s.1 (IsLocalRing.closedPoint K)) trivial a) = 0 :=
    RingHom.mem_ker.mp ((ker_augmentation c s).symm ▸ hb)
  rw [augmentation_globalGerm] at hb0
  have hs0 : s.1.appTop a = 0 := by
    apply (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom).injective
    simpa only [map_zero] using hb0
  have hp : a ^ p = 0 := by
    have he := congrArg (fun f : X ⟶ X => f.appTop a) hF
    change a ^ p ^ 1 = _ at he
    rw [pow_one] at he
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at he
    change a ^ p = c.appTop ((baseMap p K).appTop (s.1.appTop a)) at he
    simpa only [hs0, map_zero] using he
  rw [← map_pow, hp, map_zero]

end SupersingularCurves.Geometry.PointedCotangent

namespace SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian SchemeFrobenius

variable {K : Type u} [Field K] [IsAlgClosed K]
variable (p : ℕ) [Fact p.Prime] [CharP K p]
variable {g : ℕ} (A : AbelianVariety K g)

/-- Absolute Frobenius of the actual simultaneous kernel factors through
its actual identity section and Frobenius of the ground field. -/
theorem absolute_eq_identity_constant :
    absolute p (toBase p A) = toBase p A ≫ baseMap p K ≫ (identityPoint p A).1 := by
  have hnat : absolute p (toBase p A) ≫ inclusion p A =
      inclusion p A ≫ absolute p (base p A) :=
    Scheme.frobenius_comp (inclusion p A) p 1 (Fact.out : p.Prime)
      (globalChar p (toBase p A)) (globalChar p (base p A))
  have hF0 : twistZero p A ≫ F p A = twiceTwistZero p A :=
    congrArg Subtype.val (relative_one p (base p A) (law p A) (𝟙 _))
  have hzero : twiceTwistZero p A ≫ projection p (base p A) =
      baseMap p K ≫ twistZero p A := by
    rw [← hF0, Category.assoc]
    change twistZero p A ≫ relative p (base p A) ≫ projection p (base p A) = _
    rw [relative_projection, ← baseMap_eq_absolute p]
    exact (Scheme.frobenius_comp (twistZero p A) p 1 (Fact.out : p.Prime)
      (Scheme.natCast_eq_zero_ΓSpec (CharP.cast_eq_zero K p))
      (globalChar p (base p A))).symm
  apply (cancel_mono (inclusion p A)).mp
  rw [hnat, ← relative_projection p (base p A)]
  change inclusion p A ≫ F p A ≫ projection p (base p A) = _
  rw [← Category.assoc, inclusion_frobenius, Category.assoc, hzero]
  simp only [Category.assoc, identityPoint_inclusion]

/-- The height-one power equation holds in the actual stalk ring used
by the pointed cotangent construction, with its actual maximal ideal. -/
theorem maximalIdeal_pow_eq_zero
    (b : PointedCotangent.Stalk (toBase p A) (identityPoint p A))
    (hb : b ∈ IsLocalRing.maximalIdeal
      (PointedCotangent.Stalk (toBase p A) (identityPoint p A))) : b ^ p = 0 := by
  let := subsingleton p A
  exact PointedCotangent.pow_eq_zero_of_absolute_eq_constant
    (toBase p A) (identityPoint p A) p (absolute_eq_identity_constant p A) b hb

/-- The same height-one equation, stated directly with the canonical
augmentation whose kernel is the actual local maximal ideal. -/
theorem augmentationIdeal_pow_eq_zero
    (b : PointedCotangent.Stalk (toBase p A) (identityPoint p A))
    (hb : PointedCotangent.augmentation (toBase p A) (identityPoint p A) b = 0) :
    b ^ p = 0 := by
  apply maximalIdeal_pow_eq_zero p A b
  rw [← PointedCotangent.ker_augmentation]
  exact RingHom.mem_ker.mpr hb

end SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup
