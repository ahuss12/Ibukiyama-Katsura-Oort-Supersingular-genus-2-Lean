/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FiniteGeometricPoints

/-!
# A finite geometric point with zero cotangent space

The actual local cotangent criterion makes the local ring a field by
Nakayama. The rational-point augmentation then identifies that field with
the base field. The finite one-point scheme application will use the
actual global-section germ, not a substitute coordinate model.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.PointedCotangent
open CategoryTheory AlgebraicGeometry NeronModelInfra

variable {K : Type u} [Field K] {X : Scheme.{u}}
variable (c : X ⟶ Spec (CommRingCat.of K))
  (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)

/-- If the actual Noetherian local cotangent space is zero, the rational
point's actual augmentation is an isomorphism on rings. -/
theorem augmentation_bijective_of_cotangent_subsingleton
    [IsNoetherianRing (Stalk c s)] (h : Subsingleton (Cotangent c s)) :
    Function.Bijective (augmentation c s) := by
  have hfield : IsField (Stalk c s) :=
    IsLocalRing.subsingleton_cotangentSpace_iff.mp h
  let : Field (Stalk c s) := hfield.toField
  refine ⟨(augmentation c s).injective, ?_⟩
  intro x
  exact ⟨algebraMap K (Stalk c s) x, (augmentation c s).commutes x⟩

/-- The base-field map to the actual stalk is bijective under the same
cotangent hypothesis, since it is inverse to the augmentation. -/
theorem algebraMap_stalk_bijective_of_cotangent_subsingleton
    [IsNoetherianRing (Stalk c s)] (h : Subsingleton (Cotangent c s)) :
    Function.Bijective (algebraMap K (Stalk c s)) := by
  have hi := (augmentation_bijective_of_cotangent_subsingleton c s h).1
  refine ⟨(algebraMap K (Stalk c s)).injective, ?_⟩
  intro x
  refine ⟨augmentation c s x, hi ?_⟩
  exact (augmentation c s).commutes _

/-- A finite scheme over an algebraically closed field with a unique
rational point and zero actual local cotangent space is that reduced
rational point. The conclusion is an actual scheme isomorphism. -/
theorem isIso_of_unique_point_of_cotangent_subsingleton
    [IsAlgClosed K] [IsFinite c]
    (huniq : ∀ q : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c, q = s)
    (hcot : Subsingleton (Cotangent c s)) : IsIso c := by
  let := FiniteGeometricPoints.subsingleton_of_unique_point c s huniq
  let := FiniteGeometricPoints.finite_stalk c s
  let : IsNoetherianRing (Stalk c s) := IsNoetherianRing.of_finite K (Stalk c s)
  let z := s.1 (IsLocalRing.closedPoint K)
  let γ := (X.presheaf.germ ⊤ z trivial).hom
  let α := c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  have hg : Function.Bijective γ := FiniteGeometricPoints.globalGerm_bijective X z
  have ha := algebraMap_stalk_bijective_of_cotangent_subsingleton c s hcot
  have halpha : Function.Bijective α := by
    constructor
    · intro a b hab
      exact ha.1 (congrArg γ hab)
    · intro a
      obtain ⟨k, hk⟩ := ha.2 (γ a)
      exact ⟨k, hg.1 hk⟩
  have he : Function.Bijective (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.bijective
  have hcapp : Function.Bijective c.appTop.hom := by
    constructor
    · intro a b hab
      obtain ⟨a', rfl⟩ := he.2 a
      obtain ⟨b', rfl⟩ := he.2 b
      exact congrArg (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (halpha.1 hab)
    · intro a
      obtain ⟨k, hk⟩ := halpha.2 a
      exact ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom k, hk⟩
  let : IsIso c.appTop := (ConcreteCategory.isIso_iff_bijective _).mpr hcapp
  exact (HasAffineProperty.iff_of_isAffine
    (P := CategoryTheory.MorphismProperty.isomorphisms Scheme)).mpr
    ⟨inferInstance, inferInstance⟩

end SupersingularCurves.Geometry.PointedCotangent
