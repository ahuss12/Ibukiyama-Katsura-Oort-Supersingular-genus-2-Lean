/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FiniteGeometricPoints
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj

/-!
# An actual one-point group scheme as the spectrum of its identity stalk

The canonical map from the spectrum of the actual local ring is an isomorphism.
The actual group law transports across that map, and its identity is the
original rational-point augmentation. No finite-group classification is used.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.FiniteLocalGroupScheme
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open P2MW.S_AlgebraicGeometry_Scheme_exists_tangentPoints_equiv_linearMap_cotangentSpace

variable {K : Type u} [Field K] {X Y : Scheme.{u}}
  {c : X ⟶ Spec (CommRingCat.of K)} {d : Y ⟶ Spec (CommRingCat.of K)}

/-- Composition with an actual scheme isomorphism on all relative points. -/
def pointEquiv (j : Y ⟶ X) [IsIso j] (hj : j ≫ c = d)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) :
    SchemeHomOver t d ≃ SchemeHomOver t c where
  toFun x := ⟨x.1 ≫ j, by rw [Category.assoc, hj, x.2]⟩
  invFun x := ⟨x.1 ≫ inv j, by rw [← hj]; simpa only [Category.assoc, IsIso.inv_hom_id_assoc] using x.2⟩
  left_inv x := Subtype.ext (by simp)
  right_inv x := Subtype.ext (by simp)

theorem pointEquiv_comp (j : Y ⟶ X) [IsIso j] (hj : j ≫ c = d)
    {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (t' : T' ⟶ Spec (CommRingCat.of K)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (x : SchemeHomOver t d) :
    pointEquiv j hj t' (schemeHomOverComp ψ hψ x) =
      schemeHomOverComp ψ hψ (pointEquiv j hj t x) :=
  Subtype.ext (Category.assoc _ _ _)

/-- The original group law transported along an actual over-base isomorphism. -/
def transportLaw (G : RelativeGroupLaw K c) (j : Y ⟶ X) [IsIso j]
    (hj : j ≫ c = d) : RelativeGroupLaw K d where
  mul t x y := (pointEquiv j hj t).symm
    (G.mul t (pointEquiv j hj t x) (pointEquiv j hj t y))
  one t := (pointEquiv j hj t).symm (G.one t)
  inv t x := (pointEquiv j hj t).symm (G.inv t (pointEquiv j hj t x))
  mul_assoc t x y z := by simp only [Equiv.apply_symm_apply, G.mul_assoc]
  one_mul t x := by simp only [Equiv.apply_symm_apply, G.one_mul, Equiv.symm_apply_apply]
  mul_one t x := by simp only [Equiv.apply_symm_apply, G.mul_one, Equiv.symm_apply_apply]
  inv_mul_cancel t x := by simp only [Equiv.apply_symm_apply, G.inv_mul_cancel]
  mul_natural t t' ψ hψ x y := by
    apply (pointEquiv j hj t').injective
    rw [pointEquiv_comp, Equiv.apply_symm_apply, G.mul_natural]
    simp only [Equiv.apply_symm_apply, pointEquiv_comp]

variable (c) (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)

/-- A one-point affine scheme is the spectrum of its actual local stalk. -/
theorem fromSpecStalk_isIso [IsAffine X] [Subsingleton X] :
    IsIso (X.fromSpecStalk (s.1 (IsLocalRing.closedPoint K))) := by
  let := FiniteGeometricPoints.globalGerm_isIso X (s.1 (IsLocalRing.closedPoint K))
  have h : IsIso (X.fromSpecStalk (s.1 (IsLocalRing.closedPoint K)) ≫ X.toSpecΓ) := by
    rw [Scheme.fromSpecStalk_toSpecΓ]
    infer_instance
  exact (isIso_comp_right_iff _ X.toSpecΓ).mp h

/-- The canonical local-ring spectrum map has the natural K-algebra structure. -/
theorem fromSpecStalk_over :
    X.fromSpecStalk (s.1 (IsLocalRing.closedPoint K)) ≫ c =
      Spec.map (CommRingCat.ofHom (algebraMap K (PointedCotangent.Stalk c s))) := by
  have h := P2mTJ1.Λ₀_comp_eq_Spec_map (x := c) (pt := s.1)
    (fun _ => rfl) (𝟙 _) (algebraMap K (PointedCotangent.Stalk c s)) (fun _ => rfl)
  dsimp only [P2mTJ1.Λ₀] at h
  rw [Spec.map_id] at h
  erw [Category.id_comp] at h
  exact h

/-- Transport of the actual group law to the actual identity stalk spectrum. -/
def stalkLaw [IsAffine X] [Subsingleton X] (G : RelativeGroupLaw K c) :
    RelativeGroupLaw K
      (Spec.map (CommRingCat.ofHom (algebraMap K (PointedCotangent.Stalk c s)))) := by
  letI := fromSpecStalk_isIso c s
  exact transportLaw G (X.fromSpecStalk (s.1 (IsLocalRing.closedPoint K)))
    (fromSpecStalk_over c s)

/-- The transported identity is the original rational-point augmentation. -/
theorem stalkLaw_one [IsAffine X] [Subsingleton X] (G : RelativeGroupLaw K c)
    (hs : G.one (𝟙 _) = s) :
    ((stalkLaw c s G).one (𝟙 _)).1 =
      Spec.map (CommRingCat.ofHom (PointedCotangent.augmentation c s).toRingHom) := by
  let := fromSpecStalk_isIso c s
  apply (cancel_mono (X.fromSpecStalk (s.1 (IsLocalRing.closedPoint K)))).mp
  change ((G.one (𝟙 _)).1 ≫ inv (X.fromSpecStalk _)) ≫ X.fromSpecStalk _ = _
  rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id, hs]
  exact (Scheme.Spec_stalkClosedPointTo_fromSpecStalk s.1).symm

end SupersingularCurves.Geometry.FiniteLocalGroupScheme
