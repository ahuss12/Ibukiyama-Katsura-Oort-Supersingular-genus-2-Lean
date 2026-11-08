/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.ProperCurveFiniteMap
import SupersingularCurves.Geometry.AbelianHomImage
import SupersingularCurves.Geometry.AbelianTateModule
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_surjective_mul_of_isProper_of_isCommutative
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_isIntegral_of_field
import Theorems.Thm_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed

/-! # Constructing an elliptic subgroup from a nonzero actual elliptic map

The input is a genuine group-scheme morphism whose induced rational Tate map
is nonzero. The closed subgroup, its smoothness, and its elliptic dimension
are conclusions. Existence of the initial morphism is a separate global goal.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
universe u
namespace SupersingularCurves.Geometry
open CategoryTheory AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open FrobeniusFactorGroup
open scoped CategoryTheory.MonObj
open P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_surjective_mul_of_isProper_of_isCommutative.GoodReductionJacobian.RelativeGroupLaw.RosenlichtDecomp

namespace AbelianTate
variable {K : Type} [Field K] [IsAlgClosed K] {g h : ℕ}

theorem not_constant_of_rationalMap_ne_zero
    (ℓ : ℕ) [Fact ℓ.Prime] {A : AbelianVariety K g} {B : AbelianVariety K h}
    (f : A.group ⟶ B.group) (hf : rationalMap ℓ f ≠ 0) :
    ¬ ∃ y : B.group.X.left, ∀ x : A.group.X.left, (underlyingScheme.map f) x = y := by
  rintro ⟨y, hy⟩
  have hpts : pointsMap f = 0 := by
    apply AddMonoidHom.ext
    intro x
    change Additive.ofMul (x.toMul ≫ f.hom.hom) = Additive.ofMul (1 : B.Points)
    apply congrArg Additive.ofMul
    apply overHomToSchemeHomOver_injective
    apply eq_of_pt_eq
    have hh : pt (overHomToSchemeHomOver (x.toMul ≫ f.hom.hom)) =
        pt (overHomToSchemeHomOver ((1 : A.Points) ≫ f.hom.hom)) :=
      (hy _).trans (hy _).symm
    simpa only [MonObj.one_comp] using hh
  have hint : integralMap ℓ f = 0 := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    funext n
    change pointsMap f (x.1 n) = 0
    rw [hpts]
    rfl
  apply hf
  simp only [rationalMap, hint, LinearMap.baseChange_zero]

end AbelianTate

namespace AbelianVariety
variable {K : Type} [Field K] [IsAlgClosed K] {g : ℕ}

/-- A nonzero Tate map from an actual elliptic curve is finite as a scheme map. -/
theorem isFinite_of_elliptic_rationalMap_ne_zero
    (ℓ : ℕ) [Fact ℓ.Prime] (E : AbelianVariety K 1) (A : AbelianVariety K g)
    (f : E.group ⟶ A.group) (hf : AbelianTate.rationalMap ℓ f ≠ 0) :
    IsFinite (underlyingScheme.map f) := by
  letI : IsIntegral E.group.X.left :=
    AbelianSchemePropertyBundle.isIntegral_of_field E.abelianSchemePropertyBundle
  letI : GeometricallyIntegral E.group.X.hom :=
    geometricallyIntegral_of_isAlgClosed E.group.X.hom
  exact isFinite_of_proper_curve_of_not_constant E.group.X.hom A.group.X.hom
    (underlyingScheme.map f) f.hom.hom.w
    (AbelianTate.not_constant_of_rationalMap_ne_zero ℓ f hf)

/-- The actual elliptic subgroup is constructed as the image of `f`. -/
theorem exists_closed_elliptic_subgroup_of_rationalMap_ne_zero
    (ℓ : ℕ) [Fact ℓ.Prime] (E : AbelianVariety K 1) (A : AbelianVariety K g)
    (f : E.group ⟶ A.group) (hf : AbelianTate.rationalMap ℓ f ≠ 0) :
    ∃ (X : Scheme) (j : X ⟶ A.group.X.left)
      (L : RelativeGroupLaw K (j ≫ A.group.X.hom)),
      IsClosedImmersion j ∧ ConnectedSpace X ∧
      SmoothOfRelativeDimension 1 (j ≫ A.group.X.hom) ∧
      (∀ {T : Scheme} (t : T ⟶ Spec (CommRingCat.of K))
        (x y : SchemeHomOver t (j ≫ A.group.X.hom)),
        pointMap j rfl (L.mul t x y) =
          (GroupScheme.law A.group).mul t (pointMap j rfl x) (pointMap j rfl y)) ∧
      Set.range j = Set.range (underlyingScheme.map f) := by
  letI := E.isFinite_of_elliptic_rationalMap_ne_zero ℓ A f hf
  exact E.exists_closed_subgroup_of_finite_hom A f


end AbelianVariety
end SupersingularCurves.Geometry
