/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.AbelianMultiplicationDegree
import SupersingularCurves.Geometry.FrobeniusFactorGroup
import SupersingularCurves.Geometry.SmoothFiniteQuotientDimension
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_isProper_image_of_homomorphism_of_isProper
import Theorems.Thm_AlgebraicGeometry_isReduced_of_smooth_over_field
import Theorems.Thm_AlgebraicGeometry_GeometricallyReduced_of_isReduced_of_perfectField
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_smooth_of_geometricallyReduced_of_locallyOfFiniteType

/-! # The scheme-theoretic image of an actual abelian homomorphism

The image is constructed from the morphism, and its reducedness, group law,
connectedness and smoothness are proved. A finite morphism preserves the
source dimension on this image.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
universe u
namespace SupersingularCurves.Geometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open FrobeniusFactorGroup
open scoped CategoryTheory.MonObj

theorem isReduced_schemeImage {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [IsReduced X] : IsReduced f.image := by
  letI : IsSchemeTheoreticallyDominant f.toImage := by
    refine ⟨Scheme.IdealSheafData.ext_of_iSup_eq_top
      (fun (U : Y.affineOpens) => ⟨f.imageι ⁻¹ᵁ U.1, U.2.preimage f.imageι⟩) ?_ (fun U => ?_)⟩
    · rw [← top_le_iff]
      intro x _
      obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ :=
        Y.isBasis_affineOpens.exists_subset_of_mem_open
          (Set.mem_univ (f.imageι x)) isOpen_univ
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨U, hU⟩, hx⟩
    · simp only [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
      exact (RingHom.injective_iff_ker_eq_bot _).mp (f.toImage_app_injective U)
  exact IsSchemeTheoreticallyDominant.isReduced f.toImage

namespace AbelianVariety
variable {K : Type u} [Field K] [IsAlgClosed K] {g h : ℕ}

theorem hom_preserves_law (A : AbelianVariety K g) (B : AbelianVariety K h)
    (f : A.group ⟶ B.group) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x y : SchemeHomOver t A.group.X.hom) :
    pointMap (underlyingScheme.map f) f.hom.hom.w ((GroupScheme.law A.group).mul t x y) =
      (GroupScheme.law B.group).mul t
        (pointMap (underlyingScheme.map f) f.hom.hom.w x)
        (pointMap (underlyingScheme.map f) f.hom.hom.w y) := by
  exact Subtype.ext (congrArg Over.Hom.left
    (MonObj.mul_comp (schemeHomOverToOverHom x) (schemeHomOverToOverHom y) f.hom.hom))

/-- A finite actual abelian homomorphism constructs a closed subgroup of the
same dimension. The subgroup is its scheme-theoretic image. -/
theorem exists_closed_subgroup_of_finite_hom
    (A : AbelianVariety K g) (B : AbelianVariety K h)
    (f : A.group ⟶ B.group) [IsFinite (underlyingScheme.map f)] :
    ∃ (X : Scheme.{u}) (j : X ⟶ B.group.X.left)
      (L : RelativeGroupLaw K (j ≫ B.group.X.hom)),
      IsClosedImmersion j ∧ ConnectedSpace X ∧
      SmoothOfRelativeDimension g (j ≫ B.group.X.hom) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
        (x y : SchemeHomOver t (j ≫ B.group.X.hom)),
        pointMap j rfl (L.mul t x y) =
          (GroupScheme.law B.group).mul t (pointMap j rfl x) (pointMap j rfl y)) ∧
      Set.range j = Set.range (underlyingScheme.map f) := by
  let φ : A.group.X.left ⟶ B.group.X.left := f.hom.hom.left
  letI : IsFinite φ := by
    change IsFinite (underlyingScheme.map f)
    infer_instance
  have hover : φ ≫ B.group.X.hom = A.group.X.hom := f.hom.hom.w
  letI : IsReduced A.group.X.left := isReduced_of_smooth_over_field
    (SmoothOfRelativeDimension.smooth g A.group.X.hom)
  letI : IsReduced φ.image := isReduced_schemeImage φ
  obtain ⟨L, hproper, hmul, -⟩ :=
    RelativeGroupLaw.exists_relativeGroupLaw_isProper_image_of_homomorphism_of_isProper
      (GroupScheme.law B.group) (GroupScheme.law A.group) ⟨φ, hover⟩
      (A.hom_preserves_law B f)
  letI := hproper
  letI : GeometricallyReduced (φ.imageι ≫ B.group.X.hom) :=
    GeometricallyReduced.of_isReduced_of_perfectField _
  letI : Smooth (φ.imageι ≫ B.group.X.hom) :=
    L.smooth_of_geometricallyReduced_of_locallyOfFiniteType
  letI : ConnectedSpace A.group.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton A.group.X.hom
  letI : ConnectedSpace φ.image :=
    Function.Surjective.connectedSpace φ.toImage.surjective φ.toImage.continuous
  have hfac : φ.toImage ≫ (φ.imageι ≫ B.group.X.hom) = A.group.X.hom := by
    rw [← Category.assoc, Scheme.Hom.toImage_imageι, hover]
  letI : IsFinite (φ.toImage ≫ φ.imageι) := by
    simpa only [Scheme.Hom.toImage_imageι] using (inferInstance : IsFinite φ)
  letI : IsFinite φ.toImage := IsFinite.of_comp _ φ.imageι
  have hdim := FiniteQuotientGeometry.smoothOfRelativeDimension_of_finite_surjective
    A.group.X.hom (φ.imageι ≫ B.group.X.hom) φ.toImage hfac g L
  have hsurj : Function.Surjective (φ.toImage : A.group.X.left → φ.image) :=
    φ.toImage.surjective
  refine ⟨φ.image, φ.imageι, L, inferInstance, inferInstance, hdim, hmul, ?_⟩
  calc
    Set.range φ.imageι = Set.range (φ.toImage ≫ φ.imageι) := by
      ext y
      constructor
      · rintro ⟨z, rfl⟩
        obtain ⟨x, hx⟩ := hsurj z
        exact ⟨x, congrArg φ.imageι hx⟩
      · rintro ⟨x, rfl⟩
        exact ⟨φ.toImage x, rfl⟩
    _ = Set.range φ := by rw [φ.toImage_imageι]

end AbelianVariety
end SupersingularCurves.Geometry
