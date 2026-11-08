/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.ScalarFrobeniusTateHopfSubgroup

/-! # Actual finite kernels as group schemes -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
universe u
namespace SupersingularCurves.Geometry.ScalarFrobeniusTate
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open GoodReductionJacobian FrobeniusFactorGroup
open scoped CategoryTheory.MonObj
variable {K : Type u} [Field K] {g h : ℕ}
  (A : AbelianVariety K g) (B : AbelianVariety K h) (f : A.group ⟶ B.group)

abbrev kernelBase := GroupHomFibre.toBase (GroupScheme.law B.group) (underlyingScheme.map f)
abbrev kernelInclusion := GroupHomFibre.inclusion (GroupScheme.law B.group) (underlyingScheme.map f)
abbrev kernelLaw := GroupHomFibre.law (GroupScheme.law A.group) (GroupScheme.law B.group)
  (underlyingScheme.map f) f.hom.hom.w (pointMap_mul f)

theorem kernelInclusion_mul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x y : SchemeHomOver t (kernelBase A B f)) :
    GroupHomFibre.inclusionPoint (GroupScheme.law B.group) (underlyingScheme.map f) f.hom.hom.w
      ((kernelLaw A B f).mul t x y) =
    (GroupScheme.law A.group).mul t
      (GroupHomFibre.inclusionPoint (GroupScheme.law B.group) (underlyingScheme.map f) f.hom.hom.w x)
      (GroupHomFibre.inclusionPoint (GroupScheme.law B.group) (underlyingScheme.map f) f.hom.hom.w y) := by
  apply Subtype.ext
  exact pullback.lift_fst _ _ _

theorem kernelInclusion_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) :
    GroupHomFibre.inclusionPoint (GroupScheme.law B.group) (underlyingScheme.map f) f.hom.hom.w
      ((kernelLaw A B f).one t) = (GroupScheme.law A.group).one t := by
  apply Subtype.ext
  exact pullback.lift_fst _ _ _

/-- The actual identity fibre with its actual induced group structure. -/
def kernelGroup : GroupScheme K where
  X := Over.mk (kernelBase A B f)
  grp := (kernelLaw A B f).grpObjOverMk

instance kernelGroup_comm : IsCommMonObj (kernelGroup A B f).X := by
  apply ((kernelLaw A B f).isCommMonObj_grpObjOverMk_iff_mul_comm).mpr
  intro T t x y
  apply GroupHomFibre.inclusionPoint_injective (GroupScheme.law B.group)
    (underlyingScheme.map f) f.hom.hom.w t
  rw [kernelInclusion_mul, kernelInclusion_mul]
  exact A.groupScheme_law_commutative t _ _

instance kernelInclusion_isMonHom :
    IsMonHom (Over.homMk (kernelInclusion A B f)
      (PointedCotangent.Fibre.inclusion_over A.group.X.hom _ f.hom.hom.w) :
        (kernelGroup A B f).X ⟶ A.group.X) := by
  apply GroupScheme.isMonHom_of_pointMap (G := kernelGroup A B f) (H := A.group)
    (kernelInclusion A B f) (PointedCotangent.Fibre.inclusion_over A.group.X.hom _ f.hom.hom.w)
  · intro T t
    simpa only [kernelInclusion, GroupScheme.law, kernelGroup, relativeGroupLawOfGrpObj_grpObjOverMk_one,
      pointMap, GroupHomFibre.inclusionPoint] using kernelInclusion_one A B f t
  · intro T t x y
    simpa only [kernelInclusion, GroupScheme.law, kernelGroup, relativeGroupLawOfGrpObj_grpObjOverMk_mul,
      pointMap, GroupHomFibre.inclusionPoint] using kernelInclusion_mul A B f t x y

/-- The actual kernel immersion as a group morphism. -/
def kernelInclusionHom : kernelGroup A B f ⟶ A.group :=
  Grp.homMk (Over.homMk (kernelInclusion A B f)
    (PointedCotangent.Fibre.inclusion_over A.group.X.hom _ f.hom.hom.w))

@[simp] theorem kernelInclusionHom_left :
    underlyingScheme.map (kernelInclusionHom A B f) = kernelInclusion A B f := rfl

instance kernelInclusionHom_closed :
    IsClosedImmersion (underlyingScheme.map (kernelInclusionHom A B f)) := by
  let : IsClosedImmersion (GroupScheme.zero B.group).1 :=
    isClosedImmersion_of_comp_eq_id B.group.X.hom (GroupScheme.zero B.group).1
      (GroupScheme.zero B.group).2
  change IsClosedImmersion (pullback.fst (underlyingScheme.map f) (GroupScheme.zero B.group).1)
  infer_instance

instance kernelGroup_finite [IsFinite (underlyingScheme.map f)] :
    IsFinite (kernelGroup A B f).X.hom := by
  change IsFinite (pullback.snd (underlyingScheme.map f) (GroupScheme.zero B.group).1)
  infer_instance

instance kernelGroup_flat : Flat (kernelGroup A B f).X.hom := by
  infer_instance

instance kernelGroup_lfp [IsFinite (underlyingScheme.map f)] :
    LocallyOfFinitePresentation (kernelGroup A B f).X.hom := by
  infer_instance

/-- The actual kernel inclusion satisfies the actual equation on every test scheme. -/
theorem kernelInclusionHom_kernel {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x : SchemeHomOver t (kernelGroup A B f).X.hom) :
    pointMap (underlyingScheme.map f) f.hom.hom.w
      (pointMap (underlyingScheme.map (kernelInclusionHom A B f))
        (kernelInclusionHom A B f).hom.hom.w x) = (GroupScheme.law B.group).one t :=
  GroupHomFibre.inclusionPoint_kernel _ _ _ x

/-- Finite actual kernels have genuine finite Hopf presentations. -/
theorem exists_kernel_hopf_presentation [IsFinite (underlyingScheme.map f)] :
    ∃ (C : Type u) (_ : CommRing C) (_ : HopfAlgebra K C),
      Module.Finite K C ∧ Nonempty (hopfGroup (K := K) C ≅ kernelGroup A B f) :=
  exists_finite_hopf_presentation (kernelGroup A B f)

end SupersingularCurves.Geometry.ScalarFrobeniusTate
