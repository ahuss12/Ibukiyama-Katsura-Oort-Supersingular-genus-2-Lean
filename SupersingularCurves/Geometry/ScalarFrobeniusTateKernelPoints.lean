/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.ScalarFrobeniusTateKernel
import SupersingularCurves.Geometry.ScalarFrobeniusTatePointSubgroup
import SupersingularCurves.Geometry.AbelianTateModule

/-! # Geometric points of the actual kernel -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
namespace SupersingularCurves.Geometry.ScalarFrobeniusTate
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open GoodReductionJacobian FrobeniusFactorGroup AbelianTate
open scoped CategoryTheory.MonObj
variable {K : Type} [Field K] {g h : ℕ}

/-- The two standard presentations of Spec K as a K-scheme agree. -/
def pointSourceIso : Over.mk (𝟙 (Spec (CommRingCat.of K))) ≅
    (Spec (CommRingCat.of K)).asOver (Spec (CommRingCat.of K)) :=
  Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ Spec.map (CommRingCat.ofHom (RingHom.id K)) = 𝟙 _
    rw [Category.id_comp]
    exact Spec.map_id _)

@[simp] theorem pointSourceIso_hom_left : (pointSourceIso (K := K)).hom.left = 𝟙 _ := rfl
@[simp] theorem pointSourceIso_inv_left : (pointSourceIso (K := K)).inv.left = 𝟙 _ := rfl

/-- Actual kernel points map to the actual point group of the abelian variety. -/
def kernelPointsMap (A : AbelianVariety K g) (B : AbelianVariety K h)
    (f : A.group ⟶ B.group) : FiniteGroupPoints (kernelGroup A B f) →+ A.AdditivePoints where
  toFun x := Additive.ofMul ((pointSourceIso (K := K)).hom ≫ x.toMul ≫
    (kernelInclusionHom A B f).hom.hom)
  map_zero' := by
    change (pointSourceIso (K := K)).hom ≫
      (1 : (Spec (CommRingCat.of K)).asOver (Spec (CommRingCat.of K)) ⟶
        (kernelGroup A B f).X) ≫ (kernelInclusionHom A B f).hom.hom = (1 : A.Points)
    rw [MonObj.one_comp, MonObj.comp_one]
  map_add' x y := by
    change _ ≫ (x.toMul * y.toMul) ≫ _ = _
    rw [MonObj.mul_comp, MonObj.comp_mul]
    rfl

@[simp] theorem kernelPointsMap_left (A : AbelianVariety K g) (B : AbelianVariety K h)
    (f : A.group ⟶ B.group) (x : FiniteGroupPoints (kernelGroup A B f)) :
    (kernelPointsMap A B f x).toMul.left = x.toMul.left ≫ kernelInclusion A B f := by
  change (pointSourceIso (K := K)).hom.left ≫
    (x.toMul.left ≫ underlyingScheme.map (kernelInclusionHom A B f)) = _
  rw [pointSourceIso_hom_left, kernelInclusionHom_left, Category.id_comp]

theorem kernelPointsMap_injective (A : AbelianVariety K g) (B : AbelianVariety K h)
    (f : A.group ⟶ B.group) : Function.Injective (kernelPointsMap A B f) := by
  intro x y hxy
  have h := congrArg (fun P : A.AdditivePoints => P.toMul.left) hxy
  rw [kernelPointsMap_left, kernelPointsMap_left] at h
  apply congrArg Additive.ofMul
  apply Over.OverMorphism.ext
  exact (cancel_mono (kernelInclusion A B f)).mp h

/-- The image is exactly the kernel of the genuine map on geometric points. -/
theorem mem_range_kernelPointsMap (A : AbelianVariety K g) (B : AbelianVariety K h)
    (f : A.group ⟶ B.group) (x : A.AdditivePoints) :
    x ∈ (kernelPointsMap A B f).range ↔ pointsMap f x = 0 := by
  constructor
  · rintro ⟨y, rfl⟩
    let z : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (kernelGroup A B f).X.hom :=
      overHomToSchemeHomOver ((pointSourceIso (K := K)).hom ≫ y.toMul)
    apply congrArg Additive.ofMul
    apply Over.OverMorphism.ext
    exact congrArg Subtype.val (kernelInclusionHom_kernel A B f (𝟙 _) z)
  · intro hx
    let z := overHomToSchemeHomOver x.toMul
    have hz : pointMap (underlyingScheme.map f) f.hom.hom.w z =
        (GroupScheme.law B.group).one (𝟙 _) := by
      apply Subtype.ext
      exact congrArg (fun P : B.AdditivePoints => P.toMul.left) hx
    let y := GroupHomFibre.liftPoint (GroupScheme.law B.group) (underlyingScheme.map f)
      f.hom.hom.w z hz
    let y' : FiniteGroupPoints (kernelGroup A B f) :=
      Additive.ofMul ((pointSourceIso (K := K)).inv ≫ schemeHomOverToOverHom y)
    refine ⟨y', ?_⟩
    apply congrArg Additive.ofMul
    apply Over.OverMorphism.ext
    change (𝟙 _ ≫ ((𝟙 _ ≫ y.1) ≫ kernelInclusion A B f)) = _
    rw [Category.id_comp, Category.id_comp]
    exact congrArg Subtype.val (GroupHomFibre.inclusionPoint_liftPoint _ _ _ z hz)

end SupersingularCurves.Geometry.ScalarFrobeniusTate
