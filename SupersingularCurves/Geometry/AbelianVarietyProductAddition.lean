/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.AbelianVarietyProductMaps

/-! # Addition maps from genuine products of abelian varieties -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
universe u
namespace SupersingularCurves.Geometry.AbelianVariety
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open FrobeniusFactorGroup
open scoped CategoryTheory.MonObj
variable {K : Type u} [Field K] {g h d : ℕ}

/-- Sum of actual group homomorphisms into an actual commutative group scheme. -/
def sumHom {A : AbelianVariety K g} {B : AbelianVariety K h}
    (f q : A.group ⟶ B.group) : A.group ⟶ B.group := by
  let m : A.group.X ⟶ B.group.X := f.hom.hom * q.hom.hom
  letI : IsMonHom m := {
    one_hom := by
      change η[A.group.X] ≫ (f.hom.hom * q.hom.hom) = η[B.group.X]
      rw [MonObj.comp_mul, IsMonHom.one_hom, IsMonHom.one_hom, MonObj.one_eq_one]
      exact one_mul _
    mul_hom := by
      change μ[A.group.X] ≫ (f.hom.hom * q.hom.hom) =
        ((f.hom.hom * q.hom.hom) ⊗ₘ (f.hom.hom * q.hom.hom)) ≫ μ[B.group.X]
      simp only [MonObj.mul_eq_mul, MonObj.comp_mul, MonObj.mul_comp,
        tensorHom_fst, tensorHom_snd]
      ac_rfl }
  exact Grp.homMk m

theorem sumHom_points {A : AbelianVariety K g} {B : AbelianVariety K h}
    (f q : A.group ⟶ B.group) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t A.group.X.hom) :
    pointMap (underlyingScheme.map (sumHom f q)) (sumHom f q).hom.hom.w x =
      (GroupScheme.law B.group).mul t
        (pointMap (underlyingScheme.map f) f.hom.hom.w x)
        (pointMap (underlyingScheme.map q) q.hom.hom.w x) := by
  exact Subtype.ext (congrArg Over.Hom.left
    (MonObj.comp_mul (schemeHomOverToOverHom x) f.hom.hom q.hom.hom))

/-- The sum of two genuine maps from the two factors of an actual fibre product. -/
def prodCopair (A : AbelianVariety K g) (B : AbelianVariety K h)
    {C : AbelianVariety K d} (f : A.group ⟶ C.group) (q : B.group ⟶ C.group) :
    (A.prod B).group ⟶ C.group :=
  sumHom (A.prodFst B ≫ f) (A.prodSnd B ≫ q)

theorem prodCopair_left (A : AbelianVariety K g) (B : AbelianVariety K h)
    {C : AbelianVariety K d} (f : A.group ⟶ C.group) (q : B.group ⟶ C.group) :
    underlyingScheme.map (A.prodCopair B f q) =
      ((GroupScheme.law C.group).mul (A.prod B).group.X.hom
        ⟨pullback.fst A.group.X.hom B.group.X.hom ≫ underlyingScheme.map f,
          (A.prodFst B ≫ f).hom.hom.w⟩
        ⟨pullback.snd A.group.X.hom B.group.X.hom ≫ underlyingScheme.map q,
          (A.prodSnd B ≫ q).hom.hom.w⟩).1 := rfl

end SupersingularCurves.Geometry.AbelianVariety
