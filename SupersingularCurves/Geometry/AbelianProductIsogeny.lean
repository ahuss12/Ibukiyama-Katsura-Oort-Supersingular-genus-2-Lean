/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.AbelianIsogenyKilledKernel
import SupersingularCurves.Geometry.AbelianVarietyProductAddition

/-! # Finiteness of the actual complementary-product map

A quasi-retraction and its annihilated complement bound the entire kernel
of addition, on every test scheme. Together with geometric surjectivity,
this proves that the actual addition morphism is a finite flat isogeny.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
universe u
namespace SupersingularCurves.Geometry.AbelianVariety
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open FrobeniusFactorGroup ScalarFrobeniusTate
open scoped CategoryTheory.MonObj
variable {K : Type u} [Field K] {g h d : ℕ}

theorem comp_multiplication (A : AbelianVariety K g) (n : ℕ) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) (x : Over.mk t ⟶ A.group.X) :
    x ≫ (multiplication A n).hom.hom = x ^ n := by
  apply Over.OverMorphism.ext
  have H := congrArg Subtype.val (GroupScheme.nsmul_eq_pow A.group t n x)
  rw [SchemeFrobenius.nsmul_point] at H
  exact H

/-- A genuine quasi-retraction annihilates the entire product-addition kernel. -/
theorem prodCopair_kernel_killed_of_quasiRetraction
    (A : AbelianVariety K g) (B : AbelianVariety K h) (C : AbelianVariety K d)
    (j : A.group ⟶ C.group) (i : B.group ⟶ C.group) (r : C.group ⟶ A.group)
    [Mono (underlyingScheme.map i)] (n : ℕ)
    (hjr : j ≫ r = multiplication A n) (hir : i ≫ r = B.trivialHom A)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x : SchemeHomOver t (A.prod B).group.X.hom)
    (hx : pointMap (underlyingScheme.map (A.prodCopair B j i))
      (A.prodCopair B j i).hom.hom.w x = (GroupScheme.law C.group).one t) :
    (GroupScheme.law (A.prod B).group).nsmul t n x =
      (GroupScheme.law (A.prod B).group).one t := by
  let u : Over.mk t ⟶ (A.prod B).group.X := schemeHomOverToOverHom x
  let a : Over.mk t ⟶ A.group.X := u ≫ (A.prodFst B).hom.hom
  let b : Over.mk t ⟶ B.group.X := u ≫ (A.prodSnd B).hom.hom
  have hz : (a ≫ j.hom.hom) * (b ≫ i.hom.hom) = 1 := by
    have H := congrArg schemeHomOverToOverHom hx
    change u ≫ ((A.prodCopair B j i).hom.hom) = 1 at H
    change u ≫ ((A.prodFst B).hom.hom ≫ j.hom.hom *
      ((A.prodSnd B).hom.hom ≫ i.hom.hom)) = 1 at H
    simpa only [MonObj.comp_mul, ← Category.assoc] using H
  have hjr' : j.hom.hom ≫ r.hom.hom = (multiplication A n).hom.hom :=
    congrArg (fun q => q.hom.hom) hjr
  have hir' : i.hom.hom ≫ r.hom.hom = 1 :=
    congrArg (fun q => q.hom.hom) hir
  have ha : a ^ n = 1 := by
    have H := congrArg (fun q => q ≫ r.hom.hom) hz
    simpa only [MonObj.mul_comp, Category.assoc, hjr', hir',
      MonObj.comp_one, MonObj.one_comp, mul_one, comp_multiplication] using H
  have hb : b ^ n = 1 := by
    have H : (a ≫ j.hom.hom) ^ n * (b ≫ i.hom.hom) ^ n = 1 := by
      rw [← mul_pow, hz, one_pow]
    rw [← MonObj.pow_comp, ha, MonObj.one_comp, one_mul] at H
    apply Over.OverMorphism.ext
    apply (cancel_mono (underlyingScheme.map i)).mp
    exact congrArg Over.Hom.left (show (b ^ n) ≫ i.hom.hom = 1 ≫ i.hom.hom by
      rw [MonObj.pow_comp, H, MonObj.one_comp])
  have hu : u ^ n = 1 := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact congrArg Over.Hom.left
        (show (u ^ n) ≫ (A.prodFst B).hom.hom = 1 ≫ (A.prodFst B).hom.hom by
          rw [MonObj.pow_comp, ha, MonObj.one_comp])
    · exact congrArg Over.Hom.left
        (show (u ^ n) ≫ (A.prodSnd B).hom.hom = 1 ≫ (A.prodSnd B).hom.hom by
          rw [MonObj.pow_comp, hb, MonObj.one_comp])
  have H := GroupScheme.nsmul_eq_pow (A.prod B).group t n u
  rw [hu] at H
  exact H

/-- Actual complementary inclusions with a genuine quasi-retraction give
an actual finite flat product isogeny. -/
theorem prodCopair_isIsogeny_of_quasiRetraction [IsAlgClosed K]
    (A : AbelianVariety K g) (B : AbelianVariety K h) (C : AbelianVariety K d)
    (j : A.group ⟶ C.group) (i : B.group ⟶ C.group) (r : C.group ⟶ A.group)
    [Mono (underlyingScheme.map i)] (n : ℕ) (hn : n ≠ 0)
    (hjr : j ≫ r = multiplication A n) (hir : i ≫ r = B.trivialHom A)
    (hs : Surjective (underlyingScheme.map (A.prodCopair B j i))) :
    IsIsogeny (A.prodCopair B j i) ∧ Flat (underlyingScheme.map (A.prodCopair B j i)) :=
  (A.prod B).isIsogeny_of_surjective_of_kernel_killed C (A.prodCopair B j i) hs n hn
    (prodCopair_kernel_killed_of_quasiRetraction A B C j i r n hjr hir)

end SupersingularCurves.Geometry.AbelianVariety
