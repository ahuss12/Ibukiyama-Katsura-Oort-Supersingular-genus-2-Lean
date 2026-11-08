/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.AbelianVarietyProduct
import SupersingularCurves.Geometry.AbelianTateModule

/-! # Group morphisms and actual points of binary products -/
set_option autoImplicit false
set_option maxHeartbeats 150000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SupersingularCurves.Geometry.AbelianVariety
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open FrobeniusFactorGroup
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
variable {K : Type u} [Field K] {g h j : ℕ}
variable (A : AbelianVariety K g) (B : AbelianVariety K h)

private theorem pointMap_one {C : AbelianVariety K j} (f : C.group ⟶ A.group)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) :
    pointMap f.hom.hom.left f.hom.hom.w ((GroupScheme.law C.group).one t) =
      (GroupScheme.law A.group).one t := by
  exact congrArg overHomToSchemeHomOver (MonObj.one_comp (f.hom.hom) (X := Over.mk t))

private theorem pointMap_mul {C : AbelianVariety K j} (f : C.group ⟶ A.group)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x y : SchemeHomOver t C.group.X.hom) :
    pointMap f.hom.hom.left f.hom.hom.w ((GroupScheme.law C.group).mul t x y) =
      (GroupScheme.law A.group).mul t (pointMap f.hom.hom.left f.hom.hom.w x)
        (pointMap f.hom.hom.left f.hom.hom.w y) := by
  exact congrArg overHomToSchemeHomOver
    (MonObj.mul_comp (schemeHomOverToOverHom x) (schemeHomOverToOverHom y) f.hom.hom)

/-- The product pairing of genuine group-scheme morphisms. -/
def prodPair {C : AbelianVariety K j} (f : C.group ⟶ A.group) (q : C.group ⟶ B.group) :
    C.group ⟶ (A.prod B).group := by
  let m := pullback.lift f.hom.hom.left q.hom.hom.left (f.hom.hom.w.trans q.hom.hom.w.symm)
  have hm : m ≫ (A.prod B).group.X.hom = C.group.X.hom := by
    dsimp [m, prod, prodStr]
    rw [pullback.lift_fst_assoc, f.hom.hom.w]
  letI : IsMonHom (Over.homMk m hm : C.group.X ⟶ (A.prod B).group.X) := by
    apply GroupScheme.isMonHom_of_pointMap (G := C.group) (H := (A.prod B).group) m hm
    · intro T t
      apply Subtype.ext
      apply pullback.hom_ext
      · simp only [prod_law_one, RelativeGroupLaw.prod_one, prodPairPt_coe, pointMap, m,
          Category.assoc, pullback.lift_fst]
        exact congrArg (fun z => z.1) (pointMap_one A f t)
      · simp only [prod_law_one, RelativeGroupLaw.prod_one, prodPairPt_coe, pointMap, m,
          Category.assoc, pullback.lift_snd]
        exact congrArg (fun z => z.1) (pointMap_one B q t)
    · intro T t x y
      apply Subtype.ext
      apply pullback.hom_ext
      · simp only [prod_law_mul, RelativeGroupLaw.prod_mul, prodPairPt_coe, pointMap, m,
          prodFstPt, Category.assoc, pullback.lift_fst]
        exact congrArg (fun z => z.1) (pointMap_mul A f t x y)
      · simp only [prod_law_mul, RelativeGroupLaw.prod_mul, prodPairPt_coe, pointMap, m,
          prodSndPt, Category.assoc, pullback.lift_snd]
        exact congrArg (fun z => z.1) (pointMap_mul B q t x y)
  exact Grp.homMk (Over.homMk m hm : C.group.X ⟶ (A.prod B).group.X)

@[simp] theorem prodPair_fst {C : AbelianVariety K j}
    (f : C.group ⟶ A.group) (q : C.group ⟶ B.group) :
    A.prodPair B f q ≫ A.prodFst B = f := by
  apply (Grp.forget _ ⋙ Over.forget _).map_injective
  exact pullback.lift_fst _ _ _

@[simp] theorem prodPair_snd {C : AbelianVariety K j}
    (f : C.group ⟶ A.group) (q : C.group ⟶ B.group) :
    A.prodPair B f q ≫ A.prodSnd B = q := by
  apply (Grp.forget _ ⋙ Over.forget _).map_injective
  exact pullback.lift_snd _ _ _

/-- The constant identity map, as an actual group morphism. -/
def trivialHom : A.group ⟶ B.group := by
  letI : IsMonHom (1 : A.group.X ⟶ B.group.X) := by
    constructor
    · rw [MonObj.one_eq_one, MonObj.comp_one, MonObj.one_eq_one]
    · rw [MonObj.comp_one, MonObj.mul_eq_mul, MonObj.comp_mul,
        tensorHom_fst, tensorHom_snd, MonObj.comp_one, MonObj.comp_one, one_mul]
  exact Grp.homMk (1 : A.group.X ⟶ B.group.X)

/-- First factor inclusion. -/
def prodInl : A.group ⟶ (A.prod B).group := A.prodPair B (𝟙 A.group) (A.trivialHom B)

/-- Second factor inclusion. -/
def prodInr : B.group ⟶ (A.prod B).group := A.prodPair B (B.trivialHom A) (𝟙 B.group)

@[simp] theorem prodInl_fst : A.prodInl B ≫ A.prodFst B = 𝟙 A.group := A.prodPair_fst B _ _
@[simp] theorem prodInl_snd : A.prodInl B ≫ A.prodSnd B = A.trivialHom B := A.prodPair_snd B _ _
@[simp] theorem prodInr_fst : A.prodInr B ≫ A.prodFst B = B.trivialHom A := A.prodPair_fst B _ _
@[simp] theorem prodInr_snd : A.prodInr B ≫ A.prodSnd B = 𝟙 B.group := A.prodPair_snd B _ _

/-- The actual points of the fibre product are the product of actual point groups. -/
def pointsProdEquiv : (A.prod B).Points ≃* A.Points × B.Points where
  toFun x := (x ≫ (A.prodFst B).hom.hom, x ≫ (A.prodSnd B).hom.hom)
  invFun x := Over.homMk (pullback.lift x.1.left x.2.left (x.1.w.trans x.2.w.symm)) (by
    change pullback.lift _ _ _ ≫ (pullback.fst _ _ ≫ _) = _
    rw [pullback.lift_fst_assoc, x.1.w])
  left_inv x := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext <;> simp [prodFst, prodSnd]
  right_inv x := by
    apply Prod.ext <;> apply Over.OverMorphism.ext <;> simp [prodFst, prodSnd]
  map_mul' x y := Prod.ext (MonObj.mul_comp _ _ _) (MonObj.mul_comp _ _ _)

/-- Additive notation for the genuine product-points equivalence. -/
def additivePointsProdEquiv : (A.prod B).AdditivePoints ≃+ A.AdditivePoints × B.AdditivePoints where
  toFun x := (Additive.ofMul ((A.pointsProdEquiv B) x.toMul).1,
    Additive.ofMul ((A.pointsProdEquiv B) x.toMul).2)
  invFun x := Additive.ofMul ((A.pointsProdEquiv B).symm (x.1.toMul, x.2.toMul))
  left_inv x := congrArg Additive.ofMul ((A.pointsProdEquiv B).symm_apply_apply x.toMul)
  right_inv x := by
    have h := (A.pointsProdEquiv B).apply_symm_apply (x.1.toMul, x.2.toMul)
    exact congrArg (fun z => (Additive.ofMul z.1, Additive.ofMul z.2)) h
  map_add' x y := by
    have h := (A.pointsProdEquiv B).map_mul x.toMul y.toMul
    exact congrArg (fun z => (Additive.ofMul z.1, Additive.ofMul z.2)) h

end SupersingularCurves.Geometry.AbelianVariety
