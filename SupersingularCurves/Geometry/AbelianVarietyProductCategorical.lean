/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.AbelianVarietyProductMaps

/-! # Comparing actual fibre products with categorical elliptic products -/
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
variable {K : Type u} [Field K] {g h : ℕ}
variable (A : AbelianVariety K g) (B : AbelianVariety K h)

private theorem pointMap_one {G : GroupScheme K} (f : G ⟶ A.group)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) :
    pointMap f.hom.hom.left f.hom.hom.w ((GroupScheme.law G).one t) =
      (GroupScheme.law A.group).one t := by
  exact congrArg overHomToSchemeHomOver (MonObj.one_comp (f.hom.hom) (X := Over.mk t))

private theorem pointMap_mul {G : GroupScheme K} (f : G ⟶ A.group)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x y : SchemeHomOver t G.X.hom) :
    pointMap f.hom.hom.left f.hom.hom.w ((GroupScheme.law G).mul t x y) =
      (GroupScheme.law A.group).mul t (pointMap f.hom.hom.left f.hom.hom.w x)
        (pointMap f.hom.hom.left f.hom.hom.w y) := by
  exact congrArg overHomToSchemeHomOver
    (MonObj.mul_comp (schemeHomOverToOverHom x) (schemeHomOverToOverHom y) f.hom.hom)

/-- The product pairing of genuine group-scheme morphisms. -/
def prodPairFromGroup {G : GroupScheme K} (f : G ⟶ A.group) (q : G ⟶ B.group) :
    G ⟶ (A.prod B).group := by
  let m := pullback.lift f.hom.hom.left q.hom.hom.left (f.hom.hom.w.trans q.hom.hom.w.symm)
  have hm : m ≫ (A.prod B).group.X.hom = G.X.hom := by
    dsimp [m, prod, prodStr]
    rw [pullback.lift_fst_assoc, f.hom.hom.w]
  letI : IsMonHom (Over.homMk m hm : G.X ⟶ (A.prod B).group.X) := by
    apply GroupScheme.isMonHom_of_pointMap (G := G) (H := (A.prod B).group) m hm
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
  exact Grp.homMk (Over.homMk m hm : G.X ⟶ (A.prod B).group.X)

@[simp] theorem prodPairFromGroup_fst {G : GroupScheme K}
    (f : G ⟶ A.group) (q : G ⟶ B.group) :
    A.prodPairFromGroup B f q ≫ A.prodFst B = f := by
  apply (Grp.forget _ ⋙ Over.forget _).map_injective
  exact pullback.lift_fst _ _ _

@[simp] theorem prodPairFromGroup_snd {G : GroupScheme K}
    (f : G ⟶ A.group) (q : G ⟶ B.group) :
    A.prodPairFromGroup B f q ≫ A.prodSnd B = q := by
  apply (Grp.forget _ ⋙ Over.forget _).map_injective
  exact pullback.lift_snd _ _ _

/-- Morphisms to the actual product are determined by their projections. -/
theorem prod_hom_ext {G : GroupScheme K} (f q : G ⟶ (A.prod B).group)
    (hf : f ≫ A.prodFst B = q ≫ A.prodFst B)
    (hq : f ≫ A.prodSnd B = q ≫ A.prodSnd B) : f = q := by
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact congrArg (fun z => z.hom.hom.left) hf
  · exact congrArg (fun z => z.hom.hom.left) hq

/-- The actual binary fibre product is the independent Fin-2 categorical
elliptic product used in the geometric supersingularity definition. -/
def prodFinTwoIso (E C : AbelianVariety K 1) :
    (E.prod C).group ≅ ellipticProduct ![E, C] where
  hom := Pi.lift (Fin.cases (E.prodFst C) (Fin.cases (E.prodSnd C) (fun i => Fin.elim0 i)))
  inv := E.prodPairFromGroup C (Pi.π (fun i => (![E, C] i).group) 0)
    (Pi.π (fun i => (![E, C] i).group) 1)
  hom_inv_id := by
    apply E.prod_hom_ext C
    · simp
    · simp
      rfl
  inv_hom_id := by
    apply Pi.hom_ext
    intro i
    fin_cases i
    · simp
    · simp only [Category.assoc, Pi.lift_π, Category.id_comp]
      exact E.prodPairFromGroup_snd C _ _

end SupersingularCurves.Geometry.AbelianVariety
