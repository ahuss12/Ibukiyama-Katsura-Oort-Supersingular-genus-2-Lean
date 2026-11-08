/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusFiniteFieldDescentGroupIso
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawProd

/-! # Actual binary products of abelian varieties -/
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SupersingularCurves.Geometry.AbelianVariety
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open FrobeniusFactorGroup
variable {K : Type u} [Field K] {g h : ℕ}
variable (A : AbelianVariety K g) (B : AbelianVariety K h)

/-- The actual fibre product, with its product group law and sum of relative dimensions. -/
def prod : AbelianVariety K (g + h) := by
  let L := (GroupScheme.law A.group).prod (GroupScheme.law B.group)
  let G : GroupScheme K :=
    { X := Over.mk (prodStr A.group.X.hom B.group.X.hom), grp := L.grpObjOverMk }
  have hfst : SmoothOfRelativeDimension h (pullback.fst A.group.X.hom B.group.X.hom) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange h).of_isPullback
      (IsPullback.of_hasPullback A.group.X.hom B.group.X.hom).flip B.smooth
  letI : SmoothOfRelativeDimension h (pullback.fst A.group.X.hom B.group.X.hom) := hfst
  letI : Smooth A.group.X.hom := SmoothOfRelativeDimension.smooth g A.group.X.hom
  letI : Smooth B.group.X.hom := SmoothOfRelativeDimension.smooth h B.group.X.hom
  exact
    { group := G
      comm := (L.isCommMonObj_grpObjOverMk_iff_mul_comm).mpr
        (RelativeGroupLaw.IsCommutative.prod A.groupScheme_law_commutative B.groupScheme_law_commutative)
      smooth := by
        change SmoothOfRelativeDimension (g + h) (pullback.fst A.group.X.hom B.group.X.hom ≫ A.group.X.hom)
        simpa only [Nat.add_comm g h] using
          (inferInstance : SmoothOfRelativeDimension (h + g)
            (pullback.fst A.group.X.hom B.group.X.hom ≫ A.group.X.hom))
      proper := by change IsProper (pullback.fst A.group.X.hom B.group.X.hom ≫ A.group.X.hom); infer_instance
      connected := GeometricallyConnected.comp (pullback.fst A.group.X.hom B.group.X.hom) A.group.X.hom }

theorem prod_law_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) :
    (GroupScheme.law (A.prod B).group).one t =
      ((GroupScheme.law A.group).prod (GroupScheme.law B.group)).one t :=
  relativeGroupLawOfGrpObj_grpObjOverMk_one _ t

theorem prod_law_mul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x y : SchemeHomOver t (A.prod B).group.X.hom) :
    (GroupScheme.law (A.prod B).group).mul t x y =
      ((GroupScheme.law A.group).prod (GroupScheme.law B.group)).mul t x y :=
  relativeGroupLawOfGrpObj_grpObjOverMk_mul _ t x y

/-- First projection, as a genuine group-scheme morphism. -/
def prodFst : (A.prod B).group ⟶ A.group := by
  let f := pullback.fst A.group.X.hom B.group.X.hom
  have hf : f ≫ A.group.X.hom = (A.prod B).group.X.hom := rfl
  letI : IsMonHom (Over.homMk f hf : (A.prod B).group.X ⟶ A.group.X) := by
    apply GroupScheme.isMonHom_of_pointMap (G := (A.prod B).group) (H := A.group) f hf
    · intro T t
      apply Subtype.ext
      rw [prod_law_one]
      exact pullback.lift_fst _ _ _
    · intro T t x y
      apply Subtype.ext
      rw [prod_law_mul]
      exact pullback.lift_fst _ _ _
  exact Grp.homMk (Over.homMk f hf : (A.prod B).group.X ⟶ A.group.X)

/-- Second projection, as a genuine group-scheme morphism. -/
def prodSnd : (A.prod B).group ⟶ B.group := by
  let f := pullback.snd A.group.X.hom B.group.X.hom
  have hf : f ≫ B.group.X.hom = (A.prod B).group.X.hom := pullback.condition.symm
  letI : IsMonHom (Over.homMk f hf : (A.prod B).group.X ⟶ B.group.X) := by
    apply GroupScheme.isMonHom_of_pointMap (G := (A.prod B).group) (H := B.group) f hf
    · intro T t
      apply Subtype.ext
      rw [prod_law_one]
      exact pullback.lift_snd _ _ _
    · intro T t x y
      apply Subtype.ext
      rw [prod_law_mul]
      exact pullback.lift_snd _ _ _
  exact Grp.homMk (Over.homMk f hf : (A.prod B).group.X ⟶ B.group.X)

end SupersingularCurves.Geometry.AbelianVariety
