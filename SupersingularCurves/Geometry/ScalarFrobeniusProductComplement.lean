/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.ScalarFrobeniusTateQuotientDescent
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_surjective_mul_of_isProper_of_isCommutative
import Theorems.Thm_AlgebraicGeometry_geometricallyConnected_of_isAlgClosed_of_isProper_of_connectedSpace

/-! # Actual abelian complements of actual abelian subvarieties -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
universe u
namespace SupersingularCurves.Geometry.ScalarFrobeniusTate
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open GoodReductionJacobian FrobeniusFactorGroup
open scoped CategoryTheory.MonObj
variable {K : Type u} [Field K] [IsAlgClosed K] {g : ℕ}

/-- A genuine connected smooth closed subgroup of an abelian variety has a
genuine complementary abelian variety, with a surjective addition map. -/
theorem exists_abelian_complement (A : AbelianVariety K g)
    {X : Scheme.{u}} (j : X ⟶ A.group.X.left)
    [IsClosedImmersion j] [ConnectedSpace X]
    (L : RelativeGroupLaw K (j ≫ A.group.X.hom))
    (a : ℕ) [SmoothOfRelativeDimension a (j ≫ A.group.X.hom)]
    (hj : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
      (x y : SchemeHomOver t (j ≫ A.group.X.hom)),
      pointMap j rfl (L.mul t x y) =
        (GroupScheme.law A.group).mul t (pointMap j rfl x) (pointMap j rfl y)) :
    ∃ C : AbelianVariety K (g - a), ∃ i : C.group ⟶ A.group,
      IsClosedImmersion (underlyingScheme.map i) ∧ a ≤ g ∧
      Surjective
        ((GroupScheme.law A.group).mul
          (pullback.fst (j ≫ A.group.X.hom) (underlyingScheme.map i ≫ A.group.X.hom) ≫
            j ≫ A.group.X.hom)
          ⟨pullback.fst (j ≫ A.group.X.hom) (underlyingScheme.map i ≫ A.group.X.hom) ≫ j,
            Category.assoc _ _ _⟩
          ⟨pullback.snd (j ≫ A.group.X.hom) (underlyingScheme.map i ≫ A.group.X.hom) ≫
              underlyingScheme.map i,
            (Category.assoc _ _ _).trans pullback.condition.symm⟩).1 := by
  letI : ConnectedSpace A.group.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton A.group.X.hom
  obtain ⟨N, i, LN, hi, hconn, hdim, hag, hmul, hsurj⟩ :=
    RelativeGroupLaw.exists_isClosedImmersion_surjective_mul_of_isProper_of_isCommutative
      K A.group.X.hom (GroupScheme.law A.group) A.groupScheme_law_commutative g
      j L a hj
  letI := hi
  letI := hconn
  letI := hdim
  let G : GroupScheme K := { X := Over.mk (i ≫ A.group.X.hom), grp := LN.grpObjOverMk }
  letI : GrpObj G.X := G.grp
  have hm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
      (x y : SchemeHomOver t (i ≫ A.group.X.hom)),
      pointMap i rfl (LN.mul t x y) =
        (GroupScheme.law A.group).mul t (pointMap i rfl x) (pointMap i rfl y) := hmul
  have hc : LN.IsCommutative := by
    intro T t x y
    apply Subtype.ext
    apply (cancel_mono i).mp
    exact congrArg Subtype.val ((hm t x y).trans
      ((A.groupScheme_law_commutative t _ _).trans (hm t y x).symm))
  let C : AbelianVariety K (g - a) := {
    group := G
    comm := (LN.isCommMonObj_grpObjOverMk_iff_mul_comm).mpr hc
    smooth := hdim
    proper := by change IsProper (i ≫ A.group.X.hom); infer_instance
    connected := geometricallyConnected_of_isAlgClosed_of_isProper_of_connectedSpace
      K (i ≫ A.group.X.hom) }
  letI : IsMonHom (Over.homMk i rfl : G.X ⟶ A.group.X) := by
    apply GroupScheme.isMonHom_of_pointMap (G := G) (H := A.group) i rfl
    · intro T t
      simpa only [GroupScheme.law, G, relativeGroupLawOfGrpObj_grpObjOverMk_one] using
        GroupHomFibre.map_one LN (GroupScheme.law A.group) i rfl hm t
    · intro T t x y
      simpa only [GroupScheme.law, G, relativeGroupLawOfGrpObj_grpObjOverMk_mul] using hm t x y
  let iG : C.group ⟶ A.group := Grp.homMk (Over.homMk i rfl : G.X ⟶ A.group.X)
  exact ⟨C, iG, hi, hag, hsurj⟩

end SupersingularCurves.Geometry.ScalarFrobeniusTate
