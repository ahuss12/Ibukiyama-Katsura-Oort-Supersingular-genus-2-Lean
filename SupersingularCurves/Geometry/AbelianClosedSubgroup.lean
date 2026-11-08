/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.ScalarFrobeniusProductComplement
import SupersingularCurves.Geometry.FrobeniusFiniteFieldGroupDescent

/-! # Actual smooth connected closed subgroups as abelian varieties -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
universe u
namespace SupersingularCurves.Geometry.AbelianVariety
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open FrobeniusFactorGroup ScalarFrobeniusTate
open scoped CategoryTheory.MonObj
variable {K : Type u} [Field K] [IsAlgClosed K] {g : ℕ}
variable (A : AbelianVariety K g) {X : Scheme.{u}} (j : X ⟶ A.group.X.left)
  [IsClosedImmersion j] [ConnectedSpace X]
  (L : RelativeGroupLaw K (j ≫ A.group.X.hom))
  (a : ℕ) [SmoothOfRelativeDimension a (j ≫ A.group.X.hom)]
  (hj : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x y : SchemeHomOver t (j ≫ A.group.X.hom)),
    pointMap j rfl (L.mul t x y) = (GroupScheme.law A.group).mul t
      (pointMap j rfl x) (pointMap j rfl y))

def ofClosedSubgroup : AbelianVariety K a := by
  let G : GroupScheme K := { X := Over.mk (j ≫ A.group.X.hom), grp := L.grpObjOverMk }
  have hc : L.IsCommutative := by
    intro T t x y
    apply Subtype.ext
    apply (cancel_mono j).mp
    exact congrArg Subtype.val ((hj t x y).trans
      ((A.groupScheme_law_commutative t _ _).trans (hj t y x).symm))
  exact {
    group := G
    comm := (L.isCommMonObj_grpObjOverMk_iff_mul_comm).mpr hc
    smooth := by change SmoothOfRelativeDimension a (j ≫ A.group.X.hom); infer_instance
    proper := by change IsProper (j ≫ A.group.X.hom); infer_instance
    connected := geometricallyConnected_of_isAlgClosed_of_isProper_of_connectedSpace
      K (j ≫ A.group.X.hom) }

def ofClosedSubgroupInclusion : (A.ofClosedSubgroup j L a hj).group ⟶ A.group := by
  let E := A.ofClosedSubgroup j L a hj
  letI : GrpObj E.group.X := E.group.grp
  letI : IsMonHom (Over.homMk j rfl : E.group.X ⟶ A.group.X) := by
    apply GroupScheme.isMonHom_of_pointMap (G := E.group) (H := A.group) j rfl
    · intro T t
      simpa only [E, ofClosedSubgroup, GroupScheme.law,
        relativeGroupLawOfGrpObj_grpObjOverMk_one] using
        GroupHomFibre.map_one L (GroupScheme.law A.group) j rfl hj t
    · intro T t x y
      simpa only [E, ofClosedSubgroup, GroupScheme.law,
        relativeGroupLawOfGrpObj_grpObjOverMk_mul] using hj t x y
  exact Grp.homMk (Over.homMk j rfl : E.group.X ⟶ A.group.X)

theorem ofClosedSubgroupInclusion_left :
    underlyingScheme.map (A.ofClosedSubgroupInclusion j L a hj) = j := rfl

theorem ofClosedSubgroup_schemeNsmul (n : ℕ) :
    (GroupScheme.law (A.ofClosedSubgroup j L a hj).group).schemeNsmul n = L.schemeNsmul n :=
  FrobeniusFiniteFieldGroupDescent.schemeNsmul_grpObjOverMk L n

def homToClosedSubgroup
    (π : SchemeHomOver A.group.X.hom (j ≫ A.group.X.hom))
    (hπ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
      (x y : SchemeHomOver t A.group.X.hom),
      pointMap π.1 π.2 ((GroupScheme.law A.group).mul t x y) =
        L.mul t (pointMap π.1 π.2 x) (pointMap π.1 π.2 y)) :
    A.group ⟶ (A.ofClosedSubgroup j L a hj).group := by
  let E := A.ofClosedSubgroup j L a hj
  letI : GrpObj E.group.X := E.group.grp
  letI : IsMonHom (Over.homMk π.1 π.2 : A.group.X ⟶ E.group.X) := by
    apply GroupScheme.isMonHom_of_pointMap (G := A.group) (H := E.group) π.1 π.2
    · intro T t
      simpa only [E, ofClosedSubgroup, GroupScheme.law,
        relativeGroupLawOfGrpObj_grpObjOverMk_one] using
        GroupHomFibre.map_one (GroupScheme.law A.group) L π.1 π.2 hπ t
    · intro T t x y
      simpa only [E, ofClosedSubgroup, GroupScheme.law,
        relativeGroupLawOfGrpObj_grpObjOverMk_mul] using hπ t x y
  exact Grp.homMk (Over.homMk π.1 π.2 : A.group.X ⟶ E.group.X)

end SupersingularCurves.Geometry.AbelianVariety
