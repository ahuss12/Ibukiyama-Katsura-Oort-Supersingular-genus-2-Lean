/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.AbelianClosedSubgroup
import SupersingularCurves.Geometry.AbelianIsogenyQuasiInverse
import SupersingularCurves.Geometry.ScalarFrobeniusProductComplementKernel

/-! # Actual product isogenies from a smooth connected closed subgroup

Poincare's argument constructs the complement and the quasi-retraction.
The addition kernel is bounded on all test schemes, hence finite. Faithfully
flat descent then constructs an isogeny in the reverse direction as well.

The existence of the initial elliptic subgroup in a zero-dV surface is a
separate global obligation; it is not assumed to follow from a Tate pairing.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
universe u
namespace SupersingularCurves.Geometry.ScalarFrobeniusTate
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open FrobeniusFactorGroup AbelianVariety
open scoped CategoryTheory.MonObj
variable {K : Type u} [Field K] [IsAlgClosed K] {g : ℕ}

/-- An actual smooth connected closed subgroup constructs complementary
abelian varieties and actual finite surjective product maps in both directions. -/
theorem exists_product_isogeny_of_closed_subgroup (A : AbelianVariety K g)
    {X : Scheme.{u}} (j : X ⟶ A.group.X.left)
    [IsClosedImmersion j] [ConnectedSpace X]
    (L : RelativeGroupLaw K (j ≫ A.group.X.hom))
    (a : ℕ) [SmoothOfRelativeDimension a (j ≫ A.group.X.hom)]
    (hj : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
      (x y : SchemeHomOver t (j ≫ A.group.X.hom)),
      pointMap j rfl (L.mul t x y) =
        (GroupScheme.law A.group).mul t (pointMap j rfl x) (pointMap j rfl y)) :
    ∃ (E : AbelianVariety K a) (C : AbelianVariety K (g - a))
      (jG : E.group ⟶ A.group) (iG : C.group ⟶ A.group),
      IsClosedImmersion (underlyingScheme.map jG) ∧
      IsClosedImmersion (underlyingScheme.map iG) ∧ a ≤ g ∧
      IsIsogeny (E.prodCopair C jG iG) ∧
      ∃ q : A.group ⟶ (E.prod C).group, IsIsogeny q := by
  letI : ConnectedSpace A.group.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton A.group.X.hom
  letI : Smooth (j ≫ A.group.X.hom) := SmoothOfRelativeDimension.smooth a _
  letI : Smooth A.group.X.hom := SmoothOfRelativeDimension.smooth g _
  obtain ⟨n, π, hn, hπ, hπj⟩ :=
    RelativeGroupLaw.exists_schemeHomOverComp_schemeHomOverComp_eq_nsmul_of_isProper_of_isCommutative_of_isAlgClosed
      K A.group.X.hom (GroupScheme.law A.group) A.groupScheme_law_commutative j L hj
  obtain ⟨N, i, LN, hi, hconn, hdim, hag, hmul, hsurj, hker⟩ :=
    Poincare.exists_complement_with_kernel K A.group.X.hom
      (GroupScheme.law A.group) A.groupScheme_law_commutative g j L a hj n hn π hπ hπj
  letI := hi
  letI := hconn
  letI := hdim
  let E := A.ofClosedSubgroup j L a hj
  let C := A.ofClosedSubgroup i LN (g - a) hmul
  let jG : E.group ⟶ A.group := A.ofClosedSubgroupInclusion j L a hj
  let iG : C.group ⟶ A.group := A.ofClosedSubgroupInclusion i LN (g - a) hmul
  let rG : A.group ⟶ E.group := A.homToClosedSubgroup j L a hj π hπ
  have hjr : jG ≫ rG = multiplication E n := by
    apply Grp.hom_ext
    apply Over.OverMorphism.ext
    change j ≫ π.1 = (GroupScheme.law E.group).schemeNsmul n
    rw [ofClosedSubgroup_schemeNsmul]
    have H := congrArg Subtype.val (hπj (j ≫ A.group.X.hom) RelativeGroupLaw.idPoint)
    simpa only [NeronModelInfra.schemeHomOverComp_coe, RelativeGroupLaw.idPoint,
      Category.id_comp, RelativeGroupLaw.schemeNsmul] using H
  have hir : iG ≫ rG = C.trivialHom E := by
    apply Grp.hom_ext
    apply Over.OverMorphism.ext
    change i ≫ π.1 = ((GroupScheme.law E.group).one (i ≫ A.group.X.hom)).1
    have H := congrArg Subtype.val (hker (i ≫ A.group.X.hom) RelativeGroupLaw.idPoint)
    simpa only [E, ofClosedSubgroup, GroupScheme.law,
      relativeGroupLawOfGrpObj_grpObjOverMk_one, NeronModelInfra.schemeHomOverComp_coe,
      RelativeGroupLaw.idPoint, Category.id_comp] using H
  haveI : IsClosedImmersion (underlyingScheme.map jG) := inferInstanceAs (IsClosedImmersion j)
  haveI : IsClosedImmersion (underlyingScheme.map iG) := hi
  have hs : Surjective (underlyingScheme.map (E.prodCopair C jG iG)) := hsurj
  obtain ⟨hprod, hflat⟩ :=
    E.prodCopair_isIsogeny_of_quasiRetraction C A jG iG rG n (Nat.ne_of_gt hn) hjr hir hs
  letI := hflat
  obtain ⟨q, _, _, hq⟩ := (E.prod C).exists_quasiInverse_of_kernel_killed A
    (E.prodCopair C jG iG) hprod n (Nat.ne_of_gt hn)
    (E.prodCopair_kernel_killed_of_quasiRetraction C A jG iG rG n hjr hir)
  exact ⟨E, C, jG, iG, inferInstance, inferInstance, hag, hprod, q, hq⟩

end SupersingularCurves.Geometry.ScalarFrobeniusTate
