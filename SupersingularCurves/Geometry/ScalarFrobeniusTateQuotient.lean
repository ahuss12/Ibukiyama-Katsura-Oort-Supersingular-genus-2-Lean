/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusFactorGroup
import SupersingularCurves.Geometry.FiniteQuotientGeometry
import SupersingularCurves.Geometry.SmoothFiniteQuotientDimension
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_quotient_abelianSchemePropertyBundle_of_finiteFlat_subgroup
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_existsUnique_quotient_desc_hom_of_isColimit
import Theorems.Thm_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_isImmersion_proj
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_forall_finset_exists_isAffineOpen_of_isAlgClosed

/-!
# Actual finite subgroup quotients for Tate's construction

A closed finite flat subgroup of an actual abelian variety has an actual
quotient abelian variety of the same dimension, provided finite subsets have
affine neighborhoods. The latter hypothesis follows from any supplied genuine
projective immersion. The construction records the group law, the kernel on
all test schemes, its quotient universal property, and its exact finite degree.

This is the geometric quotient step; it does not assert Tate Hom surjectivity
or the superspecial elliptic-product classification.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
universe u

namespace SupersingularCurves.Geometry.ScalarFrobeniusTate
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open GoodReductionJacobian FrobeniusFactorGroup
open scoped CategoryTheory.MonObj

variable {K : Type u} [Field K] {g : ℕ} (A : AbelianVariety K g)

/-- A genuine closed finite flat subgroup, including all-test-scheme closure. -/
structure FiniteSubgroup where
  carrier : Scheme.{u}
  inclusion : carrier ⟶ A.group.X.left
  [closed : IsClosedImmersion inclusion]
  [finite : IsFinite (inclusion ≫ A.group.X.hom)]
  [flat : Flat (inclusion ≫ A.group.X.hom)]
  [lfp : LocallyOfFinitePresentation (inclusion ≫ A.group.X.hom)]
  one : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)),
    ∃ e : T ⟶ carrier, e ≫ inclusion = ((GroupScheme.law A.group).one t).1
  mul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x y : SchemeHomOver t A.group.X.hom),
    (∃ e : T ⟶ carrier, e ≫ inclusion = x.1) →
    (∃ e : T ⟶ carrier, e ≫ inclusion = y.1) →
    ∃ e : T ⟶ carrier, e ≫ inclusion = ((GroupScheme.law A.group).mul t x y).1
  inv : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x : SchemeHomOver t A.group.X.hom),
    (∃ e : T ⟶ carrier, e ≫ inclusion = x.1) →
    ∃ e : T ⟶ carrier, e ≫ inclusion = ((GroupScheme.law A.group).inv t x).1

attribute [instance] FiniteSubgroup.closed FiniteSubgroup.finite
  FiniteSubgroup.flat FiniteSubgroup.lfp

variable (H : FiniteSubgroup A)

/-- Full actual quotient data, whose existence is proved below. -/
structure Quotient where
  variety : AbelianVariety K g
  map : A.group ⟶ variety.group
  [finite : IsFinite (underlyingScheme.map map)]
  [flat : Flat (underlyingScheme.map map)]
  [lfp : LocallyOfFinitePresentation (underlyingScheme.map map)]
  [surjective : Surjective (underlyingScheme.map map)]
  kernel : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x : SchemeHomOver t A.group.X.hom),
    pointMap (underlyingScheme.map map) map.hom.hom.w x =
        (GroupScheme.law variety.group).one t ↔
      ∃ e : T ⟶ H.carrier, e ≫ H.inclusion = x.1
  coequalizes : pullback.snd (H.inclusion ≫ A.group.X.hom) A.group.X.hom ≫
      underlyingScheme.map map =
    (GroupScheme.law A.group).action H.inclusion ≫ underlyingScheme.map map
  relation : IsPullback (pullback.snd (H.inclusion ≫ A.group.X.hom) A.group.X.hom)
    ((GroupScheme.law A.group).action H.inclusion)
    (underlyingScheme.map map) (underlyingScheme.map map)
  coequalizer : Nonempty (IsColimit (Cofork.ofπ (underlyingScheme.map map) coequalizes))

attribute [instance] Quotient.finite Quotient.flat Quotient.lfp Quotient.surjective

/-- Actual existence of the quotient; no quotient variety or isogeny is an input. -/
theorem nonempty_quotient
    (hAF : ∀ S : Finset A.group.X.left, ∃ U : A.group.X.left.Opens,
      IsAffineOpen U ∧ ∀ x ∈ S, x ∈ U) : Nonempty (Quotient A H) := by
  obtain ⟨P, cP, L, q, hq, w, hP, hc, hfin, hflat, hlfp, hsurj,
    hmul, hker, hrel, hcoeq⟩ :=
    (GroupScheme.law A.group).exists_quotient_abelianSchemePropertyBundle_of_finiteFlat_subgroup
      A.abelianSchemePropertyBundle A.groupScheme_law_commutative hAF H.inclusion
      H.one H.mul H.inv
  let : IsFinite q := hfin
  let : Flat q := hflat
  let : Surjective q := hsurj
  let : Smooth cP := hP.smooth
  let G : GroupScheme K := { X := Over.mk cP, grp := L.grpObjOverMk }
  letI : GrpObj G.X := G.grp
  let B : AbelianVariety K g := {
    group := G
    comm := (L.isCommMonObj_grpObjOverMk_iff_mul_comm).mpr hc
    smooth := FiniteQuotientGeometry.smoothOfRelativeDimension_of_finite_surjective
      A.group.X.hom cP q hq g L
    proper := hP.proper
    connected := FiniteQuotientGeometry.geometricallyConnected_of_surjective
      A.group.X.hom cP q hq }
  have hone : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)),
      pointMap q hq ((GroupScheme.law A.group).one t) = L.one t := by
    intro T t
    let : Group (SchemeHomOver t cP) := L.pointGroup t
    let a := pointMap q hq ((GroupScheme.law A.group).one t)
    have ha : a * a = a * 1 := by
      change L.mul t a a = L.mul t a (L.one t)
      rw [L.mul_one]
      exact (hmul t ((GroupScheme.law A.group).one t)
        ((GroupScheme.law A.group).one t)).symm.trans
          (congrArg (pointMap q hq) ((GroupScheme.law A.group).one_mul t _))
    exact mul_left_cancel ha
  let : IsMonHom (Over.homMk q hq : A.group.X ⟶ G.X) := by
    apply GroupScheme.isMonHom_of_pointMap (G := A.group) (H := G) q hq
    · intro T t
      simpa only [GroupScheme.law, G, relativeGroupLawOfGrpObj_grpObjOverMk_one] using hone t
    · intro T t x y
      simpa only [GroupScheme.law, G, relativeGroupLawOfGrpObj_grpObjOverMk_mul, pointMap] using hmul t x y
  let qG : A.group ⟶ B.group := ⟨⟨Over.homMk q hq⟩⟩
  refine ⟨{
    variety := B
    map := qG
    finite := hfin
    flat := hflat
    lfp := hlfp
    surjective := hsurj
    kernel := ?_
    coequalizes := w
    relation := hrel
    coequalizer := hcoeq }⟩
  intro T t x
  change pointMap q hq x = (GroupScheme.law G).one t ↔ _
  simpa only [G, GroupScheme.law, relativeGroupLawOfGrpObj_grpObjOverMk_one, pointMap]
    using hker t x

/-- A projective immersion proves the affine-neighborhood input to the
actual quotient construction over any field, including a finite field. -/
theorem nonempty_quotient_of_projectiveImmersion
    {R : Type u} [CommRing R] {σ : Type u} [SetLike σ R] [AddSubgroupClass σ R]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (i : A.group.X.left ⟶ Proj 𝒜) [IsImmersion i] :
    Nonempty (Quotient A H) :=
  nonempty_quotient A H (exists_isAffineOpen_forall_mem_of_isImmersion_proj 𝒜 i)

/-- Over an algebraically closed field every actual abelian variety supplies
all affine neighborhoods required for its finite subgroup quotient. -/
theorem nonempty_quotient_of_isAlgClosed [IsAlgClosed K] : Nonempty (Quotient A H) :=
  nonempty_quotient A H
    ((GroupScheme.law A.group).forall_finset_exists_isAffineOpen_of_isAlgClosed
      A.abelianSchemePropertyBundle)

namespace Quotient
variable {A H} (D : Quotient A H)

/-- The constructed quotient map is an actual isogeny. -/
theorem isIsogeny : IsIsogeny D.map := ⟨D.finite, D.surjective⟩

/-- Its scheme-theoretic degree equals the rank of the actual subgroup. -/
theorem finrank_eq_subgroup (y : D.variety.group.X.left) :
    (underlyingScheme.map D.map).finrank y =
      (H.inclusion ≫ A.group.X.hom).finrank (IsLocalRing.closedPoint K) := by
  obtain ⟨x, rfl⟩ := (underlyingScheme.map D.map).surjective y
  exact (Scheme.Hom.finrank_of_isPullback _ _ _ _ D.relation.flip x).symm.trans
    ((Scheme.Hom.finrank_pullback_snd _ _ x).trans
      (congrArg (H.inclusion ≫ A.group.X.hom).finrank (Subsingleton.elim _ _)))

end Quotient
end SupersingularCurves.Geometry.ScalarFrobeniusTate
