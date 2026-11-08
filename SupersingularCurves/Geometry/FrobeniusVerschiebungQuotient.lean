/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroupGroup
import SupersingularCurves.Geometry.FiniteQuotientGeometry
import SupersingularCurves.Geometry.SmoothFiniteQuotientDimension
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_forall_finset_exists_isAffineOpen_of_isAlgClosed
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_quotient_abelianSchemePropertyBundle_of_finiteFlat_subgroup

/-!
# The actual quotient by the simultaneous Frobenius--Verschiebung kernel

The already constructed closed finite flat subgroup has an actual quotient
scheme. Existence is proved from the pinned finite-flat equivalence-relation
quotient theorem, with its affine-neighborhood hypothesis proved for the actual
abelian variety. The quotient map is finite, flat, surjective, and preserves the
actual group law. Its kernel is identified on every test scheme.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
universe u

namespace SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open GoodReductionJacobian SchemeFrobenius PerfectFieldVerschiebung FrobeniusFactorGroup

variable {K : Type u} [Field K]
variable (p : ℕ) [Fact p.Prime] [CharP K p] [IsAlgClosed K]
variable {g : ℕ} (A : AbelianVariety K g)

/-- Data of a genuine quotient scheme. Existence of these data is proved
below, rather than supplied as a classification hypothesis. -/
structure QuotientData where
  carrier : Scheme.{u}
  structureMap : carrier ⟶ Spec (CommRingCat.of K)
  quotientLaw : RelativeGroupLaw K structureMap
  quotientMap : Twist p A.group.X.hom ⟶ carrier
  over_base : quotientMap ≫ structureMap = base p A
  properties : AbelianSchemePropertyBundle K structureMap
  commutative : quotientLaw.IsCommutative
  [finite : IsFinite quotientMap]
  [flat : Flat quotientMap]
  [locallyOfFinitePresentation : LocallyOfFinitePresentation quotientMap]
  [surjective : Surjective quotientMap]
  [connected : GeometricallyConnected structureMap]
  map_mul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x y : SchemeHomOver t (base p A)),
    pointMap quotientMap over_base ((law p A).mul t x y) =
      quotientLaw.mul t (pointMap quotientMap over_base x) (pointMap quotientMap over_base y)
  kernel : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x : SchemeHomOver t (base p A)),
    pointMap quotientMap over_base x = quotientLaw.one t ↔
      ∃ e : T ⟶ scheme p A, e ≫ inclusion p A = x.1
  coequalizes : pullback.snd (inclusion p A ≫ base p A) (base p A) ≫ quotientMap =
    (law p A).action (inclusion p A) ≫ quotientMap
  relation : IsPullback (pullback.snd (inclusion p A ≫ base p A) (base p A))
    ((law p A).action (inclusion p A)) quotientMap quotientMap
  coequalizer : Nonempty (IsColimit (Cofork.ofπ quotientMap coequalizes))

attribute [instance] QuotientData.finite QuotientData.flat
  QuotientData.locallyOfFinitePresentation QuotientData.surjective QuotientData.connected

/-- The actual finite flat subgroup has an actual smooth proper connected
quotient. All hypotheses of the quotient construction are proved here. -/
theorem nonempty_quotientData : Nonempty (QuotientData p A) := by
  have hA := A.twist_abelianSchemePropertyBundle p
  have hc : (law p A).IsCommutative := twistLaw_commutative p A.group.X.hom (GroupScheme.law A.group)
    A.groupScheme_law_commutative
  have hAF := (law p A).forall_finset_exists_isAffineOpen_of_isAlgClosed hA
  let : IsFinite (inclusion p A ≫ base p A) := structure_isFinite p A
  let : Flat (inclusion p A ≫ base p A) := structure_flat p A
  let : LocallyOfFinitePresentation (inclusion p A ≫ base p A) :=
    structure_locallyOfFinitePresentation p A
  obtain ⟨P, cP, LP, q, hq, w, hP, hcomm, hfinite, hflat, hlfp, hsurj,
    hmul, hkernel, hrelation, hcoeq⟩ :=
    (law p A).exists_quotient_abelianSchemePropertyBundle_of_finiteFlat_subgroup
      hA hc hAF (inclusion p A) (one_factors p A) (mul_factors p A) (inv_factors p A)
  let : Surjective q := hsurj
  let : GeometricallyConnected (base p A) := by
    change GeometricallyConnected (pullback.snd A.group.X.hom (baseMap p K))
    infer_instance
  exact ⟨{
    carrier := P
    structureMap := cP
    quotientLaw := LP
    quotientMap := q
    over_base := hq
    properties := hP
    commutative := hcomm
    finite := hfinite
    flat := hflat
    locallyOfFinitePresentation := hlfp
    surjective := hsurj
    connected := FiniteQuotientGeometry.geometricallyConnected_of_surjective
      (base p A) cP q hq
    map_mul := hmul
    kernel := hkernel
    coequalizes := w
    relation := hrelation
    coequalizer := hcoeq }⟩

/-- A chosen actual quotient, selected from the proved construction. -/
def quotientData : QuotientData p A := Classical.choice (nonempty_quotientData p A)

instance relativeFrobenius_isMonHom :
    IsMonHom (Over.homMk (relative p A.group.X.hom) (relative_toBase p A.group.X.hom) :
      A.group.X ⟶ (twistGroup p A).X) := by
  apply GroupScheme.isMonHom_of_pointMap (G := A.group) (H := twistGroup p A)
    (relative p A.group.X.hom) (relative_toBase p A.group.X.hom)
  · intro T t
    simpa only [GroupScheme.law, twistGroup, law, base, relativeGroupLawOfGrpObj_grpObjOverMk_one,
      pointMap, relativePoint] using
      relative_one p A.group.X.hom (GroupScheme.law A.group) t
  · intro T t x y
    simpa only [GroupScheme.law, twistGroup, law, base, relativeGroupLawOfGrpObj_grpObjOverMk_mul,
      pointMap, relativePoint] using
      relative_mul p A.group.X.hom (GroupScheme.law A.group) t x y

/-- Actual relative Frobenius as a morphism into the independently
constructed Frobenius-twisted internal group scheme. -/
def relativeFrobeniusHom : A.group ⟶ twistGroup p A :=
  ⟨⟨Over.homMk (relative p A.group.X.hom) (relative_toBase p A.group.X.hom)⟩⟩

theorem relativeFrobeniusHom_isIsogeny : IsIsogeny (relativeFrobeniusHom p A) :=
  ⟨(finite_flat_surjective p A.group.X.hom).1,
    (finite_flat_surjective p A.group.X.hom).2.2.2⟩

namespace QuotientData
variable {p A} (D : QuotientData p A)

instance smooth : Smooth D.structureMap := D.properties.smooth

instance proper : IsProper D.structureMap := D.properties.proper

/-- The actual group scheme on the constructed quotient scheme. -/
def group : GroupScheme K where
  X := Over.mk D.structureMap
  grp := D.quotientLaw.grpObjOverMk

instance group_commutative : IsCommMonObj D.group.X :=
  (D.quotientLaw.isCommMonObj_grpObjOverMk_iff_mul_comm).mpr D.commutative

/-- The actual quotient map preserves the identity on all test schemes. -/
theorem map_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) :
    pointMap D.quotientMap D.over_base ((law p A).one t) = D.quotientLaw.one t := by
  let : Group (SchemeHomOver t D.structureMap) := D.quotientLaw.pointGroup t
  let a := pointMap D.quotientMap D.over_base ((law p A).one t)
  have h : a * a = a * 1 := by
    change D.quotientLaw.mul t a a = D.quotientLaw.mul t a (D.quotientLaw.one t)
    rw [D.quotientLaw.mul_one, ← D.map_mul, (law p A).one_mul]
  exact mul_left_cancel h

instance quotientMap_isMonHom :
    IsMonHom (Over.homMk D.quotientMap D.over_base : (twistGroup p A).X ⟶ D.group.X) := by
  apply GroupScheme.isMonHom_of_pointMap
    (G := twistGroup p A) (H := D.group) D.quotientMap D.over_base
  · intro T t
    simpa only [GroupScheme.law, twistGroup, group,
      relativeGroupLawOfGrpObj_grpObjOverMk_one] using D.map_one t
  · intro T t x y
    simpa only [GroupScheme.law, twistGroup, group,
      relativeGroupLawOfGrpObj_grpObjOverMk_mul] using D.map_mul t x y

/-- The quotient is a morphism of genuine internal group schemes. -/
def quotientHom : twistGroup p A ⟶ D.group :=
  ⟨⟨Over.homMk D.quotientMap D.over_base⟩⟩

theorem quotientHom_left : D.quotientHom.hom.hom.left = D.quotientMap := rfl

/-- The actual quotient group morphism is finite and surjective, hence
an isogeny in the existing geometric definition. -/
theorem quotientHom_isIsogeny : IsIsogeny D.quotientHom :=
  ⟨D.finite, D.surjective⟩

/-- The actual finite quotient retains the abelian variety's dimension. -/
instance smoothOfRelativeDimension : SmoothOfRelativeDimension g D.structureMap := by
  let : SmoothOfRelativeDimension g (base p A) := by
    change SmoothOfRelativeDimension g (pullback.snd A.group.X.hom (baseMap p K))
    exact (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
      (IsPullback.of_hasPullback A.group.X.hom (baseMap p K)) A.smooth
  exact FiniteQuotientGeometry.smoothOfRelativeDimension_of_finite_surjective
    (base p A) D.structureMap D.quotientMap D.over_base g D.quotientLaw

/-- The quotient is an actual abelian variety of the original dimension. -/
def abelianVariety : AbelianVariety K g where
  group := D.group
  comm := D.group_commutative
  smooth := D.smoothOfRelativeDimension
  proper := D.properties.proper
  connected := D.connected

/-- The original abelian variety maps to the actual quotient by a genuine
isogeny, composing actual Frobenius and the constructed quotient map. -/
def isogenyFromOriginal : A.group ⟶ D.abelianVariety.group :=
  relativeFrobeniusHom p A ≫ D.quotientHom

theorem isogenyFromOriginal_isIsogeny : IsIsogeny D.isogenyFromOriginal :=
  (relativeFrobeniusHom_isIsogeny p A).comp D.quotientHom_isIsogeny

/-- The genuine source abelian variety, with its independently constructed
Frobenius-twisted group law. -/
def sourceAbelianVariety : AbelianVariety K g where
  group := twistGroup p A
  comm := inferInstance
  smooth := by
    change SmoothOfRelativeDimension g (pullback.snd A.group.X.hom (baseMap p K))
    exact (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
      (IsPullback.of_hasPullback A.group.X.hom (baseMap p K)) A.smooth
  proper := by
    change IsProper (pullback.snd A.group.X.hom (baseMap p K))
    infer_instance
  connected := by
    change GeometricallyConnected (pullback.snd A.group.X.hom (baseMap p K))
    infer_instance

end QuotientData
end SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup
