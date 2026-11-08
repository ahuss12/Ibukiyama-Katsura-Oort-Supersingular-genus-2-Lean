/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusVerschiebungQuotientFactorsDegree

/-!
# Genuine group morphisms from the simultaneous-kernel quotient

The actual descended Frobenius and Verschiebung preserve the group law on
every test scheme. They therefore define morphisms from the actual quotient
group scheme to the actual double Frobenius twist and original abelian variety.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open SchemeFrobenius FrobeniusFactorGroup

variable {K : Type u} [Field K]
variable {p : ℕ} [Fact p.Prime] [CharP K p] [IsAlgClosed K]
variable {g : ℕ} {A : AbelianVariety K g} (D : QuotientData p A)

private theorem map_one_of_mul
    {Y : Scheme.{u}} {d : Y ⟶ Spec (CommRingCat.of K)}
    (M : RelativeGroupLaw K d) (f : SchemeHomOver D.structureMap d)
    (hm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
      (x y : SchemeHomOver t D.structureMap),
      pointMap f.1 f.2 (D.quotientLaw.mul t x y) =
        M.mul t (pointMap f.1 f.2 x) (pointMap f.1 f.2 y))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) :
    pointMap f.1 f.2 (D.quotientLaw.one t) = M.one t := by
  let : Group (SchemeHomOver t d) := M.pointGroup t
  let a := pointMap f.1 f.2 (D.quotientLaw.one t)
  have h : a * a = a * 1 := by
    change M.mul t a a = M.mul t a (M.one t)
    rw [M.mul_one, ← hm, D.quotientLaw.one_mul]
  exact mul_left_cancel h

theorem frobeniusFactor_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) :
    pointMap D.frobeniusFactor.1 D.frobeniusFactor.2 (D.quotientLaw.one t) =
      (twistLaw p (base p A) (law p A)).one t :=
  D.map_one_of_mul _ D.frobeniusFactor D.frobeniusFactor_mul t

theorem verschiebungFactor_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) :
    pointMap D.verschiebungFactor.1 D.verschiebungFactor.2 (D.quotientLaw.one t) =
      (GroupScheme.law A.group).one t :=
  D.map_one_of_mul _ D.verschiebungFactor D.verschiebungFactor_mul t

instance frobeniusFactor_isMonHom :
    IsMonHom (Over.homMk D.frobeniusFactor.1 D.frobeniusFactor.2 :
      D.group.X ⟶ (A.doubleFrobeniusTwistGroup p).X) := by
  apply GroupScheme.isMonHom_of_pointMap
    (G := D.group) (H := A.doubleFrobeniusTwistGroup p)
    D.frobeniusFactor.1 D.frobeniusFactor.2
  · intro T t
    simpa only [GroupScheme.law, group, AbelianVariety.doubleFrobeniusTwistGroup,
      relativeGroupLawOfGrpObj_grpObjOverMk_one, base, law] using D.frobeniusFactor_one t
  · intro T t x y
    simpa only [GroupScheme.law, group, AbelianVariety.doubleFrobeniusTwistGroup,
      relativeGroupLawOfGrpObj_grpObjOverMk_mul, base, law] using D.frobeniusFactor_mul t x y

instance verschiebungFactor_isMonHom :
    IsMonHom (Over.homMk D.verschiebungFactor.1 D.verschiebungFactor.2 :
      D.group.X ⟶ A.group.X) := by
  apply GroupScheme.isMonHom_of_pointMap
    (G := D.group) (H := A.group) D.verschiebungFactor.1 D.verschiebungFactor.2
  · intro T t
    simpa only [GroupScheme.law, group, relativeGroupLawOfGrpObj_grpObjOverMk_one] using
      D.verschiebungFactor_one t
  · intro T t x y
    simpa only [GroupScheme.law, group, relativeGroupLawOfGrpObj_grpObjOverMk_mul] using
      D.verschiebungFactor_mul t x y

/-- The descended actual Frobenius as a genuine group-scheme morphism. -/
def frobeniusFactorHom : D.group ⟶ A.doubleFrobeniusTwistGroup p :=
  Grp.homMk (Over.homMk D.frobeniusFactor.1 D.frobeniusFactor.2)

/-- The descended actual Verschiebung as a genuine group-scheme morphism. -/
def verschiebungFactorHom : D.group ⟶ A.group :=
  Grp.homMk (Over.homMk D.verschiebungFactor.1 D.verschiebungFactor.2)

theorem frobeniusFactorHom_left : D.frobeniusFactorHom.hom.hom.left = D.frobeniusFactor.1 := rfl

theorem verschiebungFactorHom_left :
    D.verschiebungFactorHom.hom.hom.left = D.verschiebungFactor.1 := rfl

/-- The descended Frobenius is finite and surjective as an actual group morphism. -/
theorem frobeniusFactorHom_isIsogeny : IsIsogeny D.frobeniusFactorHom :=
  ⟨D.frobeniusFactor_isFinite, D.frobeniusFactor_surjective⟩

/-- The descended Verschiebung is finite and surjective as an actual group morphism. -/
theorem verschiebungFactorHom_isIsogeny : IsIsogeny D.verschiebungFactorHom :=
  ⟨D.verschiebungFactor_isFinite, D.verschiebungFactor_surjective⟩

end SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData
