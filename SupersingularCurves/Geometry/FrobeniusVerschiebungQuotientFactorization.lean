/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusVerschiebungQuotientDescent

/-!
# Frobenius and Verschiebung of the actual quotient

The descended maps give factorizations of the quotient's own Frobenius and
Verschiebung. All twists are actual fibre products over the Frobenius of the
field, and cancellation uses proved faithful-flat epimorphisms.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
universe u

namespace SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open GoodReductionJacobian SchemeFrobenius PerfectFieldVerschiebung FrobeniusFactorGroup

variable {K : Type u} [Field K]
variable {p : ℕ} [Fact p.Prime] [CharP K p] [IsAlgClosed K]
variable {g : ℕ} {A : AbelianVariety K g} (D : QuotientData p A)

omit [IsAlgClosed K] in
private theorem nsmul_recovery {Y : Scheme.{u}} {d : Y ⟶ Spec (CommRingCat.of K)}
    (M : RelativeGroupLaw K d) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (n : ℕ) (x : SchemeHomOver t d) :
    letI := M.grpObjOverMk
    (relativeGroupLawOfGrpObj K d).nsmul t n x = M.nsmul t n x := by
  let := M.grpObjOverMk
  induction n with
  | zero => simp only [RelativeGroupLaw.nsmul_zero, relativeGroupLawOfGrpObj_grpObjOverMk_one]
  | succ n ih =>
    simp only [RelativeGroupLaw.nsmul_succ, relativeGroupLawOfGrpObj_grpObjOverMk_mul, ih]

omit [IsAlgClosed K] in
private theorem schemeNsmul_recovery {Y : Scheme.{u}} {d : Y ⟶ Spec (CommRingCat.of K)}
    (M : RelativeGroupLaw K d) (n : ℕ) :
    letI := M.grpObjOverMk
    (relativeGroupLawOfGrpObj K d).schemeNsmul n = M.schemeNsmul n :=
  congrArg Subtype.val (nsmul_recovery M d n RelativeGroupLaw.idPoint)

/-- Multiplication by an integer commutes with the actual quotient. -/
theorem quotientMap_nsmul (n : ℕ) :
    (law p A).schemeNsmul n ≫ D.quotientMap =
      D.quotientMap ≫ (GroupScheme.law D.group).schemeNsmul n := by
  have h := GroupScheme.schemeNsmul_natural D.quotientHom n
  change (GroupScheme.law (twistGroup p A)).schemeNsmul n ≫ D.quotientMap =
    D.quotientMap ≫ (GroupScheme.law D.group).schemeNsmul n at h
  simpa only [GroupScheme.law, twistGroup, schemeNsmul_recovery] using h

/-- The actual Frobenius base-change of the constructed quotient map. -/
def quotientTwistMap : Twist p (base p A) ⟶ Twist p D.structureMap :=
  SchemeFrobenius.map p D.quotientMap D.over_base

@[reassoc]
theorem quotientTwistMap_over :
    D.quotientTwistMap ≫ SchemeFrobenius.toBase p D.structureMap =
      SchemeFrobenius.toBase p (base p A) :=
  SchemeFrobenius.map_toBase p D.quotientMap D.over_base

/-- The quotient's Frobenius is the descended Frobenius followed by the
actual Frobenius twist of the quotient map. -/
theorem frobenius_eq_factor_comp_quotientTwist :
    relative p D.structureMap = D.frobeniusFactor.1 ≫ D.quotientTwistMap := by
  apply (cancel_epi D.quotientMap).mp
  rw [← Category.assoc, D.quotientMap_frobeniusFactor]
  exact (relative_natural p D.quotientMap D.over_base).symm

/-- The quotient's Verschiebung is the actual twist of the descended
Verschiebung followed by the original quotient map. -/
theorem verschiebung_eq_factorTwist_comp_quotient :
    verschiebung p D.structureMap (GroupScheme.law D.group)
        (GroupScheme.law_commutative D.group) =
      SchemeFrobenius.map p D.verschiebungFactor.1 D.verschiebungFactor.2 ≫
        D.quotientMap := by
  let hF := finite_flat_surjective p D.structureMap
  let : IsFinite (relative p D.structureMap) := hF.1
  let : Flat (relative p D.structureMap) := hF.2.1
  let : Surjective (relative p D.structureMap) := hF.2.2.2
  apply (cancel_epi (relative p D.structureMap)).mp
  rw [frobenius_verschiebung]
  apply (cancel_epi D.quotientMap).mp
  rw [← D.quotientMap_nsmul]
  calc
    (law p A).schemeNsmul p ≫ D.quotientMap =
        (V p A ≫ relative p A.group.X.hom) ≫ D.quotientMap := by
      rw [verschiebung_frobenius]
    _ = (relative p (base p A) ≫
        SchemeFrobenius.map p (V p A) (verschiebung_over p A.group.X.hom
          (GroupScheme.law A.group) A.groupScheme_law_commutative)) ≫ D.quotientMap := by
      rw [relative_natural]
    _ = ((relative p (base p A) ≫ D.quotientTwistMap) ≫
        SchemeFrobenius.map p D.verschiebungFactor.1 D.verschiebungFactor.2) ≫
          D.quotientMap := by
      have hm : SchemeFrobenius.map p (V p A)
          (verschiebung_over p A.group.X.hom (GroupScheme.law A.group)
            A.groupScheme_law_commutative) =
          D.quotientTwistMap ≫
            SchemeFrobenius.map p D.verschiebungFactor.1 D.verschiebungFactor.2 := by
        rw [quotientTwistMap, ← SchemeFrobenius.map_comp]
        simp only [D.quotientMap_verschiebungFactor]
      simp only [hm, Category.assoc]
    _ = D.quotientMap ≫ relative p D.structureMap ≫
        SchemeFrobenius.map p D.verschiebungFactor.1 D.verschiebungFactor.2 ≫
          D.quotientMap := by
      rw [quotientTwistMap, relative_natural]
      simp only [Category.assoc]

end SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData
