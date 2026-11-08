/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusVerschiebungQuotientFactorHom
import SupersingularCurves.Geometry.FrobeniusVerschiebungQuotientFactorization

/-!
# Actual cotangent maps for the quotient and descended Verschiebung

The four maps are differentials of the actual quotient, descended
Verschiebung, and their actual Frobenius base changes. Their composition
identities follow from the proved factorizations of actual scheme morphisms.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u

namespace SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open SchemeFrobenius PerfectFieldVerschiebung PointedCotangent FrobeniusFactorGroup

variable {K : Type u} [Field K]
variable {p : ℕ} [Fact p.Prime] [CharP K p] [IsAlgClosed K]
variable {g : ℕ} {A : AbelianVariety K g} (D : QuotientData p A)

local instance : Smooth D.group.X.hom := D.smooth

/-- The quotient carries the original twist identity to its own actual identity. -/
theorem quotientMap_zero :
    (GroupScheme.twistZero p A.group).1 ≫ D.quotientMap = (GroupScheme.zero D.group).1 := by
  simpa only [GroupScheme.zero, GroupScheme.twistZero, GroupScheme.law, group,
    relativeGroupLawOfGrpObj_grpObjOverMk_one, pointMap, law] using
    congrArg Subtype.val (D.map_one (𝟙 _))

theorem verschiebungFactor_zero :
    (GroupScheme.zero D.group).1 ≫ D.verschiebungFactor.1 = (GroupScheme.zero A.group).1 :=
  GroupScheme.zero_natural D.verschiebungFactorHom

theorem quotientTwistMap_zero :
    (GroupScheme.twistZero p (twistGroup p A)).1 ≫ D.quotientTwistMap =
      (GroupScheme.twistZero p D.group).1 :=
  GroupScheme.twistZero_natural p D.quotientHom

theorem verschiebungFactorTwist_zero :
    (GroupScheme.twistZero p D.group).1 ≫
        SchemeFrobenius.map p D.verschiebungFactor.1 D.verschiebungFactor.2 =
      (GroupScheme.twistZero p A.group).1 :=
  GroupScheme.twistZero_natural p D.verschiebungFactorHom

/-- The actual quotient differential `dq : Cot(Q) → Cot(A^(p))`. -/
def quotientCotangent :
    Cotangent D.structureMap (GroupScheme.zero D.group) →ₗ[K]
      Cotangent (base p A) (GroupScheme.twistZero p A.group) :=
  differential (base p A) (GroupScheme.twistZero p A.group)
    D.quotientMap D.over_base D.quotientMap_zero

/-- The actual descended Verschiebung differential `dψ : Cot(A) → Cot(Q)`. -/
def verschiebungFactorCotangent :
    Cotangent A.group.X.hom (GroupScheme.zero A.group) →ₗ[K]
      Cotangent D.structureMap (GroupScheme.zero D.group) :=
  differential D.structureMap (GroupScheme.zero D.group)
    D.verschiebungFactor.1 D.verschiebungFactor.2 D.verschiebungFactor_zero

/-- The differential of the actual Frobenius twist of the quotient map. -/
def quotientTwistCotangent :
    Cotangent (SchemeFrobenius.toBase p D.structureMap) (GroupScheme.twistZero p D.group) →ₗ[K]
      Cotangent (SchemeFrobenius.toBase p (base p A))
        (GroupScheme.twistZero p (twistGroup p A)) :=
  differential (SchemeFrobenius.toBase p (base p A))
    (GroupScheme.twistZero p (twistGroup p A))
    D.quotientTwistMap D.quotientTwistMap_over D.quotientTwistMap_zero

/-- The differential of the actual Frobenius twist of descended Verschiebung. -/
def verschiebungFactorTwistCotangent :
    Cotangent (base p A) (GroupScheme.twistZero p A.group) →ₗ[K]
      Cotangent (SchemeFrobenius.toBase p D.structureMap) (GroupScheme.twistZero p D.group) :=
  differential (SchemeFrobenius.toBase p D.structureMap) (GroupScheme.twistZero p D.group)
    (SchemeFrobenius.map p D.verschiebungFactor.1 D.verschiebungFactor.2)
    (SchemeFrobenius.map_toBase p D.verschiebungFactor.1 D.verschiebungFactor.2)
    D.verschiebungFactorTwist_zero

include D in
theorem verschiebungTwist_zero :
    (GroupScheme.twistZero p (twistGroup p A)).1 ≫
      SchemeFrobenius.map p (V p A)
        (verschiebung_over p A.group.X.hom (GroupScheme.law A.group)
          A.groupScheme_law_commutative) = (GroupScheme.twistZero p A.group).1 := by
  have h := GroupScheme.twistZero_natural p (D.quotientHom ≫ D.verschiebungFactorHom)
  change (GroupScheme.twistZero p (twistGroup p A)).1 ≫
    SchemeFrobenius.map p (D.quotientMap ≫ D.verschiebungFactor.1) _ = _ at h
  simpa only [D.quotientMap_verschiebungFactor] using h

/-- The actual differential of the base change of the original Verschiebung. -/
def verschiebungTwistCotangent :
    Cotangent (base p A) (GroupScheme.twistZero p A.group) →ₗ[K]
      Cotangent (SchemeFrobenius.toBase p (base p A))
        (GroupScheme.twistZero p (twistGroup p A)) :=
  differential (SchemeFrobenius.toBase p (base p A))
    (GroupScheme.twistZero p (twistGroup p A))
    (SchemeFrobenius.map p (V p A)
      (verschiebung_over p A.group.X.hom (GroupScheme.law A.group)
        A.groupScheme_law_commutative))
    (SchemeFrobenius.map_toBase p (V p A)
      (verschiebung_over p A.group.X.hom (GroupScheme.law A.group)
        A.groupScheme_law_commutative)) D.verschiebungTwist_zero

/-- The original actual Verschiebung differential factors as `dq ∘ dψ`. -/
theorem verschiebungCotangent_eq_quotient_comp_factor :
    GroupScheme.verschiebungCotangent p A.group (GroupScheme.law_commutative A.group) =
      D.quotientCotangent ∘ₗ D.verschiebungFactorCotangent := by
  unfold quotientCotangent verschiebungFactorCotangent GroupScheme.verschiebungCotangent
  rw [← differential_comp]
  congr 1
  exact D.quotientMap_verschiebungFactor.symm

/-- The differential of the actual twist of Verschiebung factors as `dq^p ∘ dψ^p`. -/
theorem verschiebungTwistCotangent_eq_quotientTwist_comp_factorTwist :
    D.verschiebungTwistCotangent =
      D.quotientTwistCotangent ∘ₗ D.verschiebungFactorTwistCotangent := by
  unfold verschiebungTwistCotangent quotientTwistCotangent verschiebungFactorTwistCotangent
  rw [← differential_comp]
  simp only [quotientTwistMap, ← SchemeFrobenius.map_comp,
    D.quotientMap_verschiebungFactor]

/-- The quotient's own actual Verschiebung differential factors as `dψ^p ∘ dq`. -/
theorem quotient_verschiebungCotangent_eq_factorTwist_comp_quotient :
    GroupScheme.verschiebungCotangent p D.group (GroupScheme.law_commutative D.group) =
      D.verschiebungFactorTwistCotangent ∘ₗ D.quotientCotangent := by
  unfold verschiebungFactorTwistCotangent quotientCotangent GroupScheme.verschiebungCotangent
  rw [← differential_comp]
  congr 1
  exact D.verschiebung_eq_factorTwist_comp_quotient

end SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData
