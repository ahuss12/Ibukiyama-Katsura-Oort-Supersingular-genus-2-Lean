/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusVerschiebungQuotient
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_existsUnique_quotient_desc_hom_of_isColimit

/-!
# Actual Frobenius and Verschiebung descend through the constructed quotient

Both actual scheme morphisms annihilate the constructed finite subgroup.
The actual quotient coequalizer therefore supplies unique morphisms from
the quotient, preserving the independently constructed group laws.
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
private theorem one_coe {Y : Scheme.{u}} {d : Y ⟶ Spec (CommRingCat.of K)}
    (M : RelativeGroupLaw K d) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) :
    (M.one t).1 = t ≫ (M.one (𝟙 _)).1 :=
  (congrArg Subtype.val (M.one_natural (𝟙 _) t t (Category.comp_id t))).symm

variable {Y : Scheme.{u}} {d : Y ⟶ Spec (CommRingCat.of K)}
variable (M : RelativeGroupLaw K d) (f : Twist p A.group.X.hom ⟶ Y)
  (hf : f ≫ d = base p A)
  (hm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x y : SchemeHomOver t (base p A)),
    pointMap f hf ((law p A).mul t x y) = M.mul t (pointMap f hf x) (pointMap f hf y))
  (hk : inclusion p A ≫ f = toBase p A ≫ (M.one (𝟙 _)).1)

include hf hm hk in
/-- Descent through the actual quotient with its actual group law. -/
theorem existsUnique_desc :
    ∃! ψ : SchemeHomOver D.structureMap d, D.quotientMap ≫ ψ.1 = f ∧
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
        (x y : SchemeHomOver t D.structureMap),
        pointMap ψ.1 ψ.2 (D.quotientLaw.mul t x y) =
          M.mul t (pointMap ψ.1 ψ.2 x) (pointMap ψ.1 ψ.2 y) := by
  apply (law p A).existsUnique_quotient_desc_hom_of_isColimit (inclusion p A)
    D.quotientMap D.coequalizes D.coequalizer.some D.over_base D.quotientLaw D.map_mul
    M ⟨f, hf⟩ hm
  intro T t e he
  apply Subtype.ext
  change (e ≫ inclusion p A) ≫ f = (M.one t).1
  have ht : e ≫ toBase p A = t := he
  rw [Category.assoc, hk, ← Category.assoc, ht, ← one_coe]

/-- The uniquely descended morphism over the field. -/
def desc : SchemeHomOver D.structureMap d :=
  Classical.choose (D.existsUnique_desc M f hf hm hk)

theorem quotientMap_desc : D.quotientMap ≫ (D.desc M f hf hm hk).1 = f :=
  (Classical.choose_spec (D.existsUnique_desc M f hf hm hk)).1.1

theorem desc_mul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x y : SchemeHomOver t D.structureMap) :
    pointMap (D.desc M f hf hm hk).1 (D.desc M f hf hm hk).2 (D.quotientLaw.mul t x y) =
      M.mul t (pointMap (D.desc M f hf hm hk).1 (D.desc M f hf hm hk).2 x)
        (pointMap (D.desc M f hf hm hk).1 (D.desc M f hf hm hk).2 y) :=
  (Classical.choose_spec (D.existsUnique_desc M f hf hm hk)).1.2 t x y

/-- The actual Frobenius factor from the actual quotient. -/
def frobeniusFactor : SchemeHomOver D.structureMap (SchemeFrobenius.toBase p (base p A)) :=
  D.desc (twistLaw p (base p A) (law p A)) (F p A) (relative_toBase p (base p A))
    (relative_mul p (base p A) (law p A)) (inclusion_frobenius p A)

theorem quotientMap_frobeniusFactor : D.quotientMap ≫ D.frobeniusFactor.1 = F p A :=
  D.quotientMap_desc _ _ _ (relative_mul p (base p A) (law p A)) (inclusion_frobenius p A)

theorem frobeniusFactor_mul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x y : SchemeHomOver t D.structureMap) :
    pointMap D.frobeniusFactor.1 D.frobeniusFactor.2 (D.quotientLaw.mul t x y) =
      (twistLaw p (base p A) (law p A)).mul t
        (pointMap D.frobeniusFactor.1 D.frobeniusFactor.2 x)
        (pointMap D.frobeniusFactor.1 D.frobeniusFactor.2 y) :=
  D.desc_mul _ _ _ (relative_mul p (base p A) (law p A)) (inclusion_frobenius p A) t x y

/-- The actual Verschiebung factor from the actual quotient. -/
def verschiebungFactor : SchemeHomOver D.structureMap A.group.X.hom :=
  D.desc (GroupScheme.law A.group) (V p A)
    (verschiebung_over p A.group.X.hom (GroupScheme.law A.group) A.groupScheme_law_commutative)
    (verschiebung_mul p A.group.X.hom (GroupScheme.law A.group) A.groupScheme_law_commutative)
    (inclusion_verschiebung p A)

theorem quotientMap_verschiebungFactor : D.quotientMap ≫ D.verschiebungFactor.1 = V p A :=
  D.quotientMap_desc _ _ _
    (verschiebung_mul p A.group.X.hom (GroupScheme.law A.group) A.groupScheme_law_commutative)
    (inclusion_verschiebung p A)

theorem verschiebungFactor_mul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x y : SchemeHomOver t D.structureMap) :
    pointMap D.verschiebungFactor.1 D.verschiebungFactor.2 (D.quotientLaw.mul t x y) =
      (GroupScheme.law A.group).mul t
        (pointMap D.verschiebungFactor.1 D.verschiebungFactor.2 x)
        (pointMap D.verschiebungFactor.1 D.verschiebungFactor.2 y) :=
  D.desc_mul _ _ _
    (verschiebung_mul p A.group.X.hom (GroupScheme.law A.group) A.groupScheme_law_commutative)
    (inclusion_verschiebung p A) t x y

end SupersingularCurves.Geometry.FrobeniusVerschiebungSubgroup.QuotientData
