/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusFiniteFieldGroupDescent
import SupersingularCurves.Geometry.FrobeniusFactorGroup
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_mul_comp_eq_mul_comp_of_one_comp_eq_one

/-!
# The actual group-scheme isomorphism to the finite-field model

The faithfully-flat pullback comparison preserving zero gives an isomorphism
of actual group schemes. Abelian rigidity proves compatibility with multiplication,
and the final model theorem retains its scalar Frobenius identity.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SupersingularCurves.Geometry
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open GoodReductionJacobian NeronModelInfra FrobeniusFactorGroup
open scoped CategoryTheory.MonObj

namespace GroupScheme
variable {K : Type u} [Field K]

theorem zero_coe_eq_unit (G : GroupScheme K) :
    (GroupScheme.zero G).1 = (η[G.X]).left := by
  change (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X).left = _
  change ((CategoryTheory.CartesianMonoidalCategory.toUnit _ ≫ η[G.X]) : _ ⟶ _).left = _
  simp only [Over.comp_left, Over.toUnit_left, Over.mk_hom]
  exact Category.id_comp _
end GroupScheme

namespace AbelianVariety
variable {k K : Type u} [Field k] [Field K] [Algebra k K] {g : ℕ}
local instance (A : AbelianVariety K g) : Smooth A.group.X.hom :=
  SmoothOfRelativeDimension.smooth g A.group.X.hom

theorem baseChange_zero_fst (B : AbelianVariety k g) :
    (GroupScheme.zero (B.baseChange K).group).1 ≫
      pullback.fst B.group.X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
      Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ (GroupScheme.zero B.group).1 := by
  rw [GroupScheme.zero_coe_eq_unit, GroupScheme.zero_coe_eq_unit]
  change ((CategoryTheory.Functor.LaxMonoidal.ε (Over.pullback _)) ≫
    (Over.pullback _).map (η[B.group.X])).left ≫ _ = _
  simp only [Over.comp_left, Over.ε_pullback_left, Over.pullback_map_left,
    Category.assoc, pullback.lift_fst]
  rw [← Category.assoc]
  have h : pullback.fst (𝟙 (Spec (CommRingCat.of k)))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) =
      pullback.snd (𝟙 (Spec (CommRingCat.of k)))
        (Spec.map (CommRingCat.ofHom (algebraMap k K))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
    simpa only [Category.comp_id] using (pullback.condition
      (f := 𝟙 (Spec (CommRingCat.of k)))
      (g := Spec.map (CommRingCat.ofHom (algebraMap k K))))
  simp only [Over.tensorUnit_hom]
  rw [h, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

/-- A pullback model whose identity descends recovers the actual group object. -/
def groupIsoOfPullbackOfOne (A : AbelianVariety K g) (B : AbelianVariety k g)
    (d : A.group.X.left ⟶ B.group.X.left)
    (hd : IsPullback d A.group.X.hom B.group.X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (hone : (GroupScheme.zero A.group).1 ≫ d =
      Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ (GroupScheme.zero B.group).1) :
    A.group ≅ (B.baseChange K).group := by
  let e : A.group.X ≅ (B.baseChange K).group.X :=
    Over.isoMk hd.isoPullback hd.isoPullback_hom_snd
  have he : e.hom.left ≫ (B.baseChange K).group.X.hom = A.group.X.hom := e.hom.w
  have hzero : (GroupScheme.zero A.group).1 ≫ e.hom.left =
      (GroupScheme.zero (B.baseChange K).group).1 := by
    apply pullback.hom_ext
    · change ((GroupScheme.zero A.group).1 ≫ hd.isoPullback.hom) ≫ _ = _
      rw [Category.assoc, hd.isoPullback_hom_fst, hone, B.baseChange_zero_fst (K := K)]
    · change ((GroupScheme.zero A.group).1 ≫ hd.isoPullback.hom) ≫ _ = _
      rw [Category.assoc, hd.isoPullback_hom_snd, (GroupScheme.zero A.group).2]
      exact (GroupScheme.zero (B.baseChange K).group).2.symm
  let : IsMonHom e.hom := by
    apply GroupScheme.isMonHom_of_pointMap e.hom.left he
    · intro T t
      apply Subtype.ext
      have h₁ := congrArg Subtype.val ((GroupScheme.law A.group).one_natural (𝟙 _) t t
        (Category.comp_id t))
      have h₂ := congrArg Subtype.val ((GroupScheme.law (B.baseChange K).group).one_natural
        (𝟙 _) t t (Category.comp_id t))
      change t ≫ (GroupScheme.zero A.group).1 = _ at h₁
      change t ≫ (GroupScheme.zero (B.baseChange K).group).1 = _ at h₂
      change ((GroupScheme.law A.group).one t).1 ≫ e.hom.left = _
      rw [← h₁, Category.assoc, hzero, h₂]
    · intro T t x y
      exact Subtype.ext (A.abelianSchemePropertyBundle.mul_comp_eq_mul_comp_of_one_comp_eq_one
        (GroupScheme.law A.group) (GroupScheme.law (B.baseChange K).group) e.hom.left he hzero t x y)
  exact Grp.mkIso' e

/-- The category-level isomorphism retains the original descent projection. -/
theorem groupIsoOfPullbackOfOne_hom_fst (A : AbelianVariety K g) (B : AbelianVariety k g)
    (d : A.group.X.left ⟶ B.group.X.left)
    (hd : IsPullback d A.group.X.hom B.group.X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (hone : (GroupScheme.zero A.group).1 ≫ d =
      Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ (GroupScheme.zero B.group).1) :
    underlyingScheme.map (groupIsoOfPullbackOfOne A B d hd hone).hom ≫
      pullback.fst B.group.X.hom (Spec.map (CommRingCat.ofHom (algebraMap k K))) = d := by
  change hd.isoPullback.hom ≫ _ = d
  exact hd.isoPullback_hom_fst

variable [IsAlgClosed K] (A : AbelianVariety K g)
local instance : Smooth A.group.X.hom := SmoothOfRelativeDimension.smooth g A.group.X.hom

/-- The genuine finite-field abelian model recovers the original abelian
variety by an isomorphism in the category of group schemes. -/
theorem exists_finiteField_abelian_iso_model_of_verschiebungCotangent_eq_zero
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (hV : GroupScheme.verschiebungCotangent p A.group A.groupScheme_law_commutative = 0) :
    Finite (FrobeniusDescent.fixedField K p 2) ∧
      Nat.card (FrobeniusDescent.fixedField K p 2) = p ^ 2 ∧
      ∃ A₀ : AbelianVariety (FrobeniusDescent.fixedField K p 2) g,
        Nonempty (A.group ≅ (A₀.baseChange K).group) ∧
        SchemeFrobenius.absolute p A₀.group.X.hom ≫
          SchemeFrobenius.absolute p A₀.group.X.hom =
            (GroupScheme.law A₀.group).schemeNsmul p := by
  obtain ⟨hfin, hcard, A₀, d, hd, hone, _, hF⟩ :=
    A.exists_finiteField_abelian_model_of_verschiebungCotangent_eq_zero p hV
  exact ⟨hfin, hcard, A₀, ⟨groupIsoOfPullbackOfOne A A₀ d hd hone⟩, hF⟩

end AbelianVariety
end SupersingularCurves.Geometry
