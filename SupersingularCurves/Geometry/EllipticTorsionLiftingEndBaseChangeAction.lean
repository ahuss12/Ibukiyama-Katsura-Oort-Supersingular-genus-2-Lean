/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.EllipticTorsionLiftingEndBaseChange
import SupersingularCurves.Geometry.EllipticTorsionLiftingEndGroup
import SupersingularCurves.Geometry.PointedCotangentGroupAddElliptic

/-! # Differentiate the genuine endomorphism action after field extension

The source rational endomorphism ring acts by actual pulled-back group maps.
The scalar ring action is differentiated on the target field directly.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace SupersingularCurves.Geometry.WeierstrassGroupModel
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open PointedCotangent WeierstrassProjModel EllipticTorsionLiftingEndRealization
open scoped CategoryTheory.MonObj

variable {k : Type} [Field k] [IsAlgClosed k] [DecidableEq k]
variable {W : WeierstrassCurve k} [W.IsElliptic] (D : WeierstrassGroupModel W)
variable (K : Type) [Field K] [Algebra k K]

/-- Construct a scalar ring action by differentiating the genuine pullbacks
of the rational source endomorphisms. No differential base-change comparison
is assumed or needed. -/
theorem exists_baseChanged_cotangentScalarRingHom :
    ∃ Φ : RationalEnd W →
        ((D.abelianVariety.baseChange K).group ⟶ (D.abelianVariety.baseChange K).group),
      ∃ hpoint : ∀ a,
          ((GroupScheme.law (D.abelianVariety.baseChange K).group).one (𝟙 _)).1 ≫
            (Φ a).hom.hom.left =
          ((GroupScheme.law (D.abelianVariety.baseChange K).group).one (𝟙 _)).1,
        ∃ ρ : RationalEnd W →+* K,
          Function.Injective Φ ∧
          (∀ a, differential (D.abelianVariety.baseChange K).group.X.hom
            ((GroupScheme.law (D.abelianVariety.baseChange K).group).one (𝟙 _))
            (Φ a).hom.hom.left (Φ a).hom.hom.w (hpoint a) = ρ a • LinearMap.id) := by
  obtain ⟨Ψ, hinj, -, hgroup, hzero, hone, hadd, hmul, -⟩ :=
    exists_faithful_action W D.weierstrassLaw (D.eval k) (D.isPointsEval.1 k) (D.eval_chart k)
  let α := fun a => D.groupEndOfMul (Ψ a) (hgroup a)
  have hαinj : Function.Injective α := by
    intro a b h
    apply hinj
    exact Subtype.ext (congrArg (fun f => f.hom.hom.left) h)
  have hαzero : (α 0).hom.hom = (1 : D.abelianVariety.group.X ⟶ D.abelianVariety.group.X) := by
    apply overHomToSchemeHomOver_injective
    change Ψ 0 = (GroupScheme.law D.abelianVariety.group).one (modelBase W)
    exact hzero.trans ((relativeGroupLawOfGrpObj_grpObjOverMk_one D.law (modelBase W)).trans
      (D.law_one_eq_weierstrass (modelBase W))).symm
  have hαone : (α 1).hom.hom = 𝟙 D.abelianVariety.group.X := by
    apply Over.OverMorphism.ext
    exact congrArg Subtype.val hone
  have hαadd : ∀ a b, (α (a + b)).hom.hom = (α a).hom.hom * (α b).hom.hom := by
    intro a b
    apply overHomToSchemeHomOver_injective
    change Ψ (a + b) = (GroupScheme.law D.abelianVariety.group).mul (modelBase W) (Ψ a) (Ψ b)
    exact (hadd a b).trans ((relativeGroupLawOfGrpObj_grpObjOverMk_mul D.law
      (modelBase W) (Ψ a) (Ψ b)).trans (D.law_mul (modelBase W) (Ψ a) (Ψ b))).symm
  have hαmul : ∀ a b, (α (a * b)).hom.hom = (α b).hom.hom ≫ (α a).hom.hom := by
    intro a b
    apply Over.OverMorphism.ext
    exact congrArg Subtype.val (hmul a b)
  let Φ := fun a => D.abelianVariety.endBaseChange K (α a)
  let G := (D.abelianVariety.baseChange K).group
  let L := GroupScheme.law G
  let ψ : RationalEnd W → SchemeHomOver G.X.hom G.X.hom :=
    fun a => overHomToSchemeHomOver (Φ a).hom.hom
  let F := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  have hΦ : ∀ a, (Φ a).hom.hom = F.map (α a).hom.hom := fun _ => rfl
  have hψzero : ψ 0 = L.one G.X.hom := by
    change overHomToSchemeHomOver (F.map (α 0).hom.hom) = overHomToSchemeHomOver (1 : G.X ⟶ G.X)
    rw [hαzero, Functor.map_one]
  have hψone : ψ 1 = NeronModelInfra.schemeHomOverId G.X.hom := by
    apply Subtype.ext
    change (F.map (α 1).hom.hom).left = 𝟙 G.X.left
    rw [hαone, F.map_id]
    rfl
  have hψadd : ∀ a b, ψ (a + b) = L.mul G.X.hom (ψ a) (ψ b) := by
    intro a b
    change overHomToSchemeHomOver (F.map (α (a + b)).hom.hom) =
      overHomToSchemeHomOver
        (schemeHomOverToOverHom (ψ a) * schemeHomOverToOverHom (ψ b))
    simp only [ψ, schemeHomOverToOverHom_overHomToSchemeHomOver, hΦ, hαadd,
      Functor.map_mul]
  have hψmul : ∀ a b, ψ (a * b) = NeronModelInfra.schemeHomOverComp (ψ b) (ψ a) := by
    intro a b
    apply Subtype.ext
    change (F.map (α (a * b)).hom.hom).left =
      (F.map (α b).hom.hom).left ≫ (F.map (α a).hom.hom).left
    rw [hαmul, F.map_comp]
    rfl
  have hpoint : ∀ a, (L.one (𝟙 _)).1 ≫ (ψ a).1 = (L.one (𝟙 _)).1 := by
    intro a
    exact congrArg (fun q : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X => q.left)
      ((IsMonHom.monoidHom (Φ a).hom.hom (Over.mk (𝟙 _))).map_one)
  letI : SmoothOfRelativeDimension 1 G.X.hom := (D.abelianVariety.baseChange K).smooth
  have hdim : Module.finrank K (Cotangent G.X.hom (L.one (𝟙 _))) = 1 :=
    finrank_eq_relativeDimension G.X.hom (L.one (𝟙 _)) 1
  let ρ := cotangentScalarRingHom L ψ hpoint hdim hψzero hψone hψadd hψmul
  refine ⟨Φ, hpoint, ρ, (D.abelianVariety.endBaseChange_injective K).comp hαinj, ?_⟩
  intro a
  exact cotangentScalarRingHom_action L ψ hpoint hdim hψzero hψone hψadd hψmul a

end SupersingularCurves.Geometry.WeierstrassGroupModel
