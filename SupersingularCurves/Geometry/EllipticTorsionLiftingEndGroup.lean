/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.EllipticTorsionLiftingEndRealization
import SupersingularCurves.Geometry.ClassificationSurfaceEllipticExistence
import SupersingularCurves.Geometry.FrobeniusFactorGroup

/-! # The rational endomorphism lattice inside actual elliptic group schemes -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SupersingularCurves.Geometry.WeierstrassGroupModel
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open FrobeniusFactorGroup WeierstrassProjModel

variable {K : Type} [Field K] [IsAlgClosed K] [DecidableEq K]
variable {W : WeierstrassCurve K} [W.IsElliptic]
variable (D : WeierstrassGroupModel W)

private theorem actual_mul {T : Scheme} (t : T ⟶ Spec (CommRingCat.of K))
    (x y : SchemeHomOver t (projModelStrCR W.toProjective)) :
    (GroupScheme.law D.abelianVariety.group).mul t x y = D.weierstrassLaw.mul t x y := by
  exact (relativeGroupLawOfGrpObj_grpObjOverMk_mul D.law t x y).trans (D.law_mul t x y)

/-- Bundle a genuinely multiplication-preserving map as an internal group
scheme morphism. Unit preservation follows on every test scheme. -/
def groupEndOfMul (φ : SchemeHomOver (projModelStrCR W.toProjective)
    (projModelStrCR W.toProjective))
    (hφ : ∀ {T : Scheme} (t : T ⟶ Spec (CommRingCat.of K))
      (x y : SchemeHomOver t (projModelStrCR W.toProjective)),
      NeronModelInfra.schemeHomOverComp (D.weierstrassLaw.mul t x y) φ =
        D.weierstrassLaw.mul t (NeronModelInfra.schemeHomOverComp x φ)
          (NeronModelInfra.schemeHomOverComp y φ)) :
    D.abelianVariety.group ⟶ D.abelianVariety.group := by
  have hmul : ∀ {T : Scheme} (t : T ⟶ Spec (CommRingCat.of K))
      (x y : SchemeHomOver t D.abelianVariety.group.X.hom),
      pointMap φ.1 φ.2 ((GroupScheme.law D.abelianVariety.group).mul t x y) =
        (GroupScheme.law D.abelianVariety.group).mul t (pointMap φ.1 φ.2 x)
          (pointMap φ.1 φ.2 y) := by
    intro T t x y
    simpa only [actual_mul, pointMap, NeronModelInfra.schemeHomOverComp] using hφ t x y
  have hone : ∀ {T : Scheme} (t : T ⟶ Spec (CommRingCat.of K)),
      pointMap φ.1 φ.2 ((GroupScheme.law D.abelianVariety.group).one t) =
        (GroupScheme.law D.abelianVariety.group).one t := by
    intro T t
    let L := GroupScheme.law D.abelianVariety.group
    letI : Group (SchemeHomOver t (projModelStrCR W.toProjective)) := L.pointGroup t
    have h := hmul t (L.one t) (L.one t)
    rw [L.one_mul] at h
    have hh : pointMap φ.1 φ.2 (L.one t) * pointMap φ.1 φ.2 (L.one t) =
        pointMap φ.1 φ.2 (L.one t) := by
      change L.mul t _ _ = _
      exact h.symm
    exact mul_eq_left.mp hh
  letI : IsMonHom (Over.homMk φ.1 φ.2 :
      D.abelianVariety.group.X ⟶ D.abelianVariety.group.X) :=
    GroupScheme.isMonHom_of_pointMap (G := D.abelianVariety.group)
      (H := D.abelianVariety.group) φ.1 φ.2 hone hmul
  exact Grp.homMk (Over.homMk φ.1 φ.2)

@[simp] theorem groupEndOfMul_left (φ : SchemeHomOver (projModelStrCR W.toProjective)
    (projModelStrCR W.toProjective)) (hφ) :
    (D.groupEndOfMul φ hφ).hom.hom.left = φ.1 := rfl

/-- All four independent rational endomorphism directions are realized as
actual group scheme endomorphisms, without a supplied realization. -/
theorem exists_faithful_rankFour_group_lattice
    (p : ℕ) [Fact p.Prime] [CharP K p] [Algebra (ZMod p) K]
    [Algebra.IsAlgebraic (ZMod p) K]
    (hss : ∀ P : W.toAffine.Point, p • P = 0 → P = 0) :
    ∃ Φ : (Fin 4 → ℤ) → (D.abelianVariety.group ⟶ D.abelianVariety.group),
      Function.Injective Φ ∧
      ((Φ 0).hom.hom.left = (D.weierstrassLaw.one (projModelStrCR W.toProjective)).1) ∧
      (∀ a b, (Φ (a + b)).hom.hom.left =
        (D.weierstrassLaw.mul (projModelStrCR W.toProjective)
          ⟨(Φ a).hom.hom.left, (Φ a).hom.hom.w⟩
          ⟨(Φ b).hom.hom.left, (Φ b).hom.hom.w⟩).1) := by
  obtain ⟨Ψ, hinj, hgroup, hzero, hadd, -⟩ :=
    EllipticTorsionLiftingEndRealization.exists_rankFour_scheme_lattice
      W D.weierstrassLaw (D.eval K) (D.isPointsEval.1 K) (D.eval_chart K) p hss
  let Φ := fun a => D.groupEndOfMul (Ψ a) (hgroup a)
  refine ⟨Φ, ?_, ?_, ?_⟩
  · intro a b h
    apply hinj
    apply Subtype.ext
    exact congrArg (fun f => f.hom.hom.left) h
  · exact congrArg Subtype.val hzero
  · intro a b
    exact congrArg Subtype.val (hadd a b)

end SupersingularCurves.Geometry.WeierstrassGroupModel
