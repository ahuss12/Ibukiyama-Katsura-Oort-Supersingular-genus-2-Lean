/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.PointedCotangentGroupAddRing
import SupersingularCurves.Geometry.EllipticTorsionLiftingEndRealization
import SupersingularCurves.Geometry.ClassificationSurfaceEllipticExistence

/-! # The actual rational elliptic endomorphism ring acts on cotangent scalars -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SupersingularCurves.Geometry.WeierstrassGroupModel
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open PointedCotangent WeierstrassProjModel EllipticTorsionLiftingEndRealization

variable {K : Type} [Field K] [IsAlgClosed K] [DecidableEq K]
variable {W : WeierstrassCurve K} [W.IsElliptic] (D : WeierstrassGroupModel W)

/-- The two genuine law presentations have the same identity on every test scheme. -/
theorem law_one_eq_weierstrass {T : Scheme} (t : T ⟶ Spec (CommRingCat.of K)) :
    D.law.one t = D.weierstrassLaw.one t := by
  have H := D.law_mul t (D.law.one t) (D.weierstrassLaw.one t)
  rw [D.law.one_mul, D.weierstrassLaw.mul_one] at H
  exact H.symm

/-- Construct the scalar ring homomorphism by differentiating the genuine
scheme endomorphisms realizing the actual rational endomorphism ring. -/
theorem exists_actual_cotangentScalarRingHom :
    ∃ Φ : RationalEnd W → SchemeHomOver (modelBase W) (modelBase W),
      ∃ hpoint : ∀ a, (D.law.one (𝟙 _)).1 ≫ (Φ a).1 = (D.law.one (𝟙 _)).1,
        ∃ ρ : RationalEnd W →+* K,
          Function.Injective Φ ∧
          (∀ a P, D.eval K (NeronModelInfra.schemeHomOverComp P (Φ a)) =
            (a : AddMonoid.End (W.baseChange K).toAffine.Point) (D.eval K P)) ∧
          (∀ a {T : Scheme} (t : T ⟶ Spec (CommRingCat.of K))
            (x y : SchemeHomOver t (modelBase W)),
            NeronModelInfra.schemeHomOverComp (D.law.mul t x y) (Φ a) =
              D.law.mul t (NeronModelInfra.schemeHomOverComp x (Φ a))
                (NeronModelInfra.schemeHomOverComp y (Φ a))) ∧
          (∀ a, differential (modelBase W) (D.law.one (𝟙 _))
            (Φ a).1 (Φ a).2 (hpoint a) = ρ a • LinearMap.id) := by
  obtain ⟨Φ, hinj, heval, hgroup, hzero, hone, hadd, hmul, -⟩ :=
    exists_faithful_action W D.weierstrassLaw (D.eval K) (D.isPointsEval.1 K) (D.eval_chart K)
  have hgroup' : ∀ a {T : Scheme} (t : T ⟶ Spec (CommRingCat.of K))
      (x y : SchemeHomOver t (modelBase W)),
      NeronModelInfra.schemeHomOverComp (D.law.mul t x y) (Φ a) =
        D.law.mul t (NeronModelInfra.schemeHomOverComp x (Φ a))
          (NeronModelInfra.schemeHomOverComp y (Φ a)) := by
    intro a T t x y
    simpa only [D.law_mul] using hgroup a t x y
  let hpoint := fun a => end_point_of_mul D.law (Φ a) (hgroup' a)
  have hzero' : Φ 0 = D.law.one (modelBase W) :=
    hzero.trans (D.law_one_eq_weierstrass (modelBase W)).symm
  have hadd' : ∀ a b, Φ (a + b) = D.law.mul (modelBase W) (Φ a) (Φ b) := by
    intro a b
    exact (hadd a b).trans (D.law_mul (modelBase W) (Φ a) (Φ b)).symm
  letI : SmoothOfRelativeDimension 1 (modelBase W) := D.abelianVariety.smooth
  have hdim := finrank_eq_relativeDimension (modelBase W) (D.law.one (𝟙 _)) 1
  refine ⟨Φ, hpoint, cotangentScalarRingHom D.law Φ hpoint hdim hzero' hone hadd' hmul,
    hinj, heval, hgroup', ?_⟩
  intro a
  exact cotangentScalarRingHom_action D.law Φ hpoint hdim hzero' hone hadd' hmul a

end SupersingularCurves.Geometry.WeierstrassGroupModel
