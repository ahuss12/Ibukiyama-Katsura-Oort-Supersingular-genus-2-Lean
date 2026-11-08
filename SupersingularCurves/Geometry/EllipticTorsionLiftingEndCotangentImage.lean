/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.EllipticTorsionLiftingEndScalarImage
import SupersingularCurves.Geometry.EllipticTorsionLiftingEndGroup
import SupersingularCurves.Geometry.PointedCotangentGroupAddElliptic
import SupersingularCurves.Geometry.EllipticTorsionLiftingEndBaseChangeAction

/-! # Actual global endomorphisms realize every Fp² cotangent scalar -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SupersingularCurves.Geometry.WeierstrassGroupModel
open CategoryTheory AlgebraicGeometry NeronModelInfra
open PointedCotangent WeierstrassProjModel EllipticTorsionLiftingEndRealization

variable {K : Type} [Field K] [IsAlgClosed K] [DecidableEq K]
variable {W : WeierstrassCurve K} [W.IsElliptic] (D : WeierstrassGroupModel W)

/-- Every p²-Frobenius-fixed scalar is the genuine cotangent action of an
actual global elliptic group endomorphism. The scalar action is constructed by
differentiation, and its image is proved from the ramified quaternion order. -/
theorem exists_endomorphism_of_frobenius_scalar
    (p : ℕ) [Fact p.Prime] [CharP K p] [Algebra (ZMod p) K]
    [Algebra.IsAlgebraic (ZMod p) K]
    (hss : ∀ P : W.toAffine.Point, p • P = 0 → P = 0)
    (c : K) (hc : c ^ (p ^ 2) = c) :
    ∃ f : D.abelianVariety.group ⟶ D.abelianVariety.group,
      ∃ hs : (D.law.one (𝟙 _)).1 ≫ f.hom.hom.left = (D.law.one (𝟙 _)).1,
        differential (modelBase W) (D.law.one (𝟙 _))
          f.hom.hom.left f.hom.hom.w hs = c • LinearMap.id := by
  obtain ⟨Φ, hpoint, ρ, -, -, hgroup, hdifferential⟩ := D.exists_actual_cotangentScalarRingHom
  have hrange : c ∈ Set.range ρ := by
    rw [EllipticTorsionLiftingEndScalarImage.rationalEnd_range_eq_frobenius_fixed W hss ρ]
    exact hc
  obtain ⟨a, ha⟩ := hrange
  have hmul : ∀ {T : Scheme} (t : T ⟶ Spec (CommRingCat.of K))
      (x y : SchemeHomOver t (modelBase W)),
      NeronModelInfra.schemeHomOverComp (D.weierstrassLaw.mul t x y) (Φ a) =
        D.weierstrassLaw.mul t (NeronModelInfra.schemeHomOverComp x (Φ a))
          (NeronModelInfra.schemeHomOverComp y (Φ a)) := by
    intro T t x y
    simpa only [D.law_mul] using hgroup a t x y
  refine ⟨D.groupEndOfMul (Φ a) hmul, hpoint a, ?_⟩
  change differential (modelBase W) (D.law.one (𝟙 _))
    (Φ a).1 (Φ a).2 (hpoint a) = c • LinearMap.id
  simpa only [ha] using hdifferential a

/-- The same full Fp² scalar image after an arbitrary field extension of the
algebraic source field. The target derivative is constructed directly from
the genuine pulled-back ring action. -/
theorem exists_baseChanged_endomorphism_of_frobenius_scalar
    (L : Type) [Field L] [Algebra K L]
    (p : ℕ) [Fact p.Prime] [CharP K p] [Algebra (ZMod p) K]
    [Algebra.IsAlgebraic (ZMod p) K] [CharP L p] [Algebra (ZMod p) L]
    (hss : ∀ P : W.toAffine.Point, p • P = 0 → P = 0)
    (c : L) (hc : c ^ (p ^ 2) = c) :
    ∃ f : (D.abelianVariety.baseChange L).group ⟶ (D.abelianVariety.baseChange L).group,
      ∃ hs : ((GroupScheme.law (D.abelianVariety.baseChange L).group).one (𝟙 _)).1 ≫
          f.hom.hom.left = ((GroupScheme.law (D.abelianVariety.baseChange L).group).one (𝟙 _)).1,
        differential (D.abelianVariety.baseChange L).group.X.hom
          ((GroupScheme.law (D.abelianVariety.baseChange L).group).one (𝟙 _))
          f.hom.hom.left f.hom.hom.w hs = c • LinearMap.id := by
  obtain ⟨Φ, hpoint, ρ, -, hdifferential⟩ := D.exists_baseChanged_cotangentScalarRingHom L
  have hrange : c ∈ Set.range ρ := by
    rw [EllipticTorsionLiftingEndScalarImage.rationalEnd_range_eq_frobenius_fixed W hss ρ]
    exact hc
  obtain ⟨a, ha⟩ := hrange
  exact ⟨Φ a, hpoint a, by simpa only [ha] using hdifferential a⟩

end SupersingularCurves.Geometry.WeierstrassGroupModel
