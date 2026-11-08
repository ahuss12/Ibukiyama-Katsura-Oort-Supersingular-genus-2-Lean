/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.JacobianConstruction
import SupersingularCurves.Geometry.SuperspecialTorsion

/-!
# The point group of any representing Jacobian

The Picard point correspondence is derived for every representing Jacobian,
including every choice of base point. Consequently p-rank is independent of
these choices. This is enough to apply the superspecial obstruction to the
existential curve predicate, without assuming uniqueness of the group scheme.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

namespace SupersingularCurves.Geometry
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open AlgebraicCurve NeronModelInfra GoodReductionJacobian
open scoped CategoryTheory.MonObj

variable {K : Type u} [Field K] [IsAlgClosed K]
  {F : Type v} [Field F] [Algebra K F] [IsCurveOver K F]
  {M : AlgebraicCurve.CurveModel K F}

namespace Jacobian
variable {s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase}

/-- The correspondence follows from Picard representability, for any Jacobian. -/
theorem picardPoints_nonempty (J : Jacobian M s) :
    Nonempty (Pic0 K F ≃+ Additive J.abelianVariety.Points) := by
  have : GeometricallyIntegral M.toBase := geometricallyIntegral_of_isAlgClosed M.toBase
  have : Algebra.EssFiniteType K F :=
    P2MW.S_AlgebraicCurve_CurveModel_exists_representsRelSubPic_abelJacobi_of_isAlgClosed.P2mJacK.essFiniteType_of_curveModel M
  let : GrpObj (Over.mk J.designation.toBase) :=
    J.represents.grpObj (P := algEquivZeroGroupCut M.toBase s)
  obtain ⟨pts, hadd, _, _⟩ :=
    AlgebraicGeometry.RelPicard.exists_pic0_equiv_points_abelJacobi_of_curveModel
      K M.toBase s J.designation J.represents M (Iso.refl M.C) (by simp)
      s (by simp)
  exact ⟨{ toEquiv := pts.trans Additive.ofMul
           map_add' := hadd }⟩

/-- Choose the equivalence only after proving that it exists. -/
def picardPoints (J : Jacobian M s) : Pic0 K F ≃+ Additive J.abelianVariety.Points :=
  Classical.choice J.picardPoints_nonempty

/-- Torsion cardinality depends on the curve, not on the chosen representation. -/
theorem card_torsionPoints_eq (J : Jacobian M s)
    {s' : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase}
    (J' : Jacobian M s') (n : ℕ) :
    Nat.card (J.abelianVariety.torsionPoints n) =
      Nat.card (J'.abelianVariety.torsionPoints n) :=
  (card_torsionPoints_eq_picard _ J.picardPoints n).trans
    (card_torsionPoints_eq_picard _ J'.picardPoints n).symm

/-- In particular geometric p-rank is independent of the base point. -/
theorem hasPRankOver_iff (J : Jacobian M s)
    {s' : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase}
    (J' : Jacobian M s') (p : ℕ) [Fact p.Prime] [CharP K p] (f : ℕ) :
    J.abelianVariety.HasPRankOver p f ↔ J'.abelianVariety.HasPRankOver p f := by
  have hc := J.card_torsionPoints_eq J' p
  have hn : p ^ f ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  constructor
  · rintro ⟨_, h⟩
    have h' := hc.symm.trans h
    exact ⟨Nat.finite_of_card_ne_zero (h' ▸ hn), h'⟩
  · rintro ⟨_, h⟩
    have h' := hc.trans h
    exact ⟨Nat.finite_of_card_ne_zero (h' ▸ hn), h'⟩

end Jacobian

/-- If the curve is geometrically superspecial, every representing Jacobian
has p-rank zero. No choice of base point can evade the obstruction. -/
theorem CurveModel.IsSuperspecial.hasPRankOver_zero
    {p : ℕ} [Fact p.Prime] [CharP K p]
    (h : CurveModel.IsSuperspecial p M)
    {s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase}
    (J : Jacobian M s) : J.abelianVariety.HasPRankOver p 0 := by
  obtain ⟨s', J', hJ'⟩ := h
  exact (J'.hasPRankOver_iff J p 0).mp
    (AbelianVariety.IsSuperspecial.hasPRankOver_zero hJ')

end SupersingularCurves.Geometry
