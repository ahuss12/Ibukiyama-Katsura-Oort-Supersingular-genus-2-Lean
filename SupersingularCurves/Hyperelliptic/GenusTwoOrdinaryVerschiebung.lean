/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Hyperelliptic.GenusTwoOrdinary
import SupersingularCurves.IKO.SemilinearInvertibility
import SupersingularCurves.Geometry.CartierVerschiebungRank
import SupersingularCurves.Geometry.GlobalCartierModels

/-!
# General genus-two ordinarity and the actual Verschiebung differential

The determinant criterion is transported through the full global differential
basis and the independently proved Cartier/Verschiebung comparison. Thus an
actual representing Jacobian is ordinary precisely when Cartier, or its actual
Verschiebung cotangent map, is bijective. All Frobenius twists are retained.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SupersingularCurves.Hyperelliptic.SimpleRootModel
open CategoryTheory AlgebraicGeometry AlgebraicCurve KaehlerDifferential
open NeronModelInfra SupersingularCurves.Geometry SupersingularCurves.IKO

variable {K : Type*} [Field K] [IsAlgClosed K] [NeZero (2 : K)]
  (a : SimpleRootModel K) (p : ℕ) [Fact p.Prime] [CharP K p]
  (hf : a.f.Separable) (hd : a.f.natDegree = 5 ∨ a.f.natDegree = 6)
  (hp : p % 2 = 1)

include hf hd hp

theorem globalCartier_injective_iff_det_ne_zero :
    Function.Injective (a.globalCartier p) ↔ (coefficientMatrix p a.f).det ≠ 0 := by
  have h : Function.Injective (a.globalCartier p) ↔
      Function.Injective (semilinearAction (frobeniusEquiv K p)
        (coefficientMatrix p a.f)) := by
    constructor
    · intro hg v w hvw
      apply (a.globalEquiv hf hd).injective
      apply hg
      apply (a.globalEquiv hf hd).symm.injective
      simpa only [a.globalCartier_coordinates hf hd p hp,
        LinearEquiv.symm_apply_apply] using hvw
    · intro hs ω η hωη
      apply (a.globalEquiv hf hd).symm.injective
      apply hs
      rw [← a.globalCartier_coordinates hf hd p hp ω,
        ← a.globalCartier_coordinates hf hd p hp η, hωη]
  exact h.trans (semilinearAction_injective_iff _ _)

theorem globalCartier_surjective_iff_det_ne_zero :
    Function.Surjective (a.globalCartier p) ↔ (coefficientMatrix p a.f).det ≠ 0 := by
  have h : Function.Surjective (a.globalCartier p) ↔
      Function.Surjective (semilinearAction (frobeniusEquiv K p)
        (coefficientMatrix p a.f)) := by
    constructor
    · intro hg v
      obtain ⟨ω, hω⟩ := hg (a.globalEquiv hf hd v)
      refine ⟨(a.globalEquiv hf hd).symm ω, ?_⟩
      rw [← a.globalCartier_coordinates hf hd p hp ω, hω,
        LinearEquiv.symm_apply_apply]
    · intro hs ω
      obtain ⟨v, hv⟩ := hs ((a.globalEquiv hf hd).symm ω)
      refine ⟨a.globalEquiv hf hd v, ?_⟩
      apply (a.globalEquiv hf hd).symm.injective
      rw [a.globalCartier_coordinates hf hd p hp,
        LinearEquiv.symm_apply_apply, hv]
  exact h.trans (semilinearAction_surjective_iff _ _)

theorem globalCartier_bijective_iff_det_ne_zero :
    Function.Bijective (a.globalCartier p) ↔ (coefficientMatrix p a.f).det ≠ 0 := by
  change (Function.Injective _ ∧ Function.Surjective _) ↔ _
  rw [a.globalCartier_injective_iff_det_ne_zero p hf hd hp,
    a.globalCartier_surjective_iff_det_ne_zero p hf hd hp, and_self]

variable {s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) a.curveModel.toBase}
  (J : Jacobian a.curveModel s)

theorem jacobian_isOrdinaryOver_iff_globalCartier_injective :
    J.abelianVariety.IsOrdinaryOver p ↔ Function.Injective (a.globalCartier p) :=
  (a.jacobian_isOrdinaryOver_iff_det_ne_zero p hf hd hp J).trans
    (a.globalCartier_injective_iff_det_ne_zero p hf hd hp).symm

theorem jacobian_isOrdinaryOver_iff_globalCartier_bijective :
    J.abelianVariety.IsOrdinaryOver p ↔ Function.Bijective (a.globalCartier p) :=
  (a.jacobian_isOrdinaryOver_iff_det_ne_zero p hf hd hp J).trans
    (a.globalCartier_bijective_iff_det_ne_zero p hf hd hp).symm

/-- The actual cotangent differential has full rank exactly on the ordinary locus. -/
theorem jacobian_isOrdinaryOver_iff_verschiebungCotangent_injective :
    J.abelianVariety.IsOrdinaryOver p ↔
      Function.Injective (J.verschiebungCotangent p) :=
  (a.jacobian_isOrdinaryOver_iff_globalCartier_injective p hf hd hp J).trans
    (J.verschiebungCotangent_injective_iff (differentialChart a.curveModel) p a.x).symm

/-- Bijectivity refers to the genuine source and Frobenius-twisted target. -/
theorem jacobian_isOrdinaryOver_iff_verschiebungCotangent_bijective :
    J.abelianVariety.IsOrdinaryOver p ↔
      Function.Bijective (J.verschiebungCotangent p) :=
  (a.jacobian_isOrdinaryOver_iff_globalCartier_bijective p hf hd hp J).trans
    (J.verschiebungCotangent_bijective_iff (differentialChart a.curveModel) p a.x).symm

end SupersingularCurves.Hyperelliptic.SimpleRootModel
