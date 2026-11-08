/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Geometry.FrobeniusFiniteFieldScalarHom
import SupersingularCurves.Geometry.FrobeniusFiniteFieldHomDescent

/-! # Scalar Frobenius supplies the invariance condition for actual Hom descent -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SupersingularCurves.Geometry.FrobeniusFiniteFieldScalarHom
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open FrobeniusDescent SchemeFrobenius FrobeniusFiniteFieldHomDescent
variable {K : Type} [Field K] [IsAlgClosed K]
variable (p : ℕ) [Fact p.Prime] [CharP K p] {g h : ℕ}

/-- The genuine homomorphism supplies precisely the coefficient-change invariance
used by the representable Hom scheme to descend its point. -/
theorem changeBase_projection_invariant
    (A : AbelianVariety (fixedField K p 2) g)
    (B : AbelianVariety (fixedField K p 2) h)
    (hA : absolute p A.group.X.hom ≫ absolute p A.group.X.hom =
      (GroupScheme.law A.group).schemeNsmul p)
    (hB : absolute p B.group.X.hom ≫ absolute p B.group.X.hom =
      (GroupScheme.law B.group).schemeNsmul p)
    (f : (A.baseChange K).group ⟶ (B.baseChange K).group) :
    changeBase (iterateFrobenius K p 2) (fixedBase p) (fixedBase p)
      (FrobeniusFiniteFieldHomDescent.frobenius_fixedBase p 2)
      (f.hom.hom.left ≫ pullback.fst B.group.X.hom (fixedBase p)) =
        f.hom.hom.left ≫ pullback.fst B.group.X.hom (fixedBase p) := by
  have hb : Spec.map (CommRingCat.ofHom (iterateFrobenius K p 2)) =
      baseMap p K ≫ baseMap p K := by
    unfold baseMap
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    ext a
    change a ^ (p ^ 2) = (a ^ p) ^ p
    rw [pow_two, pow_mul]
  have ha : pullback.lift (pullback.fst A.group.X.hom (fixedBase p))
      (pullback.snd A.group.X.hom (fixedBase p) ≫
        Spec.map (CommRingCat.ofHom (iterateFrobenius K p 2)))
      (by rw [Category.assoc, FrobeniusFiniteFieldHomDescent.frobenius_fixedBase];
          exact pullback.condition) = coefficientSquare p A := by
    apply pullback.hom_ext
    · simp only [pullback.lift_fst, coefficientSquare_fst]
    · change _ = coefficientSquare p A ≫ (A.baseChange K).group.X.hom
      rw [pullback.lift_snd, coefficientSquare_snd, hb]
      rfl
  unfold changeBase
  rw [ha]
  exact hom_projection_invariant p A B hA hB f

end SupersingularCurves.Geometry.FrobeniusFiniteFieldScalarHom
