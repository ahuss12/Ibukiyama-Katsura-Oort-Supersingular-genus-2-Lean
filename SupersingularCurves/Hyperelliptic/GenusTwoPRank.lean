/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Hyperelliptic.GenusTwoJacobian
import SupersingularCurves.Hyperelliptic.GenusTwoGlobalForms
import SupersingularCurves.IKO.GenusTwoFixedVectors

/-!
# The general genus-two p-rank-zero Cartier criterion

For every separable quintic or sextic in odd characteristic, p-rank zero
of any representing Jacobian is equivalent to square-zero Cartier on the
whole space of regular differentials, and to the IKO twisted matrix equation.

The argument uses actual Jacobian torsion, its independently constructed
Picard point correspondence, and the logarithmic Cartier-fixed correspondence.
The remaining two-dimensional argument uses algebraic closedness to show that
trivial Cartier-fixed vectors force square-zero Cartier. No supersingularity
or superspeciality predicate is redefined or assumed in these results.
-/

set_option autoImplicit false
noncomputable section

namespace SupersingularCurves.Hyperelliptic.SimpleRootModel
open CategoryTheory AlgebraicGeometry AlgebraicCurve KaehlerDifferential
open AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open SupersingularCurves.Geometry SupersingularCurves.Differentials
open SupersingularCurves.IKO SupersingularCurves.PicardTorsion

variable {K : Type*} [Field K] [IsAlgClosed K] [NeZero (2 : K)]
  (a : SimpleRootModel K)
  (p : ℕ) [Fact p.Prime] [CharP K p]

/-- P-rank zero of an actual Jacobian is equivalent to trivial regular
Cartier-fixed differentials. This step does not require a genus hypothesis. -/
theorem jacobian_hasPRankOver_zero_iff_cartier_fixed_trivial
    {s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) a.curveModel.toBase}
    (J : Jacobian a.curveModel s) :
    J.abelianVariety.HasPRankOver p 0 ↔
      ∀ ω : regularDifferentials K a.FunctionField,
        regularCartier p a.x ω = ω → ω = 0 := by
  classical
  have hC : ConstantsAreBase K a.FunctionField :=
    constantsAreBase_of_isAlgClosed K a.FunctionField
  rw [← torsion_eq_zero_iff_fixed_eq_zero p a.x hC]
  constructor
  · intro h q
    have hc : Nat.card (Pic0.torsion K a.FunctionField p) = 1 := by
      rw [← card_torsionPoints_eq_picard _ J.picardPoints p]
      simpa using h.2
    exact (Nat.card_eq_one_iff_unique.mp hc).1.elim q 0
  · intro ht
    have hc : Nat.card (J.abelianVariety.torsionPoints p) = 1 := by
      rw [card_torsionPoints_eq_picard _ J.picardPoints p]
      exact Nat.card_eq_one_iff_exists.mpr ⟨0, ht⟩
    exact ⟨Nat.finite_of_card_ne_zero (by rw [hc]; decide), by simpa using hc⟩

variable (hf : a.f.Separable) (hd : a.f.natDegree = 5 ∨ a.f.natDegree = 6)
  (hp : p % 2 = 1)

include hf hd hp

/-- The verified full basis transports the absence of Cartier-fixed
differentials to the absence of fixed vectors of the coefficient matrix. -/
theorem cartier_fixed_trivial_iff_coordinates :
    (∀ ω : regularDifferentials K a.FunctionField,
      regularCartier p a.x ω = ω → ω = 0) ↔
      ∀ v : Fin 2 → K,
        semilinearAction (frobeniusEquiv K p) (coefficientMatrix p a.f) v = v →
          v = 0 := by
  constructor
  · intro h v hv
    apply (a.regularEquiv hf hd).injective
    rw [map_zero]
    apply h
    change regularCartier p a.x (a.regularCoordinates hf hd v) =
      a.regularCoordinates hf hd v
    rw [a.regularCartier_action hf hd p hp v, hv]
  · intro h ω hω
    apply (a.regularEquiv hf hd).symm.injective
    rw [map_zero]
    apply h
    rw [← a.regularCartier_coordinates hf hd p hp ω, hω]

/-- The general p-rank-zero criterion for an actual representing Jacobian.
Its matrix convention is the twisted product `M^(p) M`. -/
theorem jacobian_hasPRankOver_zero_iff_matrix
    {s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) a.curveModel.toBase}
    (J : Jacobian a.curveModel s) :
    J.abelianVariety.HasPRankOver p 0 ↔
      (coefficientMatrix p a.f).map (fun c => c ^ p) *
        coefficientMatrix p a.f = 0 := by
  rw [a.jacobian_hasPRankOver_zero_iff_cartier_fixed_trivial p J,
    a.cartier_fixed_trivial_iff_coordinates p hf hd hp]
  exact semilinear_fixed_trivial_iff_twisted_square_zero p (coefficientMatrix p a.f)

/-- For every separable quintic or sextic, p-rank zero is equivalent to
square-zero Cartier on all regular differentials of the actual function field. -/
theorem jacobian_hasPRankOver_zero_iff_cartier_square_zero
    {s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) a.curveModel.toBase}
    (J : Jacobian a.curveModel s) :
    J.abelianVariety.HasPRankOver p 0 ↔
      ∀ ω : regularDifferentials K a.FunctionField,
        regularCartier p a.x (regularCartier p a.x ω) = 0 := by
  rw [a.all_regularCartier_square_zero_iff hf hd p hp]
  exact a.jacobian_hasPRankOver_zero_iff_matrix p hf hd hp J

/-- The same p-rank criterion on actual scheme-global differential forms
of the smooth proper curve, through canonical generic restriction. -/
theorem jacobian_hasPRankOver_zero_iff_globalCartier_square_zero
    {s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) a.curveModel.toBase}
    (J : Jacobian a.curveModel s) :
    J.abelianVariety.HasPRankOver p 0 ↔
      ∀ ω : a.GlobalForms, a.globalCartier p (a.globalCartier p ω) = 0 := by
  rw [a.all_globalCartier_square_zero_iff hf hd p hp]
  exact a.jacobian_hasPRankOver_zero_iff_matrix p hf hd hp J

end SupersingularCurves.Hyperelliptic.SimpleRootModel
