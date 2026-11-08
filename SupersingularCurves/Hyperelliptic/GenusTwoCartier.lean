/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Hyperelliptic.GenusTwoBasis

/-!
# The full Cartier matrix for a general quintic or sextic

The operator is the previously constructed Cartier operator on actual regular
differentials. The matrix now describes the whole space for every separable
equation of degree five or six. Zero and square-zero are distinct conditions.
No geometric superspecial or supersingular classification is asserted here.
-/

set_option autoImplicit false
noncomputable section

namespace SupersingularCurves.Hyperelliptic.SimpleRootModel
open AlgebraicCurve KaehlerDifferential
open SupersingularCurves.IKO SupersingularCurves.Differentials
variable {K : Type*} [Field K] [IsAlgClosed K] [NeZero (2 : K)]
  (a : SimpleRootModel K) (hf : a.f.Separable)
  (hd : a.f.natDegree = 5 ∨ a.f.natDegree = 6)
  (p : ℕ) [Fact p.Prime] [CharP K p] (hp : p % 2 = 1)

include hf hd hp

omit [NeZero (2 : K)] in
theorem regularCartier_action (v : Fin 2 → K) :
    regularCartier p a.x (a.regularCoordinates hf hd v) =
      a.regularCoordinates hf hd
        (semilinearAction (frobeniusEquiv K p) (coefficientMatrix p a.f) v) :=
  regularCartier_differentialCombination p a.x hp a.f (by omega) a.y
    a.equation_in_functionField a.y_ne_zero _ _ v

/-- The IKO matrix coordinates hold for an arbitrary regular differential. -/
theorem regularCartier_coordinates (ω : regularDifferentials K a.FunctionField) :
    (a.regularEquiv hf hd).symm (regularCartier p a.x ω) =
      semilinearAction (frobeniusEquiv K p) (coefficientMatrix p a.f)
        ((a.regularEquiv hf hd).symm ω) := by
  apply (a.regularEquiv hf hd).injective
  rw [LinearEquiv.apply_symm_apply]
  exact (congrArg (regularCartier p a.x)
    ((a.regularEquiv hf hd).apply_symm_apply ω).symm).trans
      (a.regularCartier_action hf hd p hp _)

theorem all_regularCartier_zero_iff :
    (∀ ω : regularDifferentials K a.FunctionField, regularCartier p a.x ω = 0) ↔
      coefficientMatrix p a.f = 0 := by
  have hspan := cartier_differentialSpan_zero_iff p a.x hp a.f (by omega) a.y
    a.equation_in_functionField a.y_ne_zero a.transcendental_x a.dx_ne_zero
  constructor
  · intro h
    apply hspan.mp
    intro v
    exact congrArg Subtype.val (h (a.regularCoordinates hf hd v))
  · intro h ω
    obtain ⟨v, rfl⟩ := (a.regularCoordinates_bijective hf hd).2 ω
    apply Subtype.ext
    exact hspan.mpr h v

/-- Iteration uses M^(p) M, including its order, rather than the ordinary square. -/
theorem all_regularCartier_square_zero_iff :
    (∀ ω : regularDifferentials K a.FunctionField,
      regularCartier p a.x (regularCartier p a.x ω) = 0) ↔
      (coefficientMatrix p a.f).map (fun c => c^p) * coefficientMatrix p a.f = 0 := by
  have hspan := cartier_differentialSpan_square_zero_iff p a.x hp a.f (by omega) a.y
    a.equation_in_functionField a.y_ne_zero a.transcendental_x a.dx_ne_zero
  constructor
  · intro h
    apply hspan.mp
    intro v
    exact congrArg Subtype.val (h (a.regularCoordinates hf hd v))
  · intro h ω
    obtain ⟨v, rfl⟩ := (a.regularCoordinates_bijective hf hd).2 ω
    apply Subtype.ext
    exact hspan.mpr h v

end SupersingularCurves.Hyperelliptic.SimpleRootModel
