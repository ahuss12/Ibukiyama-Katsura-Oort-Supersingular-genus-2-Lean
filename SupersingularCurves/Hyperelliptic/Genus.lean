/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Hyperelliptic.Ramification
import Theorems.Thm_AlgebraicCurve_two_mul_genusFF_sub_two_eq_of_isSeparable_of_tame
import Theorems.Thm_AlgebraicCurve_genusFF_ratFunc_eq_zero_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_finite_and_finrank_regularDiffs_eq_genusFF_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_regularDiffs_eq_regularDifferentials_of_perfectField

/-! # Genus and the dimension of actual regular differentials

Genus is the imported cohomological function-field genus. Riemann--Hurwitz
and the regular-differential dimension theorem are used with their hypotheses
proved for the constructed quotient field.
-/
set_option autoImplicit false
noncomputable section
namespace SupersingularCurves.Hyperelliptic.SimpleRootModel
open AlgebraicCurve
variable {K : Type*} [Field K] [IsAlgClosed K] [NeZero (2 : K)] (a : SimpleRootModel K)

instance essFiniteType : Algebra.EssFiniteType K a.FunctionField :=
  essFiniteType_of_transcendental_of_finiteDimensional
    a.transcendental_x a.finiteDimensional_coordinate

/-- Riemann--Hurwitz proves genus two; it is not part of the model data. -/
theorem genus_eq_two (hf : a.f.Separable) (hd : a.f.natDegree = 5 ∨ a.f.natDegree = 6) :
    genusFF K a.FunctionField = 2 := by
  have hF : ∃ x : RatFunc K, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K {x}) (RatFunc K) := by
    refine ⟨RatFunc.X, RatFunc.transcendental_X, ?_⟩
    rw [RatFunc.adjoin_X]
    refine Module.Finite.of_equiv_equiv
      (IntermediateField.topEquiv :
        (⊤ : IntermediateField K (RatFunc K)) ≃ₐ[K] RatFunc K).symm.toRingEquiv
      (RingEquiv.refl (RatFunc K)) ?_
    ext z
    rfl
  have h := two_mul_genusFF_sub_two_eq_of_isSeparable_of_tame hF (a.tame hf hd)
  rw [a.finrank_functionField, a.total_ramification hf hd,
    genusFF_ratFunc_eq_zero_of_isAlgClosed] at h
  omega

theorem finite_and_finrank_regularDifferentials (hf : a.f.Separable)
    (hd : a.f.natDegree = 5 ∨ a.f.natDegree = 6) :
    Module.Finite K (regularDifferentials K a.FunctionField) ∧
      Module.finrank K (regularDifferentials K a.FunctionField) = 2 := by
  have h := finite_and_finrank_regularDiffs_eq_genusFF_of_isAlgClosed
    (K := K) (F := a.FunctionField)
  rw [regularDiffs_eq_regularDifferentials_of_perfectField, a.genus_eq_two hf hd] at h
  exact h

end SupersingularCurves.Hyperelliptic.SimpleRootModel
