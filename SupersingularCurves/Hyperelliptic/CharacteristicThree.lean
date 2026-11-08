/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Hyperelliptic.GenusTwoGlobalForms
import SupersingularCurves.Hyperelliptic.GenusTwoJacobian

/-!
# A genuine genus-two curve with nonzero square-zero Cartier

In characteristic three the equation y² = x⁵ − 1 gives an actual function
field, smooth proper curve, full regular/global differential spaces, and
representing Jacobian. Its Cartier operator is nonzero but has square zero;
its actual Jacobian has p-rank zero. No geometric classification converse is
used or asserted.
-/
set_option autoImplicit false
noncomputable section
namespace SupersingularCurves.Hyperelliptic.CharacteristicThree
open Polynomial AlgebraicCurve KaehlerDifferential
open SupersingularCurves.IKO SupersingularCurves.Differentials
variable {K : Type*} [Field K] [IsAlgClosed K] [CharP K 3]
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance two_ne_zero : NeZero (2 : K) :=
  ⟨fun h => (show ¬ 3 ∣ 2 by decide) ((CharP.cast_eq_zero_iff K 3 2).mp h)⟩

omit [IsAlgClosed K] in
/-- The input equation is proved nonsingular in characteristic three. -/
theorem quintic_separable : (X^5 - 1 : K[X]).Separable := by
  simpa using separable_X_pow_sub_C' 3 5 (1 : K) (by decide) one_ne_zero

omit [IsAlgClosed K] [CharP K 3] in
theorem quintic_degree : (X^5 - 1 : K[X]).natDegree = 5 := by
  simpa using (natDegree_X_pow_sub_C (R := K) (n := 5) (r := 1))

def model : SimpleRootModel K :=
  modelOfSeparable (X^5 - 1) quintic_separable (Or.inl quintic_degree)

@[simp] theorem model_f : (model (K := K)).f = X^5 - 1 := rfl

theorem genus_eq_two : genusFF K (model (K := K)).FunctionField = 2 :=
  (model (K := K)).genus_eq_two quintic_separable (Or.inl quintic_degree)

theorem regular_cartier_distinction :
    (¬ ∀ ω : regularDifferentials K (model (K := K)).FunctionField,
      regularCartier 3 model.x ω = 0) ∧
    (∀ ω : regularDifferentials K (model (K := K)).FunctionField,
      regularCartier 3 model.x (regularCartier 3 model.x ω) = 0) := by
  rw [model.all_regularCartier_zero_iff quintic_separable (Or.inl quintic_degree) 3 (by decide),
    model.all_regularCartier_square_zero_iff quintic_separable (Or.inl quintic_degree) 3 (by decide)]
  simpa only [model_f, ← frobenius_twistMatrix] using
    x_fifth_sub_one_three_matrix_distinction (frobeniusEquiv K 3)

theorem global_cartier_distinction :
    (¬ ∀ ω : (model (K := K)).GlobalForms, model.globalCartier 3 ω = 0) ∧
    (∀ ω : (model (K := K)).GlobalForms,
      model.globalCartier 3 (model.globalCartier 3 ω) = 0) := by
  rw [model.all_globalCartier_zero_iff quintic_separable (Or.inl quintic_degree) 3 (by decide),
    model.all_globalCartier_square_zero_iff quintic_separable (Or.inl quintic_degree) 3 (by decide)]
  simpa only [model_f, ← frobenius_twistMatrix] using
    x_fifth_sub_one_three_matrix_distinction (frobeniusEquiv K 3)

theorem jacobian_hasPRankOver_zero :
    (model (K := K)).jacobianRealization.jacobian.abelianVariety.HasPRankOver 3 0 :=
  model.jacobian_hasPRankOver_zero_of_cartier_square_zero 3
    regular_cartier_distinction.2 model.jacobianRealization.jacobian

end SupersingularCurves.Hyperelliptic.CharacteristicThree
