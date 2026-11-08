import SupersingularCurves.Hyperelliptic.GenusTwoOrdinaryVerschiebung
import SupersingularCurves.Hyperelliptic.FifthPowerClassification

/-!
Concrete integration checks for arbitrary-matrix ordinarity and the four
uniform fifth-power congruence cases. The characteristic-eleven case also
exercises the true Jacobian Verschiebung cotangent comparison.
-/
set_option autoImplicit false
noncomputable section

open Polynomial AlgebraicCurve SupersingularCurves.IKO
open SupersingularCurves.Hyperelliptic

namespace Checkpoint23Examples

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance : Fact (Nat.Prime 11) := ⟨by decide⟩
local instance : Fact (Nat.Prime 19) := ⟨by decide⟩
local instance : NeZero (2 : AlgebraicClosure (ZMod 3)) :=
  ⟨fun h => (show ¬ 3 ∣ 2 by decide) ((CharP.cast_eq_zero_iff _ 3 2).mp h)⟩
local instance : NeZero (2 : AlgebraicClosure (ZMod 7)) :=
  ⟨fun h => (show ¬ 7 ∣ 2 by decide) ((CharP.cast_eq_zero_iff _ 7 2).mp h)⟩
local instance : NeZero (2 : AlgebraicClosure (ZMod 11)) :=
  ⟨fun h => (show ¬ 11 ∣ 2 by decide) ((CharP.cast_eq_zero_iff _ 11 2).mp h)⟩
local instance : NeZero (2 : AlgebraicClosure (ZMod 19)) :=
  ⟨fun h => (show ¬ 19 ∣ 2 by decide) ((CharP.cast_eq_zero_iff _ 19 2).mp h)⟩

-- A non-diagonal invertible matrix exercises the new elimination argument.
example : Nat.card (fixedVectors 3
    (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (AlgebraicClosure (ZMod 3)))) = 3 ^ 2 := by
  apply (card_fixedVectors_eq_prime_sq_iff_det_ne_zero 3 _).mpr
  simp [Matrix.det_fin_two]

-- A singular nonzero matrix exercises the converse of the count criterion.
example : Nat.card (fixedVectors 3
    (!![1, 1; 1, 1] : Matrix (Fin 2) (Fin 2) (AlgebraicClosure (ZMod 3)))) ≠ 3 ^ 2 := by
  intro h
  have hd := (card_fixedVectors_eq_prime_sq_iff_det_ne_zero 3 _).mp h
  simp [Matrix.det_fin_two] at hd

example : let a := FifthPowerClassification.model (K := AlgebraicClosure (ZMod 3)) 3 (by decide);
    (¬ ∀ ω : a.GlobalForms, a.globalCartier 3 ω = 0) ∧
    (∀ ω : a.GlobalForms, a.globalCartier 3 (a.globalCartier 3 ω) = 0) :=
  FifthPowerClassification.global_cartier_distinction_mod_three 3
    (by decide) (by decide) (by decide)

example : let a := FifthPowerClassification.model (K := AlgebraicClosure (ZMod 7)) 7 (by decide);
    (¬ ∀ ω : a.GlobalForms, a.globalCartier 7 ω = 0) ∧
    (∀ ω : a.GlobalForms, a.globalCartier 7 (a.globalCartier 7 ω) = 0) :=
  FifthPowerClassification.global_cartier_distinction_mod_two 7
    (by decide) (by decide) (by decide)

example : let a := FifthPowerClassification.model (K := AlgebraicClosure (ZMod 19)) 19 (by decide);
    ∀ ω : a.GlobalForms, a.globalCartier 19 ω = 0 := by
  exact (FifthPowerClassification.global_cartier_zero_iff 19
    (by decide) (by decide)).mpr (by decide)

private abbrev elevenModel : SimpleRootModel (AlgebraicClosure (ZMod 11)) :=
  FifthPowerClassification.model 11 (by decide)

private theorem eleven_ordinary :
    elevenModel.jacobianRealization.jacobian.abelianVariety.IsOrdinaryOver 11 := by
  apply (elevenModel.jacobian_isOrdinaryOver_iff_det_ne_zero 11
    (FifthPowerClassification.quintic_separable 11 (by decide))
    (Or.inl FifthPowerClassification.quintic_degree) (by decide)
    elevenModel.jacobianRealization.jacobian).mpr
  exact coefficientMatrix_fifthPower_det_ne_zero_mod_one 11 (by decide) (by decide)

example : elevenModel.jacobianRealization.jacobian.abelianVariety.IsOrdinaryOver 11 :=
  eleven_ordinary

example : Function.Bijective
    (elevenModel.jacobianRealization.jacobian.verschiebungCotangent 11) := by
  exact (elevenModel.jacobian_isOrdinaryOver_iff_verschiebungCotangent_bijective 11
    (FifthPowerClassification.quintic_separable 11 (by decide))
    (Or.inl FifthPowerClassification.quintic_degree) (by decide)
    elevenModel.jacobianRealization.jacobian).mp eleven_ordinary

end Checkpoint23Examples
