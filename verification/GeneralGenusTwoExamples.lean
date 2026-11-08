import SupersingularCurves.Hyperelliptic.CharacteristicThree

open Polynomial AlgebraicCurve
open SupersingularCurves.Hyperelliptic SupersingularCurves.Differentials
noncomputable section

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance : NeZero (2 : AlgebraicClosure (ZMod 3)) :=
  ⟨fun h => (show ¬ 3 ∣ 2 by decide) ((CharP.cast_eq_zero_iff _ 3 2).mp h)⟩
local instance : NeZero (2 : AlgebraicClosure (ZMod 5)) :=
  ⟨fun h => (show ¬ 5 ∣ 2 by decide) ((CharP.cast_eq_zero_iff _ 5 2).mp h)⟩

-- The full Cartier distinction now belongs to an actual genus-two curve.
example : genusFF (AlgebraicClosure (ZMod 3))
    (CharacteristicThree.model (K := AlgebraicClosure (ZMod 3))).FunctionField = 2 :=
  CharacteristicThree.genus_eq_two

example : let a := CharacteristicThree.model (K := AlgebraicClosure (ZMod 3))
    (¬ ∀ ω : a.GlobalForms, a.globalCartier 3 ω = 0) ∧
    (∀ ω : a.GlobalForms, a.globalCartier 3 (a.globalCartier 3 ω) = 0) :=
  CharacteristicThree.global_cartier_distinction

example : (CharacteristicThree.model (K := AlgebraicClosure (ZMod 3))).jacobianRealization.jacobian.abelianVariety.HasPRankOver 3 0 :=
  CharacteristicThree.jacobian_hasPRankOver_zero

-- A sextic in another characteristic exercises the general basis construction.
private theorem sextic_five_separable :
    (X^6 - 1 : (AlgebraicClosure (ZMod 5))[X]).Separable := by
  simpa using separable_X_pow_sub_C' 5 6
    (1 : AlgebraicClosure (ZMod 5)) (by decide) one_ne_zero

private def sexticFive : SimpleRootModel (AlgebraicClosure (ZMod 5)) :=
  modelOfSeparable (X^6 - 1) sextic_five_separable
    (Or.inr (by simpa using (natDegree_X_pow_sub_C
      (R := AlgebraicClosure (ZMod 5)) (n := 6) (r := 1))))

example : Module.finrank (AlgebraicClosure (ZMod 5)) sexticFive.GlobalForms = 2 := by
  exact sexticFive.globalForms_finrank sextic_five_separable
    (Or.inr (by simpa [sexticFive] using (natDegree_X_pow_sub_C
      (R := AlgebraicClosure (ZMod 5)) (n := 6) (r := 1))))

-- A separable sextic with a root at zero has a degree-five reciprocal chart.
private theorem zero_root_sextic_separable :
    (X^6 - X : (AlgebraicClosure (ZMod 3))[X]).Separable := by
  have h6 : (6 : AlgebraicClosure (ZMod 3)) = 0 := by
    exact (CharP.cast_eq_zero_iff _ 3 6).mpr (by decide)
  change IsCoprime _ _
  simp only [derivative_sub, derivative_pow, derivative_X,
    Nat.cast_ofNat, h6, C_0, zero_mul, zero_sub]
  exact ⟨0, -1, by simp⟩

example : ((X^6 - X : (AlgebraicClosure (ZMod 3))[X]).reflect 6).Separable := by
  apply reflect_six_separable _ zero_root_sextic_separable
  right
  compute_degree!
