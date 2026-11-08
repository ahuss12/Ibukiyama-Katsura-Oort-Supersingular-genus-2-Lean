import SupersingularCurves.Hyperelliptic.GenusTwoPRank
import SupersingularCurves.Hyperelliptic.CharacteristicThree

/-!
Integration checks for the general genus-two p-rank-zero equivalence.
The final example deliberately uses entries outside the prime field:
the Frobenius-twisted product vanishes although the ordinary square does not.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Polynomial Matrix AlgebraicCurve
open SupersingularCurves.Hyperelliptic SupersingularCurves.Differentials
open SupersingularCurves.IKO

namespace GenusTwoPRankExamples

section CharacteristicThree

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
private abbrev K3 := AlgebraicClosure (ZMod 3)
local instance : NeZero (2 : K3) :=
  ⟨fun h => (show ¬ 3 ∣ 2 by decide) ((CharP.cast_eq_zero_iff K3 3 2).mp h)⟩
private abbrev quintic := CharacteristicThree.model (K := K3)
private abbrev J3 := quintic.jacobianRealization.jacobian

example : J3.abelianVariety.HasPRankOver 3 0 ↔
    (coefficientMatrix 3 (X ^ 5 - 1 : K3[X])).map (fun c => c ^ 3) *
      coefficientMatrix 3 (X ^ 5 - 1 : K3[X]) = 0 :=
  quintic.jacobian_hasPRankOver_zero_iff_matrix 3
    CharacteristicThree.quintic_separable
    (Or.inl CharacteristicThree.quintic_degree) (by decide) J3

example : J3.abelianVariety.HasPRankOver 3 0 ↔
    ∀ ω : regularDifferentials K3 quintic.FunctionField,
      regularCartier 3 quintic.x (regularCartier 3 quintic.x ω) = 0 :=
  quintic.jacobian_hasPRankOver_zero_iff_cartier_square_zero 3
    CharacteristicThree.quintic_separable
    (Or.inl CharacteristicThree.quintic_degree) (by decide) J3

/-- The reverse implication recovers actual p-rank from the checked Cartier calculation. -/
example : J3.abelianVariety.HasPRankOver 3 0 :=
  (quintic.jacobian_hasPRankOver_zero_iff_cartier_square_zero 3
    CharacteristicThree.quintic_separable
    (Or.inl CharacteristicThree.quintic_degree) (by decide) J3).mpr
      CharacteristicThree.regular_cartier_distinction.2

private def twistExample (a : K3) : Matrix (Fin 2) (Fin 2) K3 :=
  !![-a, -1; 1, -a]

private theorem twistExample_twisted_square (a : K3) (h2 : a ^ 2 = -1) :
    (twistExample a).map (fun c => c ^ 3) * twistExample a = 0 := by
  have hcube : a ^ 3 = -a := by
    calc
      a ^ 3 = a * a ^ 2 := by ring
      _ = -a := by rw [h2]; ring
  have hnegcube : (-a) ^ 3 = a := by
    calc
      (-a) ^ 3 = -(a ^ 3) := by ring
      _ = a := by rw [hcube]; ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twistExample, Matrix.mul_apply, Fin.sum_univ_two, hnegcube] <;>
    ring_nf <;> simp [h2]

private theorem twistExample_ordinary_square_entry (a : K3) (h2 : a ^ 2 = -1) :
    (twistExample a * twistExample a) 0 0 = 1 := by
  have hthree : (3 : K3) = 0 :=
    (CharP.cast_eq_zero_iff K3 3 3).mpr (by decide)
  simp [twistExample, Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination h2 - hthree

private theorem twistExample_ordinary_square_ne_zero (a : K3) (h2 : a ^ 2 = -1) :
    twistExample a * twistExample a ≠ 0 := by
  intro hz
  have he := congrArg (fun N : Matrix (Fin 2) (Fin 2) K3 => N 0 0) hz
  rw [twistExample_ordinary_square_entry a h2] at he
  exact one_ne_zero he

/-- Trivial fixed vectors are governed by the twisted product, not ordinary M². -/
example (a : K3) (h2 : a ^ 2 = -1) :
    (∀ v : Fin 2 → K3,
      semilinearAction (frobeniusEquiv K3 3) (twistExample a) v = v → v = 0) ∧
      twistExample a * twistExample a ≠ 0 := by
  exact ⟨(semilinear_fixed_trivial_iff_twisted_square_zero 3 (twistExample a)).mpr
      (twistExample_twisted_square a h2), twistExample_ordinary_square_ne_zero a h2⟩

/-- Algebraic closedness supplies a genuine parameter, so the preceding test
does not rest on a possibly uninhabited scalar assumption. -/
example : ∃ a : K3, a ^ 2 = -1 ∧
    (twistExample a).map (fun c => c ^ 3) * twistExample a = 0 ∧
    (twistExample a * twistExample a) 0 0 = 1 ∧
    (∀ v : Fin 2 → K3,
      semilinearAction (frobeniusEquiv K3 3) (twistExample a) v = v → v = 0) := by
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : K3) (n := 2) (by decide)
  exact ⟨a, ha, twistExample_twisted_square a ha,
    twistExample_ordinary_square_entry a ha,
    (semilinear_fixed_trivial_iff_twisted_square_zero 3 (twistExample a)).mpr
      (twistExample_twisted_square a ha)⟩

end CharacteristicThree

section CharacteristicFive

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev K5 := AlgebraicClosure (ZMod 5)
local instance : NeZero (2 : K5) :=
  ⟨fun h => (show ¬ 5 ∣ 2 by decide) ((CharP.cast_eq_zero_iff K5 5 2).mp h)⟩

private theorem sextic_separable : (X ^ 6 - 1 : K5[X]).Separable := by
  simpa using separable_X_pow_sub_C' 5 6 (1 : K5) (by decide) one_ne_zero

private theorem sextic_degree : (X ^ 6 - 1 : K5[X]).natDegree = 6 := by
  simpa using (natDegree_X_pow_sub_C (R := K5) (n := 6) (r := 1))

private def sextic : SimpleRootModel K5 :=
  modelOfSeparable (X ^ 6 - 1) sextic_separable (Or.inr sextic_degree)
private abbrev J5 := sextic.jacobianRealization.jacobian

example : J5.abelianVariety.HasPRankOver 5 0 ↔
    (coefficientMatrix 5 (X ^ 6 - 1 : K5[X])).map (fun c => c ^ 5) *
      coefficientMatrix 5 (X ^ 6 - 1 : K5[X]) = 0 :=
  sextic.jacobian_hasPRankOver_zero_iff_matrix 5 sextic_separable
    (Or.inr sextic_degree) (by decide) J5

example : J5.abelianVariety.HasPRankOver 5 0 ↔
    ∀ ω : regularDifferentials K5 sextic.FunctionField,
      regularCartier 5 sextic.x (regularCartier 5 sextic.x ω) = 0 :=
  sextic.jacobian_hasPRankOver_zero_iff_cartier_square_zero 5 sextic_separable
    (Or.inr sextic_degree) (by decide) J5

end CharacteristicFive

end GenusTwoPRankExamples
