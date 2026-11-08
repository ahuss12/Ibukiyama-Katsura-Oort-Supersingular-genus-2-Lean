/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Hyperelliptic.GenusTwoPRank
import SupersingularCurves.Hyperelliptic.GenusTwoOrdinary
import SupersingularCurves.IKO.FifthPowerCongruences

/-!
# Uniform genus-two Cartier classification for y² = x⁵ − 1

For every odd prime other than five, the equation gives an actual quadratic
function field, smooth proper genus-two curve, and representing Jacobian.
Cartier on the full space of global differentials vanishes exactly when
p ≡ 4 mod 5, and its square vanishes exactly when p is not congruent to one.
The latter condition is equivalent to p-rank zero of the actual Jacobian.
The Jacobian is ordinary precisely when p ≡ 1 mod 5.

In the residue classes two and three Cartier is nonzero with square zero.
These statements use the uniform coefficient calculation and the proved
general genus-two p-rank criterion. No converse from p-rank zero to a
geometric supersingularity predicate is assumed here.
-/

set_option autoImplicit false
noncomputable section

namespace SupersingularCurves.Hyperelliptic.FifthPowerClassification
open Polynomial AlgebraicCurve KaehlerDifferential
open SupersingularCurves.IKO SupersingularCurves.Differentials

variable {K : Type*} [Field K]

theorem quintic_degree : (X ^ 5 - 1 : K[X]).natDegree = 5 := by
  simpa using (natDegree_X_pow_sub_C (R := K) (n := 5) (r := 1))

variable (p : ℕ) [hpPrime : Fact p.Prime] [CharP K p]

/-- The excluded prime is precisely the characteristic in which the
derivative of the quintic would vanish. -/
theorem five_ne_zero (hp5 : p ≠ 5) : (5 : K) ≠ 0 := by
  intro h
  have hd : p ∣ 5 := (CharP.cast_eq_zero_iff K p 5).mp h
  rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hd with h1 | h5
  · exact hpPrime.out.ne_one h1
  · exact hp5 h5

theorem quintic_separable (hp5 : p ≠ 5) : (X ^ 5 - 1 : K[X]).Separable := by
  simpa using separable_X_pow_sub_C (n := 5) (1 : K) (five_ne_zero p hp5) one_ne_zero

variable [IsAlgClosed K]

/-- The actual hyperelliptic curve model of y² = x⁵ − 1. -/
def model (hp5 : p ≠ 5) : SimpleRootModel K :=
  modelOfSeparable (X ^ 5 - 1) (quintic_separable p hp5) (Or.inl quintic_degree)

@[simp] theorem model_f (hp5 : p ≠ 5) :
    (model (K := K) p hp5).f = X ^ 5 - 1 := rfl

variable [NeZero (2 : K)] (hp5 : p ≠ 5)

theorem genus_eq_two : genusFF K (model (K := K) p hp5).FunctionField = 2 :=
  (model p hp5).genus_eq_two (quintic_separable p hp5) (Or.inl quintic_degree)

variable (hp : p % 2 = 1)

include hp

private theorem odd_prime_ge_three : 3 ≤ p := by
  have h := hpPrime.out.two_le
  omega

/-- Cartier vanishes on every regular differential exactly in residue
class four modulo five. -/
theorem regular_cartier_zero_iff :
    (∀ ω : regularDifferentials K (model (K := K) p hp5).FunctionField,
      regularCartier p (model p hp5).x ω = 0) ↔ p % 5 = 4 := by
  rw [(model p hp5).all_regularCartier_zero_iff
    (quintic_separable p hp5) (Or.inl quintic_degree) p hp, model_f]
  exact coefficientMatrix_fifthPower_zero_iff p (odd_prime_ge_three p hp) hp5

/-- The same zero criterion on the whole space of scheme-global forms. -/
theorem global_cartier_zero_iff :
    (∀ ω : (model (K := K) p hp5).GlobalForms,
      (model p hp5).globalCartier p ω = 0) ↔ p % 5 = 4 := by
  rw [(model p hp5).all_globalCartier_zero_iff
    (quintic_separable p hp5) (Or.inl quintic_degree) p hp, model_f]
  exact coefficientMatrix_fifthPower_zero_iff p (odd_prime_ge_three p hp) hp5

/-- The square of Cartier on all regular differentials is zero exactly
outside residue class one modulo five. -/
theorem regular_cartier_square_zero_iff :
    (∀ ω : regularDifferentials K (model (K := K) p hp5).FunctionField,
      regularCartier p (model p hp5).x
        (regularCartier p (model p hp5).x ω) = 0) ↔ p % 5 ≠ 1 := by
  rw [(model p hp5).all_regularCartier_square_zero_iff
    (quintic_separable p hp5) (Or.inl quintic_degree) p hp, model_f]
  exact coefficientMatrix_fifthPower_twisted_square_zero_iff
    p (odd_prime_ge_three p hp) hp5

/-- The square-zero criterion on the whole space of scheme-global forms. -/
theorem global_cartier_square_zero_iff :
    (∀ ω : (model (K := K) p hp5).GlobalForms,
      (model p hp5).globalCartier p ((model p hp5).globalCartier p ω) = 0) ↔
      p % 5 ≠ 1 := by
  rw [(model p hp5).all_globalCartier_square_zero_iff
    (quintic_separable p hp5) (Or.inl quintic_degree) p hp, model_f]
  exact coefficientMatrix_fifthPower_twisted_square_zero_iff
    p (odd_prime_ge_three p hp) hp5

/-- The actual representing Jacobian has p-rank zero exactly outside
residue class one modulo five. -/
theorem jacobian_hasPRankOver_zero_iff :
    (model (K := K) p hp5).jacobianRealization.jacobian.abelianVariety.HasPRankOver p 0 ↔
      p % 5 ≠ 1 := by
  rw [(model p hp5).jacobian_hasPRankOver_zero_iff_globalCartier_square_zero p
    (quintic_separable p hp5) (Or.inl quintic_degree) hp
    (model p hp5).jacobianRealization.jacobian]
  exact global_cartier_square_zero_iff p hp5 hp

/-- The actual representing Jacobian is ordinary exactly in residue
class one modulo five. -/
theorem jacobian_isOrdinaryOver_iff :
    (model (K := K) p hp5).jacobianRealization.jacobian.abelianVariety.IsOrdinaryOver p ↔
      p % 5 = 1 := by
  rw [(model p hp5).jacobian_isOrdinaryOver_iff_det_ne_zero p
    (quintic_separable p hp5) (Or.inl quintic_degree) hp
    (model p hp5).jacobianRealization.jacobian, model_f]
  exact coefficientMatrix_fifthPower_det_ne_zero_iff p (odd_prime_ge_three p hp) hp5

/-- In residue class two, global Cartier is nonzero and has square zero. -/
theorem global_cartier_distinction_mod_two (hmod : p % 5 = 2) :
    (¬ ∀ ω : (model (K := K) p hp5).GlobalForms,
      (model p hp5).globalCartier p ω = 0) ∧
    (∀ ω : (model (K := K) p hp5).GlobalForms,
      (model p hp5).globalCartier p ((model p hp5).globalCartier p ω) = 0) := by
  rw [global_cartier_zero_iff p hp5 hp, global_cartier_square_zero_iff p hp5 hp]
  omega

/-- In residue class three, global Cartier is nonzero and has square zero. -/
theorem global_cartier_distinction_mod_three (hmod : p % 5 = 3) :
    (¬ ∀ ω : (model (K := K) p hp5).GlobalForms,
      (model p hp5).globalCartier p ω = 0) ∧
    (∀ ω : (model (K := K) p hp5).GlobalForms,
      (model p hp5).globalCartier p ((model p hp5).globalCartier p ω) = 0) := by
  rw [global_cartier_zero_iff p hp5 hp, global_cartier_square_zero_iff p hp5 hp]
  omega

end SupersingularCurves.Hyperelliptic.FifthPowerClassification
