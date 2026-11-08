/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.Differentials.Cartier

/-! Inverse-Frobenius scalar and monomial laws, extracted from the larger project's
CartierResidue module. No residue or Picard-torsion dependencies are needed here. -/

set_option autoImplicit false
noncomputable section
namespace SupersingularCurves.Differentials
open AlgebraicCurve KaehlerDifferential
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
  [PerfectField K] [IsCurveOver K F]
  (p : ℕ) [Fact p.Prime] [CharP K p]
  (x : F) [FiniteDimensional (IntermediateField.adjoin K {x}) F]

/-- Cartier's scalar law over the perfect constant field. -/
theorem cartier_smul (c : K) (ω : Ω[F⁄K]) :
    cartier p x (c • ω) = (frobeniusEquiv K p).symm c • cartier p x ω := by
  have h := cartier_pow_smul p x
    (algebraMap K F ((frobeniusEquiv K p).symm c)) ω
  have hc : (algebraMap K F ((frobeniusEquiv K p).symm c)) ^ p =
      algebraMap K F c := by rw [← map_pow, frobeniusEquiv_symm_pow_p]
  rw [hc, algebraMap_smul, algebraMap_smul] at h
  exact h

/-- Monomials below the exceptional exponent are exact up to a nonzero constant. -/
theorem cartier_monomial_low (f : F) (r : ℕ) (hr : r < p - 1) :
    cartier p x (f ^ r • D K F f) = 0 := by
  have hp := (Fact.out : p.Prime).two_le
  have hc : ((r + 1 : ℕ) : K) ≠ 0 := by
    rw [ne_eq, CharP.cast_eq_zero_iff K p]
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have h := cartier_exact (K := K) p x (f ^ (r + 1))
  rw [Derivation.leibniz_pow, Nat.add_sub_cancel,
    ← Nat.cast_smul_eq_nsmul K, cartier_smul] at h
  exact (smul_eq_zero.mp h).resolve_left
    ((map_ne_zero (frobeniusEquiv K p).symm).mpr hc)

/-- The exceptional congruence class of nonnegative monomials. -/
theorem cartier_monomial_exceptional (f : F) (n : ℕ) (hn : n % p = p - 1) :
    cartier p x (f ^ n • D K F f) = f ^ (n / p) • D K F f := by
  have he : n = n / p * p + (p - 1) := by
    rw [← hn, Nat.mul_comm (n / p) p, Nat.div_add_mod]
  conv_lhs => rw [he, pow_add, pow_mul, mul_smul]
  rw [cartier_pow_smul, cartier_normalization]

/-- All other congruence classes of nonnegative monomials are killed. -/
theorem cartier_monomial_other (f : F) (n : ℕ) (hn : n % p ≠ p - 1) :
    cartier p x (f ^ n • D K F f) = 0 := by
  have he : n = n / p * p + n % p := by simpa only [Nat.mul_comm] using (Nat.div_add_mod n p).symm
  conv_lhs => rw [he, pow_add, pow_mul, mul_smul]
  rw [cartier_pow_smul, cartier_monomial_low, smul_zero]
  have h := Nat.mod_lt n (Fact.out : p.Prime).pos
  omega

end SupersingularCurves.Differentials
