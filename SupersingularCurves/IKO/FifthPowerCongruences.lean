/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.IKO.CoefficientMatrix
import SupersingularCurves.IKO.BinomialPolynomial

/-!
# Uniform Cartier matrix congruences for y² = x⁵ − 1

The coefficients are computed for every odd prime other than five. Their
support modulo five gives all four matrix patterns, and the relevant
binomial coefficients are proved nonzero in characteristic p. These results
concern the coefficient matrix, without assuming a geometric classification.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace SupersingularCurves.IKO
open Polynomial Matrix
variable {K : Type*} [Field K]

theorem fifthPower_power_expand (n : ℕ) :
    (X ^ 5 - 1 : K[X]) ^ n = expand K 5 ((X - 1) ^ n) := by
  simp

private theorem coeff_sub_one_pow_fifth (n i : ℕ) :
    ((X - 1 : K[X]) ^ n).coeff i = (-1 : K) ^ (n - i) * (n.choose i : K) := by
  simpa [sub_eq_add_neg] using coeff_X_add_C_pow (-1 : K) n i

/-- The exact coefficient formula, including coefficients outside the support. -/
theorem coeff_fifthPower_power (n i : ℕ) :
    ((X ^ 5 - 1 : K[X]) ^ n).coeff i =
      if 5 ∣ i then (-1 : K) ^ (n - i / 5) * (n.choose (i / 5) : K) else 0 := by
  rw [fifthPower_power_expand, coeff_expand (by decide : 0 < 5)]
  simp only [coeff_sub_one_pow_fifth]

/-- A candidate nonzero entry in the raw IKO matrix. -/
def fifthPowerEntry (p i : ℕ) : K :=
  (-1 : K) ^ ((p - 1) / 2 - i / 5) * (((p - 1) / 2).choose (i / 5) : K)

theorem coefficientMatrix_fifthPower_mod_one (p : ℕ) (hp : 3 ≤ p)
    (hmod : p % 5 = 1) :
    coefficientMatrix p (X ^ 5 - 1 : K[X]) =
      !![fifthPowerEntry p (p - 1), 0; 0, fifthPowerEntry p (2 * p - 2)] := by
  have h00 : 5 ∣ p - 1 := by omega
  have h01 : ¬ 5 ∣ p - 2 := by omega
  have h10 : ¬ 5 ∣ 2 * p - 1 := by omega
  have h11 : 5 ∣ 2 * p - 2 := by omega
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coefficientMatrix, coeff_fifthPower_power, fifthPowerEntry, h00, h01, h10, h11]

theorem coefficientMatrix_fifthPower_mod_two (p : ℕ) (hp : 3 ≤ p)
    (hmod : p % 5 = 2) :
    coefficientMatrix p (X ^ 5 - 1 : K[X]) =
      !![0, fifthPowerEntry p (p - 2); 0, 0] := by
  have h00 : ¬ 5 ∣ p - 1 := by omega
  have h01 : 5 ∣ p - 2 := by omega
  have h10 : ¬ 5 ∣ 2 * p - 1 := by omega
  have h11 : ¬ 5 ∣ 2 * p - 2 := by omega
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coefficientMatrix, coeff_fifthPower_power, fifthPowerEntry, h00, h01, h10, h11]

theorem coefficientMatrix_fifthPower_mod_three (p : ℕ) (hp : 3 ≤ p)
    (hmod : p % 5 = 3) :
    coefficientMatrix p (X ^ 5 - 1 : K[X]) =
      !![0, 0; fifthPowerEntry p (2 * p - 1), 0] := by
  have h00 : ¬ 5 ∣ p - 1 := by omega
  have h01 : ¬ 5 ∣ p - 2 := by omega
  have h10 : 5 ∣ 2 * p - 1 := by omega
  have h11 : ¬ 5 ∣ 2 * p - 2 := by omega
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coefficientMatrix, coeff_fifthPower_power, fifthPowerEntry, h00, h01, h10, h11]

theorem coefficientMatrix_fifthPower_mod_four (p : ℕ) (hp : 3 ≤ p)
    (hmod : p % 5 = 4) : coefficientMatrix p (X ^ 5 - 1 : K[X]) = 0 := by
  have h00 : ¬ 5 ∣ p - 1 := by omega
  have h01 : ¬ 5 ∣ p - 2 := by omega
  have h10 : ¬ 5 ∣ 2 * p - 1 := by omega
  have h11 : ¬ 5 ∣ 2 * p - 2 := by omega
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coefficientMatrix, coeff_fifthPower_power, h00, h01, h10, h11]

variable (p : ℕ) [hpPrime : Fact p.Prime] [CharP K p]

theorem fifthPowerEntry_ne_zero (i : ℕ) (hi : i / 5 ≤ (p - 1) / 2) :
    (fifthPowerEntry p i : K) ≠ 0 := by
  have hp0 : 0 < p := hpPrime.out.pos
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    (cast_choose_ne_zero_of_lt p (by omega) hi)

/-- For p ≡ 1 mod 5 both diagonal coefficients are nonzero. -/
theorem coefficientMatrix_fifthPower_det_ne_zero_mod_one (hp : 3 ≤ p)
    (hmod : p % 5 = 1) :
    (coefficientMatrix p (X ^ 5 - 1 : K[X])).det ≠ 0 := by
  rw [coefficientMatrix_fifthPower_mod_one p hp hmod]
  simpa [Matrix.det_fin_two] using
    mul_ne_zero (fifthPowerEntry_ne_zero (K := K) p (p - 1) (by omega))
      (fifthPowerEntry_ne_zero (K := K) p (2 * p - 2) (by omega))

/-- For p ≡ 2 mod 5 the upper off-diagonal coefficient is nonzero. -/
theorem coefficientMatrix_fifthPower_ne_zero_mod_two (hp : 3 ≤ p)
    (hmod : p % 5 = 2) : coefficientMatrix p (X ^ 5 - 1 : K[X]) ≠ 0 := by
  intro hz
  have h := congrArg (fun N : Matrix (Fin 2) (Fin 2) K => N 0 1) hz
  rw [coefficientMatrix_fifthPower_mod_two p hp hmod] at h
  exact fifthPowerEntry_ne_zero p (p - 2) (by omega) (by simpa using h)

/-- For p ≡ 3 mod 5 the lower off-diagonal coefficient is nonzero. -/
theorem coefficientMatrix_fifthPower_ne_zero_mod_three (hp : 3 ≤ p)
    (hmod : p % 5 = 3) : coefficientMatrix p (X ^ 5 - 1 : K[X]) ≠ 0 := by
  intro hz
  have h := congrArg (fun N : Matrix (Fin 2) (Fin 2) K => N 1 0) hz
  rw [coefficientMatrix_fifthPower_mod_three p hp hmod] at h
  exact fifthPowerEntry_ne_zero p (2 * p - 1) (by omega) (by simpa using h)

omit [CharP K p] in
theorem coefficientMatrix_fifthPower_twisted_square_zero_mod_two (hp : 3 ≤ p)
    (hmod : p % 5 = 2) :
    (coefficientMatrix p (X ^ 5 - 1 : K[X])).map (fun c => c ^ p) *
      coefficientMatrix p (X ^ 5 - 1 : K[X]) = 0 := by
  rw [coefficientMatrix_fifthPower_mod_two p hp hmod]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hpPrime.out.ne_zero]

omit [CharP K p] in
theorem coefficientMatrix_fifthPower_twisted_square_zero_mod_three (hp : 3 ≤ p)
    (hmod : p % 5 = 3) :
    (coefficientMatrix p (X ^ 5 - 1 : K[X])).map (fun c => c ^ p) *
      coefficientMatrix p (X ^ 5 - 1 : K[X]) = 0 := by
  rw [coefficientMatrix_fifthPower_mod_three p hp hmod]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hpPrime.out.ne_zero]

theorem coefficientMatrix_fifthPower_twisted_square_ne_zero_mod_one (hp : 3 ≤ p)
    (hmod : p % 5 = 1) :
    (coefficientMatrix p (X ^ 5 - 1 : K[X])).map (fun c => c ^ p) *
      coefficientMatrix p (X ^ 5 - 1 : K[X]) ≠ 0 := by
  rw [coefficientMatrix_fifthPower_mod_one p hp hmod]
  intro hz
  have h := congrArg (fun N : Matrix (Fin 2) (Fin 2) K => N 0 0) hz
  have he : (fifthPowerEntry p (p - 1) : K) ≠ 0 :=
    fifthPowerEntry_ne_zero p (p - 1) (by omega)
  exact mul_ne_zero (pow_ne_zero p he) he
    (by simpa [Matrix.mul_apply, Fin.sum_univ_two, hpPrime.out.ne_zero] using h)

omit [CharP K p] in
theorem prime_ne_five_mod_five (hp5 : p ≠ 5) :
    p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by
  have hnd : ¬ 5 ∣ p := by
    intro hd
    have h := (Nat.dvd_prime hpPrime.out).mp hd
    omega
  have hm : p % 5 ≠ 0 := fun h => hnd (Nat.dvd_of_mod_eq_zero h)
  omega

/-- The determinant is nonzero exactly in residue class one. -/
theorem coefficientMatrix_fifthPower_det_ne_zero_iff (hp : 3 ≤ p) (hp5 : p ≠ 5) :
    (coefficientMatrix p (X ^ 5 - 1 : K[X])).det ≠ 0 ↔ p % 5 = 1 := by
  constructor
  · intro hdet
    rcases prime_ne_five_mod_five p hp5 with h1 | h2 | h3 | h4
    · exact h1
    · rw [coefficientMatrix_fifthPower_mod_two p hp h2] at hdet
      simp [Matrix.det_fin_two] at hdet
    · rw [coefficientMatrix_fifthPower_mod_three p hp h3] at hdet
      simp [Matrix.det_fin_two] at hdet
    · rw [coefficientMatrix_fifthPower_mod_four p hp h4] at hdet
      simp at hdet
  · exact coefficientMatrix_fifthPower_det_ne_zero_mod_one p hp

/-- Uniformly for every odd prime other than five, the Cartier matrix
vanishes precisely in the residue class four. -/
theorem coefficientMatrix_fifthPower_zero_iff (hp : 3 ≤ p) (hp5 : p ≠ 5) :
    coefficientMatrix p (X ^ 5 - 1 : K[X]) = 0 ↔ p % 5 = 4 := by
  constructor
  · intro hz
    rcases prime_ne_five_mod_five p hp5 with h1 | h2 | h3 | h4
    · have h := coefficientMatrix_fifthPower_det_ne_zero_mod_one (K := K) p hp h1
      simp [hz] at h
    · exact (coefficientMatrix_fifthPower_ne_zero_mod_two p hp h2 hz).elim
    · exact (coefficientMatrix_fifthPower_ne_zero_mod_three p hp h3 hz).elim
    · exact h4
  · exact coefficientMatrix_fifthPower_mod_four p hp

/-- Uniformly for every odd prime other than five, the square of Cartier
vanishes precisely outside residue class one; the Frobenius twist is explicit. -/
theorem coefficientMatrix_fifthPower_twisted_square_zero_iff
    (hp : 3 ≤ p) (hp5 : p ≠ 5) :
    (coefficientMatrix p (X ^ 5 - 1 : K[X])).map (fun c => c ^ p) *
      coefficientMatrix p (X ^ 5 - 1 : K[X]) = 0 ↔ p % 5 ≠ 1 := by
  constructor
  · intro hz h1
    exact coefficientMatrix_fifthPower_twisted_square_ne_zero_mod_one p hp h1 hz
  · intro hn
    rcases prime_ne_five_mod_five p hp5 with h1 | h2 | h3 | h4
    · exact (hn h1).elim
    · exact coefficientMatrix_fifthPower_twisted_square_zero_mod_two p hp h2
    · exact coefficientMatrix_fifthPower_twisted_square_zero_mod_three p hp h3
    · rw [coefficientMatrix_fifthPower_mod_four p hp h4]
      simp

end SupersingularCurves.IKO
