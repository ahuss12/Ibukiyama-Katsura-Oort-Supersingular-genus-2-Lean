/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.IKO.Polynomials

/-!
# Uniform quadratic coefficient formulas

The two IKO families reduce to powers of `(X - 1) * (X - C t)`.
This file proves the binomial-sum identities used to identify their
coefficient matrices, over any field and before imposing a characteristic.
-/

set_option autoImplicit false
noncomputable section

namespace SupersingularCurves.IKO

open Polynomial Finset

variable {K : Type*} [Field K]

/-- The shared binomial polynomial underlying IKO's g and h. -/
def coefficientPolynomial (n d : ℕ) : K[X] :=
  ∑ j ∈ range (n - d + 1),
    C (n.choose (d + j) : K) * C (n.choose j : K) * X ^ j

private theorem sub_pow_expansion (t : K) (n : ℕ) :
    (X - C t) ^ n =
      ∑ j ∈ range (n + 1), C ((n.choose j : K) * (-t) ^ j) * X ^ (n - j) := by
  rw [sub_eq_add_neg, ← map_neg, add_comm, add_pow]
  apply sum_congr rfl
  intro j _
  simp only [map_mul, map_pow, map_natCast]
  ring

private theorem coeff_sub_one_pow (n i : ℕ) :
    ((X - 1 : K[X]) ^ n).coeff i = (-1 : K) ^ (n - i) * n.choose i := by
  simpa [sub_eq_add_neg] using coeff_X_add_C_pow (-1 : K) n i

private theorem quadratic_coeff_expansion (t : K) (n k : ℕ) :
    (quadratic t ^ n).coeff k =
      ∑ j ∈ range (n + 1), (n.choose j : K) * (-t) ^ j *
        (if n - j ≤ k then
          (-1 : K) ^ (n - (k - (n - j))) * n.choose (k - (n - j)) else 0) := by
  rw [quadratic, mul_pow, sub_pow_expansion, mul_sum, finsetSum_coeff]
  apply sum_congr rfl
  intro j _
  rw [show (X - 1 : K[X]) ^ n *
      (C ((n.choose j : K) * (-t) ^ j) * X ^ (n - j)) =
      C ((n.choose j : K) * (-t) ^ j) * ((X - 1) ^ n * X ^ (n - j)) by ring,
    coeff_C_mul, coeff_mul_X_pow']
  simp only [coeff_sub_one_pow]

/-- The upper of two coefficients symmetric around n. -/
theorem coeff_quadratic_power_high (t : K) (n d : ℕ) (hd : d ≤ n) :
    (quadratic t ^ n).coeff (n + d) =
      (-1 : K) ^ (n - d) * (coefficientPolynomial n d).eval t := by
  rw [quadratic_coeff_expansion]
  have heval : (coefficientPolynomial n d).eval t =
      ∑ j ∈ range (n - d + 1), (n.choose (d + j) : K) * n.choose j * t ^ j := by
    simp [coefficientPolynomial, eval_finsetSum]
  rw [heval, mul_sum]
  calc
    _ = ∑ j ∈ range (n - d + 1), (n.choose j : K) * (-t) ^ j *
        (if n - j ≤ n + d then
          (-1 : K) ^ (n - (n + d - (n - j))) * n.choose (n + d - (n - j))
          else 0) := by
      symm
      apply sum_subset (range_mono (by omega))
      intro j hj hjnot
      have hjn : j ≤ n := by simpa using hj
      have hjd : n - d < j := by simpa using hjnot
      have hk : n + d - (n - j) = d + j := by omega
      have hz : n.choose (d + j) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [hk, hz]
    _ = _ := by
      apply sum_congr rfl
      intro j hj
      have hjd : j ≤ n - d := by simpa using hj
      have hk : n + d - (n - j) = d + j := by omega
      have hle : n - j ≤ n + d := by omega
      have he : j + (n - (d + j)) = n - d := by omega
      simp only [ite_eq_left hle, hk, neg_eq_neg_one_mul t, mul_pow]
      calc
        _ = ((-1 : K) ^ j * (-1) ^ (n - (d + j))) *
            ((n.choose (d + j) : K) * n.choose j * t ^ j) := by ring
        _ = _ := by rw [← pow_add, he]

private theorem coeff_sub_C_pow (t : K) (n i : ℕ) :
    ((X - C t) ^ n).coeff i = (-t) ^ (n - i) * (n.choose i : K) := by
  simpa [sub_eq_add_neg] using coeff_X_add_C_pow (-t) n i

/-- The lower coefficient has the same polynomial factor and an extra t^d. -/
theorem coeff_quadratic_power_low (t : K) (n d : ℕ) (hd : d ≤ n) :
    (quadratic t ^ n).coeff (n - d) =
      t ^ d * ((-1 : K) ^ (n - d) * (coefficientPolynomial n d).eval t) := by
  rw [quadratic, mul_pow, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_sub_one_pow, coeff_sub_C_pow]
  have heval : (coefficientPolynomial n d).eval t =
      ∑ j ∈ range (n - d + 1), (n.choose (d + j) : K) * n.choose j * t ^ j := by
    simp [coefficientPolynomial, eval_finsetSum]
  rw [heval, mul_sum, mul_sum]
  apply sum_congr rfl
  intro j hj
  have hjd : j ≤ n - d := by simpa using hj
  have hjn : j ≤ n := by omega
  have he : n - (n - d - j) = d + j := by omega
  have hc : n.choose (n - d - j) = n.choose (d + j) :=
    Nat.choose_symm_of_eq_add (by omega)
  have hs : (-1 : K) ^ (n - j) * (-1) ^ (d + j) = (-1) ^ (n - d) := by
    rw [← pow_add, show n - j + (d + j) = (n - d) + 2 * d by omega,
      pow_add, pow_mul]
    simp
  rw [he, hc, neg_eq_neg_one_mul t, mul_pow, pow_add t]
  calc
    _ = ((-1 : K) ^ (n - j) * (-1) ^ (d + j)) *
        (t ^ d * ((n.choose (d + j) : K) * n.choose j * t ^ j)) := by ring
    _ = _ := by rw [hs]; ring

/-- Coefficients symmetric around n differ by precisely t^d. -/
theorem coeff_quadratic_power_symmetry (t : K) (n d : ℕ) (hd : d ≤ n) :
    (quadratic t ^ n).coeff (n - d) =
      t ^ d * (quadratic t ^ n).coeff (n + d) := by
  rw [coeff_quadratic_power_low t n d hd, coeff_quadratic_power_high t n d hd]

end SupersingularCurves.IKO
