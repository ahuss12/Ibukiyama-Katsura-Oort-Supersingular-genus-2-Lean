/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.IKO.Hypergeometric

/-!
# Binomial polynomial solutions of the hypergeometric equation

The IKO parameter polynomials share the coefficients
`choose m (s+j) * choose m j`. We prove the recurrence, differential equation,
endpoint values, degree, and separability uniformly. Specialization to g and h
is in `SimpleRoots.lean`.
-/

set_option autoImplicit false
noncomputable section
namespace SupersingularCurves.IKO
open Polynomial Finset
variable {K : Type*} [Field K]

def binomialPolynomial (m s : ℕ) : K[X] :=
  ∑ j ∈ range (m - s + 1), C ((m.choose (s + j) : K) * (m.choose j : K)) * X ^ j

theorem coeff_binomialPolynomial (m s j : ℕ) :
    (binomialPolynomial m s : K[X]).coeff j =
      (m.choose (s + j) : K) * (m.choose j : K) := by
  simp only [binomialPolynomial, finsetSum_coeff, coeff_C_mul_X_pow,
    Finset.sum_ite_eq, Finset.mem_range]
  split_ifs with h
  · rfl
  · rw [Nat.choose_eq_zero_of_lt (by omega : m < s + j)]
    simp

theorem natDegree_binomialPolynomial_le (m s : ℕ) :
    (binomialPolynomial m s : K[X]).natDegree ≤ m - s := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro j hj
  rw [coeff_binomialPolynomial, Nat.choose_eq_zero_of_lt (by omega : m < s + j)]
  simp

theorem eval_zero_binomialPolynomial (m s : ℕ) :
    (binomialPolynomial m s : K[X]).eval 0 = (m.choose s : K) := by
  rw [← coeff_zero_eq_eval_zero, coeff_binomialPolynomial]
  simp

theorem eval_one_binomialPolynomial (m s : ℕ) (hs : s ≤ m) :
    (binomialPolynomial m s : K[X]).eval 1 = ((2 * m).choose (m - s) : K) := by
  simp only [binomialPolynomial, eval_finsetSum, eval_mul, eval_C, eval_pow,
    eval_X, one_pow, mul_one]
  have hsum : (∑ j ∈ range (m - s + 1), m.choose (s + j) * m.choose j) =
      (2 * m).choose (m - s) := by
    rw [two_mul, Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j ≤ m - s := by simpa using hj
    rw [← Nat.choose_symm (by omega : s + j ≤ m)]
    have he : m - (s + j) = m - s - j := by omega
    rw [he, mul_comm]
  simpa only [Nat.cast_sum, Nat.cast_mul] using congrArg (Nat.cast (R := K)) hsum

/-- The coefficient recurrence for equation (1.31). It is valid integrally,
before specializing the characteristic. -/
theorem binomialPolynomial_coeff_recurrence (m s j : ℕ) :
    ((j : K) + 1) * (j + (s + 1)) * (binomialPolynomial m s : K[X]).coeff (j + 1) =
      (j + -(m : K)) * (j + ((s : K) - m)) * (binomialPolynomial m s : K[X]).coeff j := by
  rw [coeff_binomialPolynomial, coeff_binomialPolynomial]
  by_cases hsj : s + j ≤ m
  · have hj : j ≤ m := by omega
    have h1 : (m.choose (s + (j + 1)) : K) * ((s : K) + j + 1) =
        (m.choose (s + j) : K) * ((m : K) - (s + j)) := by
      have h := congrArg (Nat.cast (R := K)) (Nat.choose_succ_right_eq m (s + j))
      push_cast [Nat.cast_sub hsj] at h
      simpa [Nat.add_assoc] using h
    have h2 : (m.choose (j + 1) : K) * ((j : K) + 1) =
        (m.choose j : K) * ((m : K) - j) := by
      have h := congrArg (Nat.cast (R := K)) (Nat.choose_succ_right_eq m j)
      push_cast [Nat.cast_sub hj] at h
      exact h
    calc
      _ = ((m.choose (s + (j + 1)) : K) * ((s : K) + j + 1)) *
          ((m.choose (j + 1) : K) * ((j : K) + 1)) := by ring
      _ = _ := by rw [h1, h2]; ring
  · rw [Nat.choose_eq_zero_of_lt (by omega : m < s + (j + 1)),
      Nat.choose_eq_zero_of_lt (by omega : m < s + j)]
    simp

theorem hypergeometricOp_binomialPolynomial (m s : ℕ) :
    hypergeometricOp (-(m : K)) ((s : K) - m) ((s : K) + 1) 0
      (binomialPolynomial m s) = 0 := by
  ext j
  rw [coeff_hypergeometricOp_zero, binomialPolynomial_coeff_recurrence, sub_self, coeff_zero]

theorem cast_choose_ne_zero_of_lt (p : ℕ) [Fact p.Prime] [CharP K p]
    {m s : ℕ} (hm : m < p) (hs : s ≤ m) : (m.choose s : K) ≠ 0 := by
  intro h
  have hd : p ∣ m.choose s := (CharP.cast_eq_zero_iff K p _).mp h
  exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mp
    ((Fact.out : p.Prime).coprime_choose_of_lt hm hs)) hd

theorem natDegree_binomialPolynomial (p : ℕ) [Fact p.Prime] [CharP K p]
    (m s : ℕ) (hm : m < p) (hs : s ≤ m) :
    (binomialPolynomial m s : K[X]).natDegree = m - s := by
  apply natDegree_eq_of_le_of_coeff_ne_zero (natDegree_binomialPolynomial_le m s)
  rw [coeff_binomialPolynomial, Nat.add_sub_of_le hs, Nat.choose_self, Nat.cast_one, one_mul]
  exact cast_choose_ne_zero_of_lt p hm (Nat.sub_le _ _)

/-- The main IKO simple-root argument, for a uniform binomial family.
The bound 2m < p ensures that both endpoint values are nonzero. -/
theorem binomialPolynomial_separable (p : ℕ) [Fact p.Prime] [CharP K p]
    (m s : ℕ) (hm : 2 * m < p) (hs : s ≤ m) :
    (binomialPolynomial m s : K[X]).Separable := by
  apply separable_of_hypergeometric p (-(m : K)) ((s : K) - m) ((s : K) + 1)
  · exact (natDegree_binomialPolynomial_le m s).trans_lt (by omega)
  · exact hypergeometricOp_binomialPolynomial m s
  · rw [eval_zero_binomialPolynomial]
    exact cast_choose_ne_zero_of_lt p (by omega) hs
  · rw [eval_one_binomialPolynomial m s hs]
    exact cast_choose_ne_zero_of_lt p hm (by omega)

end SupersingularCurves.IKO
