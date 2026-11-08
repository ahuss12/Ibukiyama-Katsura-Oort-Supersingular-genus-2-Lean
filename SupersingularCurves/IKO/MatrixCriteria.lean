/-
Copyright (c) 2026 Ameen Hussain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ameen Hussain
-/
import SupersingularCurves.IKO.UniformMatrices

/-!
# Algebraic criteria for the IKO matrices

For admissible parameters these matrices are zero or have nonzero
determinant. Their twisted-square criterion therefore agrees with their
zero criterion. These are matrix theorems, not definitions or proofs of
geometric supersingularity or superspeciality.
-/

set_option autoImplicit false
noncomputable section

namespace SupersingularCurves.IKO

open Polynomial Matrix

variable {K : Type*} [Field K]

private theorem prime_mod_six (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    p % 6 = 1 ∨ p % 6 = 5 := by
  have h2 : p % 2 = 1 := hp.mod_two_eq_one_iff_ne_two.mpr (by omega)
  have h3 : ¬3 ∣ p := by
    intro h
    have := (Nat.dvd_prime hp).mp h
    omega
  omega

/-- The family-(a) matrix vanishes precisely at roots of g, for all primes p ≥ 5. -/
theorem coefficientMatrix_familyA_zero_iff (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (t : K) : coefficientMatrix p (familyA t) = 0 ↔ (gPolynomial p).eval t = 0 := by
  rcases prime_mod_six p hp hp5 with h | h
  · rw [coefficientMatrix_familyA_formula_one p (by omega) h]
    constructor
    · intro hz
      simpa using congrFun (congrFun hz 1) 1
    · intro hz
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hz]
  · rw [coefficientMatrix_familyA_formula_five p h]
    constructor
    · intro hz
      simpa using congrFun (congrFun hz 1) 0
    · intro hz
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hz]

/-- The family-(b) zero criterion covers every odd prime, including three. -/
theorem coefficientMatrix_familyB_zero_iff (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p)
    (t : K) : coefficientMatrix p (familyB t) = 0 ↔ (hPolynomial p).eval t = 0 := by
  have hp2 : p % 2 = 1 := hp.mod_two_eq_one_iff_ne_two.mpr (by omega)
  have hs : (-1 : K) ^ (p / 4) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have hc : p % 4 = 1 ∨ p % 4 = 3 := by omega
  rcases hc with h | h
  · rw [coefficientMatrix_familyB_formula_one p hp3 h]
    constructor
    · intro hz
      have he := congrFun (congrFun hz 1) 1
      simpa [hs] using he
    · intro hz
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hz]
  · rw [coefficientMatrix_familyB_formula_three p h]
    constructor
    · intro hz
      have he := congrFun (congrFun hz 1) 0
      simpa [hs] using he
    · intro hz
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hz]

/-- Away from t = 0, every nonzero family-(a) matrix is invertible. -/
theorem coefficientMatrix_familyA_det_ne_zero_iff (p : ℕ) (hp : p.Prime)
    (hp5 : 5 ≤ p) (t : K) (ht : t ≠ 0) :
    (coefficientMatrix p (familyA t)).det ≠ 0 ↔ (gPolynomial p).eval t ≠ 0 := by
  rcases prime_mod_six p hp hp5 with h | h
  · rw [coefficientMatrix_familyA_formula_one p (by omega) h]
    simp [det_fin_two, pow_ne_zero _ ht]
  · rw [coefficientMatrix_familyA_formula_five p h]
    simp [det_fin_two, pow_ne_zero _ ht]

/-- Away from t = 0, every nonzero family-(b) matrix is invertible. -/
theorem coefficientMatrix_familyB_det_ne_zero_iff (p : ℕ) (hp : p.Prime)
    (hp3 : 3 ≤ p) (t : K) (ht : t ≠ 0) :
    (coefficientMatrix p (familyB t)).det ≠ 0 ↔ (hPolynomial p).eval t ≠ 0 := by
  have hp2 : p % 2 = 1 := hp.mod_two_eq_one_iff_ne_two.mpr (by omega)
  have hs : (-1 : K) ^ (p / 4) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have hc : p % 4 = 1 ∨ p % 4 = 3 := by omega
  rcases hc with h | h
  · rw [coefficientMatrix_familyB_formula_one p hp3 h]
    simp [det_fin_two, pow_ne_zero _ ht, hs]
  · rw [coefficientMatrix_familyB_formula_three p h]
    simp [det_fin_two, pow_ne_zero _ ht, hs]

/-- A matrix that is zero or invertible cannot have a nonzero vanishing twisted square. -/
theorem twisted_square_zero_iff_of_det (σ : K ≃+* K) (M : Matrix (Fin 2) (Fin 2) K)
    (hdet : M ≠ 0 → M.det ≠ 0) : twistMatrix σ M * M = 0 ↔ M = 0 := by
  constructor
  · intro hz
    by_contra hn
    have hd := hdet hn
    have ht : (twistMatrix σ M).det = σ M.det := by
      simp [twistMatrix, det_fin_two]
    have hzdet : (twistMatrix σ M * M).det = 0 := by rw [hz]; simp
    rw [det_mul, ht] at hzdet
    exact mul_ne_zero (by simpa using hd) hd hzdet
  · rintro rfl
    simp

/-- Algebraic part of IKO 1.8: the twisted square vanishes exactly at roots of g. -/
theorem coefficientMatrix_familyA_twisted_square_zero_iff (σ : K ≃+* K)
    (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (t : K) (ht : t ≠ 0) :
    twistMatrix σ (coefficientMatrix p (familyA t)) * coefficientMatrix p (familyA t) = 0 ↔
      (gPolynomial p).eval t = 0 := by
  rw [twisted_square_zero_iff_of_det σ _ ?_, coefficientMatrix_familyA_zero_iff p hp hp5]
  intro hn
  apply (coefficientMatrix_familyA_det_ne_zero_iff p hp hp5 t ht).mpr
  exact fun hg => hn ((coefficientMatrix_familyA_zero_iff p hp hp5 t).mpr hg)

/-- Algebraic part of IKO 1.9: the twisted square vanishes exactly at roots of h. -/
theorem coefficientMatrix_familyB_twisted_square_zero_iff (σ : K ≃+* K)
    (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (t : K) (ht : t ≠ 0) :
    twistMatrix σ (coefficientMatrix p (familyB t)) * coefficientMatrix p (familyB t) = 0 ↔
      (hPolynomial p).eval t = 0 := by
  rw [twisted_square_zero_iff_of_det σ _ ?_, coefficientMatrix_familyB_zero_iff p hp hp3]
  intro hn
  apply (coefficientMatrix_familyB_det_ne_zero_iff p hp hp3 t ht).mpr
  exact fun hh => hn ((coefficientMatrix_familyB_zero_iff p hp hp3 t).mpr hh)

/-- The family-(a) coordinate action vanishes exactly at roots of g. -/
theorem familyA_semilinear_zero_iff (σ : K ≃+* K) (p : ℕ)
    (hp : p.Prime) (hp5 : 5 ≤ p) (t : K) :
    (∀ v, semilinearAction σ (coefficientMatrix p (familyA t)) v = 0) ↔
      (gPolynomial p).eval t = 0 := by
  rw [semilinearAction_zero_iff, coefficientMatrix_familyA_zero_iff p hp hp5]

/-- The family-(a) coordinate action has vanishing square exactly at roots of g. -/
theorem familyA_semilinear_square_zero_iff (σ : K ≃+* K) (p : ℕ)
    (hp : p.Prime) (hp5 : 5 ≤ p) (t : K) (ht : t ≠ 0) :
    (∀ v, semilinearAction σ (coefficientMatrix p (familyA t))
      (semilinearAction σ (coefficientMatrix p (familyA t)) v) = 0) ↔
      (gPolynomial p).eval t = 0 := by
  rw [semilinearAction_square_zero_iff,
    coefficientMatrix_familyA_twisted_square_zero_iff σ p hp hp5 t ht]

/-- The family-(b) coordinate action vanishes exactly at roots of h. -/
theorem familyB_semilinear_zero_iff (σ : K ≃+* K) (p : ℕ)
    (hp : p.Prime) (hp3 : 3 ≤ p) (t : K) :
    (∀ v, semilinearAction σ (coefficientMatrix p (familyB t)) v = 0) ↔
      (hPolynomial p).eval t = 0 := by
  rw [semilinearAction_zero_iff, coefficientMatrix_familyB_zero_iff p hp hp3]

/-- The family-(b) coordinate action has vanishing square exactly at roots of h. -/
theorem familyB_semilinear_square_zero_iff (σ : K ≃+* K) (p : ℕ)
    (hp : p.Prime) (hp3 : 3 ≤ p) (t : K) (ht : t ≠ 0) :
    (∀ v, semilinearAction σ (coefficientMatrix p (familyB t))
      (semilinearAction σ (coefficientMatrix p (familyB t)) v) = 0) ↔
      (hPolynomial p).eval t = 0 := by
  rw [semilinearAction_square_zero_iff,
    coefficientMatrix_familyB_twisted_square_zero_iff σ p hp hp3 t ht]

/-- The entrywise p-th-power version used in IKO, over a perfect field. -/
theorem coefficientMatrix_familyA_frobenius_square_zero_iff (p : ℕ)
    [Fact p.Prime] [CharP K p] [PerfectField K] (hp5 : 5 ≤ p) (t : K) (ht : t ≠ 0) :
    (coefficientMatrix p (familyA t)).map (fun a => a ^ p) *
      coefficientMatrix p (familyA t) = 0 ↔ (gPolynomial p).eval t = 0 := by
  rw [← frobenius_twistMatrix p]
  exact coefficientMatrix_familyA_twisted_square_zero_iff
    (frobeniusEquiv K p) p Fact.out hp5 t ht

/-- The entrywise p-th-power criterion for family (b), including p = 3. -/
theorem coefficientMatrix_familyB_frobenius_square_zero_iff (p : ℕ)
    [Fact p.Prime] [CharP K p] [PerfectField K] (hp3 : 3 ≤ p) (t : K) (ht : t ≠ 0) :
    (coefficientMatrix p (familyB t)).map (fun a => a ^ p) *
      coefficientMatrix p (familyB t) = 0 ↔ (hPolynomial p).eval t = 0 := by
  rw [← frobenius_twistMatrix p]
  exact coefficientMatrix_familyB_twisted_square_zero_iff
    (frobeniusEquiv K p) p Fact.out hp3 t ht

end SupersingularCurves.IKO
